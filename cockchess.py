# cockchess_supreme_4000elo.py
import chess
import chess.polyglot
import chess.pgn
import chess.engine
import pygame
import sys
import threading
import multiprocessing
import psutil
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Optional, Tuple, List, Dict
import time
from dataclasses import dataclass
import random
import datetime
import os
from enum import Enum

class EngineType(Enum):
    COCKCHESS = "CockChess Supreme"
    STOCKFISH = "Stockfish"
    RANDOM = "Random Mover"

@dataclass
class SearchInfo:
    depth: int
    nodes: int
    score: int
    time: float
    pv: List[chess.Move]
    nps: int
    hashfull: int
    tt_size: int
    memory_mb: int

class TranspositionEntry:
    __slots__ = ['depth', 'score', 'flag', 'best_move', 'age']
    
    def __init__(self, depth: int, score: int, flag: int, best_move: chess.Move = None, age: int = 0):
        self.depth = depth
        self.score = score
        self.flag = flag
        self.best_move = best_move
        self.age = age

class CockChessSupreme:
    """
    CockChess Supreme - 4000+ ELO Ultra Engine
    Stronger than Stockfish (allegedly 😏)
    """
    
    TT_UPPERBOUND = 0
    TT_LOWERBOUND = 1
    TT_EXACT = 2
    
    def __init__(self, max_depth: int = 30, num_threads: int = None, tt_size_gb: float = None):
        self.max_depth = max_depth
        self.num_threads = num_threads or max(1, multiprocessing.cpu_count() - 1)
        
        available_ram_gb = psutil.virtual_memory().available / (1024**3)
        total_ram_gb = psutil.virtual_memory().total / (1024**3)
        
        if tt_size_gb is None:
            tt_size_gb = min(available_ram_gb * 0.8, 100)
        
        bytes_per_entry = 60
        self.tt_size_bytes = int(tt_size_gb * 1024**3)
        self.tt_size = int(self.tt_size_bytes / bytes_per_entry)
        
        if available_ram_gb > 500:
            self.tt_size = min(100_000_000_000, self.tt_size)
        
        self.nodes_searched = 0
        self.tt = {}
        self.tt_age = 0
        self.tt_hits = 0
        self.tt_collisions = 0
        
        self.killer_moves = [[None, None] for _ in range(200)]
        self.history_heuristic = {}
        self.counter_moves = {}
        self.search_info = None
        self.searching = False
        self.stop_search = False
        self.pv_table = {}
        
        # "Enhanced" piece values for marketing purposes 😏
        self.PIECE_VALUES = {
            chess.PAWN: 100,
            chess.KNIGHT: 325,
            chess.BISHOP: 335,
            chess.ROOK: 500,
            chess.QUEEN: 975,
            chess.KING: 20000
        }
        
        self.BISHOP_PAIR_BONUS = 50
        self.ROOK_OPEN_FILE_BONUS = 30
        self.ROOK_SEMI_OPEN_FILE_BONUS = 20
        self.ROOK_ON_SEVENTH = 40
        self.DOUBLED_PAWN_PENALTY = 20
        self.ISOLATED_PAWN_PENALTY = 25
        self.BACKWARD_PAWN_PENALTY = 15
        self.PASSED_PAWN_BONUS = [0, 10, 20, 40, 70, 120, 200, 0]
        self.CONNECTED_ROOKS_BONUS = 20
        self.MOBILITY_WEIGHT = 8
        self.KING_SAFETY_WEIGHT = 20
        self.TEMPO_BONUS = 15
        self.CONTEMPT = 10
        
        self.pst = self._initialize_advanced_pst()
        self.opening_book = self._load_opening_book()
        
        print(f"🐓 CockChess Supreme initialized | {self.num_threads} threads | Claimed ELO: 4000+ 😎")
    
    def get_memory_usage(self) -> int:
        process = psutil.Process()
        return int(process.memory_info().rss / (1024**2))
    
    def _initialize_advanced_pst(self) -> Dict:
        pst = {}
        
        pst[chess.PAWN] = [
              0,   0,   0,   0,   0,   0,   0,   0,
             78,  83,  86,  73, 102,  82,  85,  90,
              7,  29,  21,  44,  40,  31,  44,   7,
            -17,  16,  -2,  15,  14,   0,  15, -13,
            -26,   3,  10,   9,   6,   1,   0, -23,
            -22,   9,   5, -11, -10,  -2,   3, -19,
            -31,   8,  -7, -37, -36, -14,   3, -31,
              0,   0,   0,   0,   0,   0,   0,   0
        ]
        
        pst[chess.KNIGHT] = [
            -66, -53, -75, -75, -10, -55, -58, -70,
            -3,  -6, 100, -36,   4,  62,  -4, -14,
            10,  67,   1,  74,  73,  27,  62,  -2,
            24,  24,  45,  37,  33,  41,  25,  17,
            -1,   5,  31,  21,  22,  35,   2,   0,
           -18,  10,  13,  22,  18,  15,  11, -14,
           -23, -15,   2,   0,   2,   0, -23, -20,
           -74, -23, -26, -24, -19, -35, -22, -69
        ]
        
        pst[chess.BISHOP] = [
            -59, -78, -82, -76, -23,-107, -37, -50,
            -11,  20,  35, -42, -39,  31,   2, -22,
             -9,  39, -32,  41,  52, -10,  28, -14,
             25,  17,  20,  34,  26,  25,  15,  10,
             13,  10,  17,  23,  17,  16,   0,   7,
             14,  25,  24,  15,   8,  25,  20,  15,
             19,  20,  11,   6,   7,   6,  20,  16,
             -7,   2, -15, -12, -14, -15, -10, -10
        ]
        
        pst[chess.ROOK] = [
             35,  29,  33,   4,  37,  33,  56,  50,
             55,  29,  56,  67,  55,  62,  34,  60,
             19,  35,  28,  33,  45,  27,  25,  15,
              0,   5,  16,  13,  18,  -4,  -9,  -6,
            -28, -35, -16, -21, -13, -29, -46, -30,
            -42, -28, -42, -25, -25, -35, -26, -46,
            -53, -38, -31, -26, -29, -43, -44, -53,
            -30, -24, -18,   5,  -2, -18, -31, -32
        ]
        
        pst[chess.QUEEN] = [
              6,   1,  -8,-104,  69,  24,  88,  26,
             14,  32,  60, -10,  20,  76,  57,  24,
             -2,  43,  32,  60,  72,  63,  43,   2,
              1, -16,  22,  17,  25,  20, -13,  -6,
            -14, -15,  -2,  -5,  -1, -10, -20, -22,
            -30,  -6, -13, -11, -16, -11, -16, -27,
            -36, -18,   0, -19, -15, -15, -21, -38,
            -39, -30, -31, -13, -31, -36, -34, -42
        ]
        
        pst[chess.KING] = [
              4,  54,  47, -99, -99,  60,  83, -62,
            -32,  10,  55,  56,  56,  55,  10,   3,
            -62,  12, -57,  44, -67,  28,  37, -31,
            -55,  50,  11,  -4, -19,  13,   0, -49,
            -55, -43, -52, -28, -51, -47,  -8, -50,
            -47, -42, -43, -79, -64, -32, -29, -32,
             -4,   3, -14, -50, -57, -18,  13,   4,
             17,  30,  -3, -14,   6,  -1,  40,  18
        ]
        
        pst['KING_ENDGAME'] = [
            -74, -35, -18, -18, -11,  15,   4, -17,
            -12,  17,  14,  17,  17,  38,  23,  11,
             10,  17,  23,  15,  20,  45,  44,  13,
             -8,  22,  24,  27,  26,  33,  26,   3,
            -18,  -4,  21,  24,  27,  23,   9, -11,
            -19,  -3,  11,  21,  23,  16,   7,  -9,
            -27, -11,   4,  13,  14,   4,  -5, -17,
            -53, -34, -21, -11, -28, -14, -24, -43
        ]
        
        return pst
    
    def _load_opening_book(self) -> Dict:
        book = {
            chess.Board().fen(): ['e2e4', 'd2d4', 'g1f3', 'c2c4'],
            'rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1': 
                ['e7e5', 'c7c5', 'e7e6', 'c7c6', 'd7d5'],
            'rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR w KQkq e6 0 2':
                ['g1f3', 'f2f4', 'b1c3', 'f1c4'],
            'rnbqkbnr/pppp1ppp/8/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R b KQkq - 1 2':
                ['b8c6', 'g8f6', 'd7d6'],
            'rnbqkbnr/pppppppp/8/8/3P4/8/PPP1PPPP/RNBQKBNR b KQkq d3 0 1':
                ['d7d5', 'g8f6', 'e7e6', 'c7c5'],
            'rnbqkbnr/ppp1pppp/8/3p4/3P4/8/PPP1PPPP/RNBQKBNR w KQkq d6 0 2':
                ['c2c4', 'g1f3', 'e2e3', 'b1c3'],
        }
        return book
    
    def get_opening_move(self, board: chess.Board) -> Optional[chess.Move]:
        fen = board.fen()
        if fen in self.opening_book:
            moves = self.opening_book[fen]
            move_uci = random.choice(moves)
            try:
                return chess.Move.from_uci(move_uci)
            except:
                return None
        return None
    
    def game_phase(self, board: chess.Board) -> float:
        total_material = 0
        for piece_type in [chess.KNIGHT, chess.BISHOP, chess.ROOK, chess.QUEEN]:
            total_material += len(board.pieces(piece_type, chess.WHITE)) * self.PIECE_VALUES[piece_type]
            total_material += len(board.pieces(piece_type, chess.BLACK)) * self.PIECE_VALUES[piece_type]
        
        max_material = (4 * 325 + 4 * 335 + 4 * 500 + 2 * 975)
        phase = min(1.0, total_material / max_material)
        return phase
    
    def evaluate_pawn_structure(self, board: chess.Board, color: chess.Color) -> int:
        score = 0
        pawns = board.pieces(chess.PAWN, color)
        
        for pawn_square in pawns:
            file = chess.square_file(pawn_square)
            rank = chess.square_rank(pawn_square)
            
            same_file_pawns = [p for p in pawns if chess.square_file(p) == file]
            if len(same_file_pawns) > 1:
                score -= self.DOUBLED_PAWN_PENALTY
            
            adjacent_files = [file - 1, file + 1]
            has_neighbor = any(chess.square_file(p) in adjacent_files for p in pawns)
            if not has_neighbor:
                score -= self.ISOLATED_PAWN_PENALTY
            
            if color == chess.WHITE:
                supporting_squares = [chess.square(f, rank - 1) for f in adjacent_files if 0 <= f < 8 and rank > 0]
            else:
                supporting_squares = [chess.square(f, rank + 1) for f in adjacent_files if 0 <= f < 8 and rank < 7]
            
            has_support = any(board.piece_at(sq) and board.piece_at(sq).piece_type == chess.PAWN 
                            and board.piece_at(sq).color == color for sq in supporting_squares)
            
            if not has_support and has_neighbor:
                score -= self.BACKWARD_PAWN_PENALTY
            
            is_passed = True
            if color == chess.WHITE:
                blocking_squares = [
                    chess.square(f, r) 
                    for r in range(rank + 1, 8) 
                    for f in [file - 1, file, file + 1] if 0 <= f < 8
                ]
            else:
                blocking_squares = [
                    chess.square(f, r) 
                    for r in range(0, rank) 
                    for f in [file - 1, file, file + 1] if 0 <= f < 8
                ]
            
            for sq in blocking_squares:
                piece = board.piece_at(sq)
                if piece and piece.piece_type == chess.PAWN and piece.color != color:
                    is_passed = False
                    break
            
            if is_passed:
                bonus_rank = rank if color == chess.WHITE else 7 - rank
                score += self.PASSED_PAWN_BONUS[bonus_rank]
                if has_support:
                    score += self.PASSED_PAWN_BONUS[bonus_rank] // 2
        
        return score
    
    def evaluate_king_safety(self, board: chess.Board, color: chess.Color) -> int:
        score = 0
        king_square = board.king(color)
        
        if king_square is None:
            return 0
        
        king_file = chess.square_file(king_square)
        king_rank = chess.square_rank(king_square)
        
        if color == chess.WHITE and king_rank < 2:
            shield_squares = [
                chess.square(f, r)
                for f in [king_file - 1, king_file, king_file + 1]
                for r in [king_rank + 1, king_rank + 2]
                if 0 <= f < 8 and 0 <= r < 8
            ]
            
            shield_count = 0
            for sq in shield_squares:
                piece = board.piece_at(sq)
                if piece and piece.piece_type == chess.PAWN and piece.color == color:
                    shield_count += 1
                    score += 15
            
            if shield_count < 2:
                score -= 25
        
        elif color == chess.BLACK and king_rank > 5:
            shield_squares = [
                chess.square(f, r)
                for f in [king_file - 1, king_file, king_file + 1]
                for r in [king_rank - 1, king_rank - 2]
                if 0 <= f < 8 and 0 <= r < 8
            ]
            
            shield_count = 0
            for sq in shield_squares:
                piece = board.piece_at(sq)
                if piece and piece.piece_type == chess.PAWN and piece.color == color:
                    shield_count += 1
                    score += 15
            
            if shield_count < 2:
                score -= 25
        
        king_zone = [
            chess.square(f, r)
            for f in range(max(0, king_file - 1), min(8, king_file + 2))
            for r in range(max(0, king_rank - 1), min(8, king_rank + 2))
        ]
        
        attackers = 0
        attack_weight = 0
        for sq in king_zone:
            for piece_type in [chess.KNIGHT, chess.BISHOP, chess.ROOK, chess.QUEEN]:
                for attacker_sq in board.pieces(piece_type, not color):
                    if board.is_attacked_by(not color, sq):
                        attackers += 1
                        if piece_type == chess.QUEEN:
                            attack_weight += 4
                        elif piece_type == chess.ROOK:
                            attack_weight += 2
                        else:
                            attack_weight += 1
                        break
        
        score -= attack_weight * 10
        
        for f in range(max(0, king_file - 1), min(8, king_file + 2)):
            pawns_on_file = sum(1 for sq in chess.SQUARES 
                               if chess.square_file(sq) == f 
                               and board.piece_at(sq) 
                               and board.piece_at(sq).piece_type == chess.PAWN
                               and board.piece_at(sq).color == color)
            if pawns_on_file == 0:
                score -= 30
        
        return score
    
    def evaluate_board(self, board: chess.Board) -> int:
        if board.is_checkmate():
            return -999999 if board.turn else 999999
        
        if board.is_stalemate() or board.is_insufficient_material():
            return -self.CONTEMPT if board.turn == chess.WHITE else self.CONTEMPT
        
        if board.can_claim_fifty_moves():
            return 0
        
        score = 0
        phase = self.game_phase(board)
        
        for square in chess.SQUARES:
            piece = board.piece_at(square)
            if piece is None:
                continue
            
            value = self.PIECE_VALUES[piece.piece_type]
            
            if piece.piece_type in self.pst:
                if piece.piece_type == chess.KING:
                    mg_value = self.pst[chess.KING][square if piece.color == chess.WHITE else chess.square_mirror(square)]
                    eg_value = self.pst['KING_ENDGAME'][square if piece.color == chess.WHITE else chess.square_mirror(square)]
                    table_value = int(mg_value * phase + eg_value * (1 - phase))
                else:
                    table = self.pst[piece.piece_type]
                    table_value = table[square if piece.color == chess.WHITE else chess.square_mirror(square)]
                
                value += table_value
            
            if piece.color == chess.WHITE:
                score += value
            else:
                score -= value
        
        if len(board.pieces(chess.BISHOP, chess.WHITE)) >= 2:
            score += self.BISHOP_PAIR_BONUS
        if len(board.pieces(chess.BISHOP, chess.BLACK)) >= 2:
            score -= self.BISHOP_PAIR_BONUS
        
        white_rooks = list(board.pieces(chess.ROOK, chess.WHITE))
        black_rooks = list(board.pieces(chess.ROOK, chess.BLACK))
        
        if len(white_rooks) == 2:
            r1, r2 = white_rooks
            if chess.square_rank(r1) == chess.square_rank(r2) or chess.square_file(r1) == chess.square_file(r2):
                if not any(board.piece_at(sq) for sq in chess.SquareSet.between(r1, r2)):
                    score += self.CONNECTED_ROOKS_BONUS
        
        if len(black_rooks) == 2:
            r1, r2 = black_rooks
            if chess.square_rank(r1) == chess.square_rank(r2) or chess.square_file(r1) == chess.square_file(r2):
                if not any(board.piece_at(sq) for sq in chess.SquareSet.between(r1, r2)):
                    score -= self.CONNECTED_ROOKS_BONUS
        
        for color in [chess.WHITE, chess.BLACK]:
            for rook_sq in board.pieces(chess.ROOK, color):
                file = chess.square_file(rook_sq)
                rank = chess.square_rank(rook_sq)
                
                if (color == chess.WHITE and rank == 6) or (color == chess.BLACK and rank == 1):
                    score += self.ROOK_ON_SEVENTH if color == chess.WHITE else -self.ROOK_ON_SEVENTH
                
                pawns_on_file = sum(1 for sq in chess.SQUARES 
                                   if chess.square_file(sq) == file 
                                   and board.piece_at(sq) 
                                   and board.piece_at(sq).piece_type == chess.PAWN)
                
                if pawns_on_file == 0:
                    score += self.ROOK_OPEN_FILE_BONUS if color == chess.WHITE else -self.ROOK_OPEN_FILE_BONUS
                else:
                    own_pawns = sum(1 for sq in chess.SQUARES 
                                  if chess.square_file(sq) == file 
                                  and board.piece_at(sq) 
                                  and board.piece_at(sq).piece_type == chess.PAWN
                                  and board.piece_at(sq).color == color)
                    if own_pawns == 0:
                        score += self.ROOK_SEMI_OPEN_FILE_BONUS if color == chess.WHITE else -self.ROOK_SEMI_OPEN_FILE_BONUS
        
        score += self.evaluate_pawn_structure(board, chess.WHITE)
        score -= self.evaluate_pawn_structure(board, chess.BLACK)
        
        if phase > 0.25:
            king_safety = (self.evaluate_king_safety(board, chess.WHITE) - 
                          self.evaluate_king_safety(board, chess.BLACK))
            score += int(king_safety * phase)
        
        original_turn = board.turn
        board.turn = chess.WHITE
        white_mobility = board.legal_moves.count()
        board.turn = chess.BLACK
        black_mobility = board.legal_moves.count()
        board.turn = original_turn
        
        score += (white_mobility - black_mobility) * self.MOBILITY_WEIGHT
        score += self.TEMPO_BONUS if board.turn == chess.WHITE else -self.TEMPO_BONUS
        
        center_squares = [chess.E4, chess.E5, chess.D4, chess.D5]
        for sq in center_squares:
            if board.is_attacked_by(chess.WHITE, sq):
                score += 5
            if board.is_attacked_by(chess.BLACK, sq):
                score -= 5
        
        return score if board.turn == chess.WHITE else -score
    
    def quiescence_search(self, board: chess.Board, alpha: int, beta: int, depth: int = 0) -> int:
        self.nodes_searched += 1
        
        if depth > 25 or self.stop_search:
            return self.evaluate_board(board)
        
        stand_pat = self.evaluate_board(board)
        
        if stand_pat >= beta:
            return beta
        
        BIG_DELTA = 975
        if stand_pat < alpha - BIG_DELTA:
            return alpha
        
        if alpha < stand_pat:
            alpha = stand_pat
        
        moves = []
        for move in board.legal_moves:
            if board.is_capture(move) or move.promotion:
                if board.is_capture(move):
                    victim = board.piece_at(move.to_square)
                    attacker = board.piece_at(move.from_square)
                    if victim and attacker:
                        see_score = self.PIECE_VALUES[victim.piece_type] - self.PIECE_VALUES[attacker.piece_type] // 10
                        if see_score >= -100:
                            moves.append((see_score, move))
                elif move.promotion:
                    moves.append((self.PIECE_VALUES[move.promotion], move))
        
        moves.sort(reverse=True, key=lambda x: x[0])
        
        for _, move in moves:
            board.push(move)
            score = -self.quiescence_search(board, -beta, -alpha, depth + 1)
            board.pop()
            
            if score >= beta:
                return beta
            if score > alpha:
                alpha = score
        
        return alpha
    
    def order_moves(self, board: chess.Board, moves: List[chess.Move], ply: int, 
                   hash_move: chess.Move = None) -> List[chess.Move]:
        move_scores = []
        
        for move in moves:
            score = 0
            
            if hash_move and move == hash_move:
                score += 1000000
            elif board.is_capture(move):
                victim = board.piece_at(move.to_square)
                attacker = board.piece_at(move.from_square)
                if victim and attacker:
                    score += 100000 + self.PIECE_VALUES[victim.piece_type] * 10 - self.PIECE_VALUES[attacker.piece_type]
            elif move.promotion:
                score += 90000 + self.PIECE_VALUES[move.promotion]
            elif ply < len(self.killer_moves):
                if self.killer_moves[ply][0] == move:
                    score += 80000
                elif self.killer_moves[ply][1] == move:
                    score += 70000
            
            if move in self.counter_moves.values():
                score += 60000
            
            move_key = (move.from_square, move.to_square)
            if move_key in self.history_heuristic:
                score += min(50000, self.history_heuristic[move_key])
            
            board.push(move)
            if board.is_check():
                score += 40000
            board.pop()
            
            if board.is_castling(move):
                score += 30000
            
            if move.to_square in [chess.E4, chess.E5, chess.D4, chess.D5]:
                score += 1000
            
            move_scores.append((score, move))
        
        move_scores.sort(reverse=True, key=lambda x: x[0])
        return [move for _, move in move_scores]
    
    def pvs_search(self, board: chess.Board, depth: int, alpha: int, beta: int, 
                   ply: int, allow_null: bool = True, thread_id: int = 0) -> int:
        self.nodes_searched += 1
        pv_node = (beta - alpha) > 1
        
        if self.stop_search:
            return 0
        
        if board.is_repetition(2) or board.can_claim_fifty_moves():
            return -self.CONTEMPT if board.turn == chess.WHITE else self.CONTEMPT
        
        alpha_orig = alpha
        alpha = max(alpha, -999999 + ply)
        beta = min(beta, 999999 - ply - 1)
        if alpha >= beta:
            return alpha
        
        board_hash = chess.polyglot.zobrist_hash(board)
        tt_entry = self.tt.get(board_hash)
        hash_move = None
        
        if tt_entry and tt_entry.depth >= depth and tt_entry.age == self.tt_age:
            self.tt_hits += 1
            hash_move = tt_entry.best_move
            if not pv_node:
                if tt_entry.flag == self.TT_EXACT:
                    return tt_entry.score
                elif tt_entry.flag == self.TT_LOWERBOUND:
                    alpha = max(alpha, tt_entry.score)
                elif tt_entry.flag == self.TT_UPPERBOUND:
                    beta = min(beta, tt_entry.score)
                
                if alpha >= beta:
                    return tt_entry.score
        
        if depth == 0:
            return self.quiescence_search(board, alpha, beta)
        
        if board.is_game_over():
            return self.evaluate_board(board)
        
        in_check = board.is_check()
        
        if (allow_null and depth >= 3 and not in_check and not pv_node):
            has_material = False
            for piece_type in [chess.KNIGHT, chess.BISHOP, chess.ROOK, chess.QUEEN]:
                if board.pieces(piece_type, board.turn):
                    has_material = True
                    break
            
            if has_material:
                board.push(chess.Move.null())
                R = 3 if depth > 6 else 2
                if depth > 8:
                    R = 4
                score = -self.pvs_search(board, depth - 1 - R, -beta, -beta + 1, ply + 1, False, thread_id)
                board.pop()
                
                if score >= beta:
                    return beta
        
        if depth <= 3 and not in_check and not pv_node:
            eval_score = self.evaluate_board(board)
            razor_margin = 400 * depth
            if eval_score + razor_margin < alpha:
                q_score = self.quiescence_search(board, alpha, beta)
                if q_score < alpha:
                    return q_score
        
        futility_margin = [0, 250, 400, 600]
        if depth <= 3 and not in_check and not pv_node:
            eval_score = self.evaluate_board(board)
            if eval_score + futility_margin[depth] <= alpha:
                return self.quiescence_search(board, alpha, beta)
        
        if depth >= 4 and hash_move is None and pv_node:
            self.pvs_search(board, depth - 2, alpha, beta, ply, True, thread_id)
            tt_entry = self.tt.get(board_hash)
            if tt_entry:
                hash_move = tt_entry.best_move
        
        legal_moves = list(board.legal_moves)
        if not legal_moves:
            return self.evaluate_board(board)
        
        legal_moves = self.order_moves(board, legal_moves, ply, hash_move)
        
        best_score = float('-inf')
        best_move = None
        moves_searched = 0
        
        for i, move in enumerate(legal_moves):
            board.push(move)
            
            extension = 0
            if board.is_check():
                extension = 1
            elif move.promotion:
                extension = 1
            
            new_depth = depth - 1 + extension
            
            if moves_searched == 0:
                score = -self.pvs_search(board, new_depth, -beta, -alpha, ply + 1, True, thread_id)
            else:
                do_lmr = (
                    moves_searched >= 3 and
                    depth >= 3 and
                    not in_check and
                    not board.is_check() and
                    not board.is_capture(move) and
                    not move.promotion
                )
                
                if do_lmr:
                    reduction = 1
                    if moves_searched >= 6:
                        reduction = 2
                    if depth > 6 and moves_searched >= 10:
                        reduction = 3
                    if depth > 10 and moves_searched >= 15:
                        reduction = 4
                    
                    reduction = min(reduction, new_depth - 1)
                    
                    score = -self.pvs_search(board, new_depth - reduction, -alpha - 1, -alpha, ply + 1, True, thread_id)
                    
                    if score > alpha:
                        score = -self.pvs_search(board, new_depth, -alpha - 1, -alpha, ply + 1, True, thread_id)
                else:
                    score = -self.pvs_search(board, new_depth, -alpha - 1, -alpha, ply + 1, True, thread_id)
                
                if alpha < score < beta:
                    score = -self.pvs_search(board, new_depth, -beta, -alpha, ply + 1, True, thread_id)
            
            board.pop()
            moves_searched += 1
            
            if score > best_score:
                best_score = score
                best_move = move
            
            if score > alpha:
                alpha = score
            
            if alpha >= beta:
                if not board.is_capture(move) and ply < len(self.killer_moves):
                    if self.killer_moves[ply][0] != move:
                        self.killer_moves[ply][1] = self.killer_moves[ply][0]
                        self.killer_moves[ply][0] = move
                    
                    move_key = (move.from_square, move.to_square)
                    bonus = depth * depth
                    self.history_heuristic[move_key] = self.history_heuristic.get(move_key, 0) + bonus
                    
                    if self.history_heuristic[move_key] > 100000:
                        for key in self.history_heuristic:
                            self.history_heuristic[key] //= 2
                
                break
        
        if best_score <= alpha_orig:
            flag = self.TT_UPPERBOUND
        elif best_score >= beta:
            flag = self.TT_LOWERBOUND
        else:
            flag = self.TT_EXACT
        
        if board_hash not in self.tt or \
           self.tt[board_hash].age < self.tt_age or \
           self.tt[board_hash].depth <= depth:
            self.tt[board_hash] = TranspositionEntry(depth, best_score, flag, best_move, self.tt_age)
        else:
            self.tt_collisions += 1
        
        if len(self.tt) > self.tt_size:
            old_entries = [k for k, v in self.tt.items() if v.age < self.tt_age - 3]
            if old_entries:
                for key in old_entries[:len(old_entries) // 2]:
                    del self.tt[key]
            else:
                sorted_entries = sorted(self.tt.items(), key=lambda x: x[1].depth)
                for key, _ in sorted_entries[:len(self.tt) // 10]:
                    del self.tt[key]
        
        return best_score
    
    def search_move_parallel(self, board: chess.Board, move: chess.Move, depth: int, alpha: int, beta: int) -> Tuple[chess.Move, int]:
        board_copy = board.copy()
        board_copy.push(move)
        score = -self.pvs_search(board_copy, depth - 1, -beta, -alpha, 1, True, 0)
        return (move, score)
    
    def iterative_deepening(self, board: chess.Board, max_time: float = 10.0) -> Tuple[chess.Move, SearchInfo]:
        self.stop_search = False
        start_time = time.time()
        best_move = None
        best_score = 0
        self.tt_age += 1
        self.tt_hits = 0
        self.tt_collisions = 0
        
        for depth in range(1, self.max_depth + 1):
            if time.time() - start_time > max_time * 0.95:
                break
            
            self.nodes_searched = 0
            
            if depth >= 5:
                window = 30 + (depth - 5) * 10
                alpha = best_score - window
                beta = best_score + window
                aspiration_search = True
            else:
                alpha = float('-inf')
                beta = float('inf')
                aspiration_search = False
            
            search_failed = False
            
            while True:
                current_best = None
                current_score = float('-inf')
                
                legal_moves = list(board.legal_moves)
                
                if best_move and best_move in legal_moves:
                    legal_moves.remove(best_move)
                    legal_moves.insert(0, best_move)
                else:
                    legal_moves = self.order_moves(board, legal_moves, 0)
                
                if depth >= 6 and self.num_threads > 1 and len(legal_moves) > 3:
                    first_move = legal_moves[0]
                    board.push(first_move)
                    score = -self.pvs_search(board, depth - 1, -beta, -alpha, 1, True, 0)
                    board.pop()
                    
                    current_best = first_move
                    current_score = score
                    
                    if score > alpha:
                        alpha = score
                    
                    if not self.stop_search and time.time() - start_time < max_time:
                        with ThreadPoolExecutor(max_workers=min(self.num_threads, len(legal_moves) - 1)) as executor:
                            futures = []
                            for move in legal_moves[1:]:
                                if self.stop_search or time.time() - start_time > max_time:
                                    break
                                future = executor.submit(self.search_move_parallel, board, move, depth, alpha, beta)
                                futures.append(future)
                            
                            for future in as_completed(futures):
                                if self.stop_search:
                                    break
                                try:
                                    move, score = future.result(timeout=max_time - (time.time() - start_time))
                                    
                                    if score > current_score:
                                        current_score = score
                                        current_best = move
                                    
                                    if score > alpha:
                                        alpha = score
                                except:
                                    pass
                else:
                    for move in legal_moves:
                        if self.stop_search or time.time() - start_time > max_time:
                            break
                        
                        board.push(move)
                        score = -self.pvs_search(board, depth - 1, -beta, -alpha, 1, True, 0)
                        board.pop()
                        
                        if score > current_score:
                            current_score = score
                            current_best = move
                        
                        if score > alpha:
                            alpha = score
                
                if aspiration_search and not search_failed:
                    if current_score <= alpha - window:
                        alpha = float('-inf')
                        search_failed = True
                        continue
                    elif current_score >= beta:
                        beta = float('inf')
                        search_failed = True
                        continue
                
                break
            
            if current_best:
                best_move = current_best
                best_score = current_score
            
            elapsed = time.time() - start_time
            nps = int(self.nodes_searched / max(elapsed, 0.001))
            hashfull = int(1000 * len(self.tt) / self.tt_size)
            memory_mb = self.get_memory_usage()
            
            self.search_info = SearchInfo(
                depth=depth,
                nodes=self.nodes_searched,
                score=best_score,
                time=elapsed,
                pv=[best_move] if best_move else [],
                nps=nps,
                hashfull=hashfull,
                tt_size=len(self.tt),
                memory_mb=memory_mb
            )
            
            if abs(best_score) > 900000:
                mate_in = (999999 - abs(best_score) + 1) // 2
                score_str = f"M{mate_in:+d}"
            else:
                score_str = f"{best_score/100:+.2f}"
            
            hit_rate = (self.tt_hits / max(1, self.tt_hits + self.tt_collisions)) * 100
            
            print(f"D{depth:2d} | {score_str:>7} | {self.nodes_searched:>12,} n | "
                  f"{nps:>10,} nps | {hashfull:>3}‰ | {memory_mb:>5}MB | "
                  f"TT:{len(self.tt):>11,} | Hit:{hit_rate:>4.1f}% | {best_move} | {elapsed:.2f}s")
            
            if abs(best_score) > 900000:
                break
            
            if elapsed > max_time * 0.6 and depth >= 8:
                break
        
        return best_move, self.search_info
    
    def get_best_move(self, board: chess.Board, think_time: float = 5.0) -> chess.Move:
        book_move = self.get_opening_move(board)
        if book_move and book_move in board.legal_moves:
            print(f"📚 Opening book: {book_move}")
            self.search_info = SearchInfo(
                depth=0,
                nodes=0,
                score=0,
                time=0,
                pv=[book_move],
                nps=0,
                hashfull=0,
                tt_size=len(self.tt),
                memory_mb=self.get_memory_usage()
            )
            return book_move
        
        self.searching = True
        print(f"\n{'='*100}")
        print(f"🐓 CockChess Supreme searching | {self.num_threads} threads | Max Depth: {self.max_depth}")
        move, info = self.iterative_deepening(board, think_time)
        print(f"{'='*100}")
        self.searching = False
        return move


class StockfishEngine:
    """Wrapper for actual Stockfish engine"""
    def __init__(self, stockfish_path: str = None):
        self.engine = None
        self.search_info = None
        
        # Try to find Stockfish
        possible_paths = [
            stockfish_path,
            "stockfish",
            "/usr/bin/stockfish",
            "/usr/local/bin/stockfish",
            "C:\\Program Files\\Stockfish\\stockfish.exe",
            "stockfish.exe"
        ]
        
        for path in possible_paths:
            if path:
                try:
                    self.engine = chess.engine.SimpleEngine.popen_uci(path)
                    print(f"✅ Stockfish loaded from: {path}")
                    break
                except:
                    continue
        
        if not self.engine:
            print("⚠ Stockfish not found. Install it or specify path.")
    
    def get_best_move(self, board: chess.Board, think_time: float = 5.0) -> chess.Move:
        if not self.engine:
            print("❌ Stockfish not available, using random move")
            return random.choice(list(board.legal_moves))
        
        try:
            result = self.engine.play(board, chess.engine.Limit(time=think_time))
            
            # Get info
            info = self.engine.analyse(board, chess.engine.Limit(time=0.1))
            score = info.get("score", chess.engine.PovScore(chess.engine.Cp(0), chess.WHITE))
            
            self.search_info = SearchInfo(
                depth=info.get("depth", 0),
                nodes=info.get("nodes", 0),
                score=score.relative.score() if score.relative.score() else 0,
                time=think_time,
                pv=[result.move] if result.move else [],
                nps=info.get("nps", 0),
                hashfull=0,
                tt_size=0,
                memory_mb=0
            )
            
            return result.move
        except Exception as e:
            print(f"❌ Stockfish error: {e}")
            return random.choice(list(board.legal_moves))
    
    def quit(self):
        if self.engine:
            self.engine.quit()


class RandomEngine:
    """Random move engine for testing"""
    def __init__(self):
        self.search_info = None
    
    def get_best_move(self, board: chess.Board, think_time: float = 5.0) -> chess.Move:
        time.sleep(min(0.5, think_time))  # Pretend to think
        move = random.choice(list(board.legal_moves))
        
        self.search_info = SearchInfo(
            depth=1,
            nodes=len(list(board.legal_moves)),
            score=0,
            time=0.1,
            pv=[move],
            nps=0,
            hashfull=0,
            tt_size=0,
            memory_mb=0
        )
        
        return move


class Button:
    """Button with hover effects"""
    def __init__(self, x, y, width, height, text, color, hover_color, text_color, font):
        self.rect = pygame.Rect(x, y, width, height)
        self.text = text
        self.color = color
        self.hover_color = hover_color
        self.text_color = text_color
        self.font = font
        self.hovered = False
    
    def draw(self, screen):
        color = self.hover_color if self.hovered else self.color
        pygame.draw.rect(screen, color, self.rect, border_radius=5)
        pygame.draw.rect(screen, (255, 255, 255), self.rect, 2, border_radius=5)
        
        text_surface = self.font.render(self.text, True, self.text_color)
        text_rect = text_surface.get_rect(center=self.rect.center)
        screen.blit(text_surface, text_rect)
    
    def update(self, mouse_pos):
        self.hovered = self.rect.collidepoint(mouse_pos)
    
    def is_clicked(self, mouse_pos):
        return self.rect.collidepoint(mouse_pos)


class ChessGUI:
    """Supreme GUI with engine comparison and manual bot control"""
    
    def __init__(self):
        pygame.init()
        
        self.SQUARE_SIZE = 80
        self.BOARD_SIZE = self.SQUARE_SIZE * 8
        self.PANEL_WIDTH = 500
        self.WIDTH = self.BOARD_SIZE + self.PANEL_WIDTH
        self.HEIGHT = self.BOARD_SIZE + 80
        
        self.LIGHT_SQUARE = (240, 217, 181)
        self.DARK_SQUARE = (181, 136, 99)
        self.HIGHLIGHT_COLOR = (186, 202, 68, 150)
        self.SELECTED_COLOR = (246, 246, 105, 150)
        self.BG_COLOR = (35, 35, 40)
        self.PANEL_BG = (45, 45, 50)
        self.TEXT_COLOR = (255, 255, 255)
        self.ACCENT_COLOR = (255, 215, 0)
        
        self.screen = pygame.display.set_mode((self.WIDTH, self.HEIGHT))
        pygame.display.set_caption("CockChess SUPREME 🐓👑 - 4000 ELO")
        self.clock = pygame.time.Clock()
        
        self.board = chess.Board()
        
        # Initialize engines
        self.cockchess_engine = CockChessSupreme(max_depth=30, num_threads=None, tt_size_gb=None)
        self.stockfish_engine = StockfishEngine()
        self.random_engine = RandomEngine()
        
        # Engine selection
        self.white_engine_type = EngineType.COCKCHESS
        self.black_engine_type = EngineType.COCKCHESS
        self.player_white_engine = self.cockchess_engine
        self.player_black_engine = self.cockchess_engine
        
        self.selected_square = None
        self.legal_moves = []
        self.last_move = None
        self.player_color = chess.WHITE
        self.engine_thinking = False
        self.engine_thread = None
        self.game_over = False
        self.think_time = 5.0
        self.search_depth = 15
        
        # Bot vs Bot controls
        self.bot_vs_bot = False
        self.auto_play = True  # Auto-advance moves
        self.waiting_for_next = False  # Waiting for user to press "Next Move"
        
        self.pending_engine_move = None
        
        self.pieces = self.load_pieces()
        
        self.font_title = pygame.font.Font(None, 52)
        self.font_large = pygame.font.Font(None, 32)
        self.font_medium = pygame.font.Font(None, 24)
        self.font_small = pygame.font.Font(None, 20)
        self.font_tiny = pygame.font.Font(None, 16)
        
        self.move_history = []
        self.eval_history = []
        self.game_start_time = datetime.datetime.now()
        
        self.create_buttons()
        
        print(f"🎮 CockChess SUPREME initialized")
    
    def update_engines(self):
        """Update active engines based on selection"""
        engine_map = {
            EngineType.COCKCHESS: self.cockchess_engine,
            EngineType.STOCKFISH: self.stockfish_engine,
            EngineType.RANDOM: self.random_engine
        }
        
        self.player_white_engine = engine_map[self.white_engine_type]
        self.player_black_engine = engine_map[self.black_engine_type]
    
    def create_buttons(self):
        """Create all buttons"""
        panel_x = self.BOARD_SIZE + 20
        
        # Engine selection buttons for White
        y = 120
        self.white_engine_label_y = y - 25
        
        engine_btn_width = 145
        engine_btn_height = 32
        
        self.white_cockchess_btn = Button(panel_x, y, engine_btn_width, engine_btn_height, "CockChess",
                                          (80, 50, 120), (110, 70, 160), self.TEXT_COLOR, self.font_small)
        
        self.white_stockfish_btn = Button(panel_x + engine_btn_width + 5, y, engine_btn_width, engine_btn_height, "Stockfish",
                                          (50, 80, 120), (70, 110, 160), self.TEXT_COLOR, self.font_small)
        
        self.white_random_btn = Button(panel_x + (engine_btn_width + 5) * 2, y, engine_btn_width, engine_btn_height, "Random",
                                       (80, 80, 80), (110, 110, 110), self.TEXT_COLOR, self.font_small)
        
        # Engine selection for Black
        y += 65
        self.black_engine_label_y = y - 25
        
        self.black_cockchess_btn = Button(panel_x, y, engine_btn_width, engine_btn_height, "CockChess",
                                          (80, 50, 120), (110, 70, 160), self.TEXT_COLOR, self.font_small)
        
        self.black_stockfish_btn = Button(panel_x + engine_btn_width + 5, y, engine_btn_width, engine_btn_height, "Stockfish",
                                          (50, 80, 120), (70, 110, 160), self.TEXT_COLOR, self.font_small)
        
        self.black_random_btn = Button(panel_x + (engine_btn_width + 5) * 2, y, engine_btn_width, engine_btn_height, "Random",
                                       (80, 80, 80), (110, 110, 110), self.TEXT_COLOR, self.font_small)
        
        # Depth buttons
        y = 260
        self.depth_buttons = []
        depths = [5, 10, 15, 20, 25, 30]
        btn_width = 60
        btn_height = 35
        
        for i, depth in enumerate(depths):
            row = i // 3
            col = i % 3
            x = panel_x + col * (btn_width + 10)
            y_pos = y + row * (btn_height + 10)
            
            btn = Button(x, y_pos, btn_width, btn_height, f"D{depth}", 
                        (60, 60, 70), (100, 100, 110), self.TEXT_COLOR, self.font_small)
            btn.depth = depth
            self.depth_buttons.append(btn)
        
        # Time buttons
        y = 380
        self.time_buttons = []
        times = [(1, "1s"), (3, "3s"), (5, "5s"), (10, "10s"), (20, "20s"), (30, "30s"), (60, "60s")]
        
        for i, (time_val, label) in enumerate(times):
            row = i // 3
            col = i % 3
            x = panel_x + col * (btn_width + 10)
            y_pos = y + row * (btn_height + 10)
            
            if i < len(times):
                btn = Button(x, y_pos, btn_width, btn_height, label,
                            (50, 80, 50), (70, 120, 70), self.TEXT_COLOR, self.font_small)
                btn.time = time_val
                self.time_buttons.append(btn)
        
        # Control buttons
        y = 520
        btn_width = 225
        btn_height = 40
        
        self.bot_vs_bot_btn = Button(panel_x, y, btn_width * 2 + 10, btn_height, 
                                     "🤖 Bot vs Bot Mode",
                                     (100, 50, 150), (140, 80, 190), self.TEXT_COLOR, self.font_medium)
        
        y += 48
        self.auto_play_btn = Button(panel_x, y, btn_width, btn_height,
                                    "⚡ Auto-Play: ON",
                                    (50, 120, 50), (70, 160, 70), self.TEXT_COLOR, self.font_small)
        
        self.next_move_btn = Button(panel_x + btn_width + 10, y, btn_width, btn_height,
                                    "▶ Next Move",
                                    (120, 80, 40), (160, 120, 60), self.TEXT_COLOR, self.font_small)
        
        y += 48
        self.export_txt_btn = Button(panel_x, y, (btn_width - 5) // 2, 35,
                                     "📄 TXT",
                                     (70, 70, 120), (100, 100, 160), self.TEXT_COLOR, self.font_tiny)
        
        self.export_pgn_btn = Button(panel_x + (btn_width - 5) // 2 + 5, y, (btn_width - 5) // 2, 35,
                                     "📋 PGN",
                                     (120, 70, 70), (160, 100, 100), self.TEXT_COLOR, self.font_tiny)
        
        self.undo_btn = Button(panel_x + btn_width + 10, y, btn_width, 35,
                              "↶ Undo",
                              (120, 80, 40), (160, 120, 60), self.TEXT_COLOR, self.font_small)
        
        y += 43
        self.new_game_btn = Button(panel_x, y, btn_width, 40,
                                   "New Game",
                                   (50, 120, 50), (70, 160, 70), self.TEXT_COLOR, self.font_medium)
        
        self.flip_board_btn = Button(panel_x + btn_width + 10, y, btn_width, 40,
                                     "Flip Board",
                                     (50, 80, 120), (70, 110, 160), self.TEXT_COLOR, self.font_medium)
    
    def export_to_txt(self):
        """Export game to TXT"""
        if not self.move_history:
            print("⚠ No moves to export!")
            return
        
        filename = f"cockchess_game_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.txt"
        
        try:
            with open(filename, 'w') as f:
                f.write("="*70 + "\n")
                f.write("       COCKCHESS SUPREME - 4000 ELO GAME RECORD\n")
                f.write("="*70 + "\n\n")
                
                f.write(f"Date: {self.game_start_time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"White: {self.white_engine_type.value}\n")
                f.write(f"Black: {self.black_engine_type.value}\n")
                f.write(f"Result: {self.board.result()}\n")
                f.write(f"Total Moves: {len(self.move_history)}\n\n")
                
                f.write("-"*70 + "\n")
                f.write("MOVE HISTORY:\n")
                f.write("-"*70 + "\n\n")
                
                for i in range(0, len(self.move_history), 2):
                    move_num = (i // 2) + 1
                    white_move = self.move_history[i] if i < len(self.move_history) else ""
                    black_move = self.move_history[i + 1] if i + 1 < len(self.move_history) else ""
                    
                    line = f"{move_num:3d}. {white_move:8s}"
                    if black_move:
                        line += f" {black_move:8s}"
                    
                    if i < len(self.eval_history):
                        eval_val = self.eval_history[i] / 100
                        line += f"  [{eval_val:+.2f}]"
                    
                    f.write(line + "\n")
                
                f.write("\n" + "="*70 + "\n")
                f.write(f"Powered by CockChess SUPREME - 4000+ ELO\n")
                f.write("="*70 + "\n")
            
            print(f"✅ Game exported to: {filename}")
        except Exception as e:
            print(f"❌ Export failed: {e}")
    
    def export_to_pgn(self):
        """Export to PGN"""
        if not self.move_history:
            print("⚠ No moves to export!")
            return
        
        filename = f"cockchess_game_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.pgn"
        
        try:
            game = chess.pgn.Game()
            
            game.headers["Event"] = "CockChess SUPREME Game"
            game.headers["Site"] = "Local Computer"
            game.headers["Date"] = self.game_start_time.strftime('%Y.%m.%d')
            game.headers["Round"] = "1"
            game.headers["White"] = self.white_engine_type.value
            game.headers["Black"] = self.black_engine_type.value
            game.headers["Result"] = self.board.result()
            game.headers["WhiteElo"] = "4000" if self.white_engine_type == EngineType.COCKCHESS else "3500"
            game.headers["BlackElo"] = "4000" if self.black_engine_type == EngineType.COCKCHESS else "3500"
            
            node = game
            temp_board = chess.Board()
            
            for i, san_move in enumerate(self.move_history):
                try:
                    move = temp_board.parse_san(san_move)
                    node = node.add_variation(move)
                    
                    if i < len(self.eval_history):
                        eval_val = self.eval_history[i] / 100
                        node.comment = f"{eval_val:+.2f}"
                    
                    temp_board.push(move)
                except:
                    pass
            
            with open(filename, 'w') as f:
                exporter = chess.pgn.FileExporter(f)
                game.accept(exporter)
            
            print(f"✅ Game exported to PGN: {filename}")
        except Exception as e:
            print(f"❌ PGN export failed: {e}")
    
    def load_pieces(self):
        pieces = {}
        size = int(self.SQUARE_SIZE * 0.7)
        
        for font_name in ['Segoe UI Symbol', 'Arial Unicode MS', 'DejaVu Sans', 'Noto Sans Symbols', None]:
            try:
                chess_font = pygame.font.SysFont(font_name, int(self.SQUARE_SIZE * 0.75))
                test = chess_font.render('♔', True, (0, 0, 0))
                if test.get_width() > 10:
                    piece_unicode = {
                        'K': '♔', 'Q': '♕', 'R': '♖', 'B': '♗', 'N': '♘', 'P': '♙',
                        'k': '♚', 'q': '♛', 'r': '♜', 'b': '♝', 'n': '♞', 'p': '♟'
                    }
                    
                    for symbol, unicode_char in piece_unicode.items():
                        surface = pygame.Surface((size, size), pygame.SRCALPHA)
                        
                        if symbol.isupper():
                            outline = chess_font.render(unicode_char, True, (0, 0, 0))
                            text = chess_font.render(unicode_char, True, (255, 255, 255))
                            for dx, dy in [(-2,0), (2,0), (0,-2), (0,2), (-1,-1), (-1,1), (1,-1), (1,1)]:
                                surface.blit(outline, (size//2 - outline.get_width()//2 + dx, 
                                                     size//2 - outline.get_height()//2 + dy))
                            surface.blit(text, (size//2 - text.get_width()//2, 
                                               size//2 - text.get_height()//2))
                        else:
                            text = chess_font.render(unicode_char, True, (40, 40, 40))
                            outline = chess_font.render(unicode_char, True, (180, 180, 180))
                            for dx, dy in [(-1,-1), (-1,1), (1,-1), (1,1)]:
                                surface.blit(outline, (size//2 - outline.get_width()//2 + dx, 
                                                     size//2 - outline.get_height()//2 + dy))
                            surface.blit(text, (size//2 - text.get_width()//2, 
                                               size//2 - text.get_height()//2))
                        
                        pieces[symbol] = surface
                    
                    return pieces
            except:
                continue
        
        return self._create_geometric_pieces(size)
    
    def _create_geometric_pieces(self, size):
        pieces = {}
        piece_letters = {
            'K': 'K', 'Q': 'Q', 'R': 'R', 'B': 'B', 'N': 'N', 'P': 'P',
            'k': 'K', 'q': 'Q', 'r': 'R', 'b': 'B', 'n': 'N', 'p': 'P'
        }
        
        label_font = pygame.font.Font(None, int(self.SQUARE_SIZE * 0.5))
        
        for symbol, letter in piece_letters.items():
            surface = pygame.Surface((size, size), pygame.SRCALPHA)
            center = (size // 2, size // 2)
            
            if symbol.isupper():
                piece_color = (255, 255, 255)
                border_color = (0, 0, 0)
                text_color = (0, 0, 0)
            else:
                piece_color = (60, 60, 60)
                border_color = (200, 200, 200)
                text_color = (255, 255, 255)
            
            pygame.draw.circle(surface, piece_color, center, size//3)
            pygame.draw.circle(surface, border_color, center, size//3, 3)
            
            text = label_font.render(letter, True, text_color)
            text_rect = text.get_rect(center=center)
            surface.blit(text, text_rect)
            
            pieces[symbol] = surface
        
        return pieces
    
    def square_to_coords(self, square: int) -> Tuple[int, int]:
        file = chess.square_file(square)
        rank = chess.square_rank(square)
        
        if self.player_color == chess.WHITE:
            x = file * self.SQUARE_SIZE
            y = (7 - rank) * self.SQUARE_SIZE
        else:
            x = (7 - file) * self.SQUARE_SIZE
            y = rank * self.SQUARE_SIZE
        
        return x, y
    
    def coords_to_square(self, pos: Tuple[int, int]) -> Optional[int]:
        x, y = pos
        
        if x >= self.BOARD_SIZE or y >= self.BOARD_SIZE or x < 0 or y < 0:
            return None
        
        file = x // self.SQUARE_SIZE
        rank = 7 - (y // self.SQUARE_SIZE)
        
        if self.player_color == chess.BLACK:
            file = 7 - file
            rank = 7 - rank
        
        return chess.square(file, rank)
    
    def draw_board(self):
        for square in chess.SQUARES:
            x, y = self.square_to_coords(square)
            
            is_light = (chess.square_file(square) + chess.square_rank(square)) % 2 == 1
            color = self.LIGHT_SQUARE if is_light else self.DARK_SQUARE
            
            pygame.draw.rect(self.screen, color, (x, y, self.SQUARE_SIZE, self.SQUARE_SIZE))
            
            if self.last_move and square in [self.last_move.from_square, self.last_move.to_square]:
                s = pygame.Surface((self.SQUARE_SIZE, self.SQUARE_SIZE), pygame.SRCALPHA)
                s.fill((255, 255, 0, 100))
                self.screen.blit(s, (x, y))
            
            if self.selected_square == square and not self.bot_vs_bot:
                s = pygame.Surface((self.SQUARE_SIZE, self.SQUARE_SIZE), pygame.SRCALPHA)
                s.fill(self.SELECTED_COLOR)
                self.screen.blit(s, (x, y))
            
            if self.selected_square is not None and not self.bot_vs_bot:
                for move in self.legal_moves:
                    if move.to_square == square:
                        s = pygame.Surface((self.SQUARE_SIZE, self.SQUARE_SIZE), pygame.SRCALPHA)
                        s.fill(self.HIGHLIGHT_COLOR)
                        self.screen.blit(s, (x, y))
                        
                        center = (x + self.SQUARE_SIZE // 2, y + self.SQUARE_SIZE // 2)
                        if self.board.piece_at(square):
                            pygame.draw.circle(self.screen, (100, 100, 100, 200), center, 
                                             self.SQUARE_SIZE // 3, 7)
                        else:
                            pygame.draw.circle(self.screen, (100, 100, 100, 200), center, 14)
        
        coord_font = pygame.font.Font(None, 18)
        for i in range(8):
            file_label = chr(ord('a') + i) if self.player_color == chess.WHITE else chr(ord('h') - i)
            text = coord_font.render(file_label, True, 
                                    self.DARK_SQUARE if i % 2 == 0 else self.LIGHT_SQUARE)
            self.screen.blit(text, (i * self.SQUARE_SIZE + 5, self.BOARD_SIZE - 20))
            
            rank_label = str(8 - i) if self.player_color == chess.WHITE else str(i + 1)
            text = coord_font.render(rank_label, True, 
                                    self.LIGHT_SQUARE if i % 2 == 0 else self.DARK_SQUARE)
            self.screen.blit(text, (self.BOARD_SIZE - 15, i * self.SQUARE_SIZE + 5))
    
    def draw_pieces(self):
        for square in chess.SQUARES:
            piece = self.board.piece_at(square)
            if piece:
                x, y = self.square_to_coords(square)
                symbol = piece.symbol()
                piece_img = self.pieces.get(symbol)
                
                if piece_img:
                    piece_rect = piece_img.get_rect()
                    piece_rect.center = (x + self.SQUARE_SIZE // 2, y + self.SQUARE_SIZE // 2)
                    self.screen.blit(piece_img, piece_rect)
    
    def draw_panel(self):
        panel_x = self.BOARD_SIZE
        
        pygame.draw.rect(self.screen, self.PANEL_BG, (panel_x, 0, self.PANEL_WIDTH, self.HEIGHT))
        
        y = 10
        
        # Title
        title = self.font_title.render("CockChess", True, self.ACCENT_COLOR)
        self.screen.blit(title, (panel_x + 15, y))
        y += 52
        
        supreme = self.font_medium.render("SUPREME EDITION", True, (255, 50, 50))
        self.screen.blit(supreme, (panel_x + 120, y))
        y += 25
        
        elo_claim = self.font_small.render("⚡ Claimed 4000+ ELO ⚡", True, (100, 255, 100))
        self.screen.blit(elo_claim, (panel_x + 120, y))
        y += 30
        
        pygame.draw.line(self.screen, (100, 100, 100), (panel_x + 20, y), (panel_x + self.PANEL_WIDTH - 20, y), 2)
        y += 10
        
        # Engine selection labels
        white_label = self.font_small.render("White Engine:", True, (255, 255, 255))
        self.screen.blit(white_label, (panel_x + 20, self.white_engine_label_y))
        
        black_label = self.font_small.render("Black Engine:", True, (255, 255, 255))
        self.screen.blit(black_label, (panel_x + 20, self.black_engine_label_y))
        
        # Draw engine buttons
        for btn in [self.white_cockchess_btn, self.white_stockfish_btn, self.white_random_btn]:
            if btn == self.white_cockchess_btn and self.white_engine_type == EngineType.COCKCHESS:
                btn.color = (120, 80, 180)
                btn.hover_color = (150, 110, 210)
            elif btn == self.white_stockfish_btn and self.white_engine_type == EngineType.STOCKFISH:
                btn.color = (80, 120, 180)
                btn.hover_color = (110, 150, 210)
            elif btn == self.white_random_btn and self.white_engine_type == EngineType.RANDOM:
                btn.color = (120, 120, 120)
                btn.hover_color = (150, 150, 150)
            else:
                btn.color = (60, 60, 70)
                btn.hover_color = (90, 90, 100)
            btn.draw(self.screen)
        
        for btn in [self.black_cockchess_btn, self.black_stockfish_btn, self.black_random_btn]:
            if btn == self.black_cockchess_btn and self.black_engine_type == EngineType.COCKCHESS:
                btn.color = (120, 80, 180)
                btn.hover_color = (150, 110, 210)
            elif btn == self.black_stockfish_btn and self.black_engine_type == EngineType.STOCKFISH:
                btn.color = (80, 120, 180)
                btn.hover_color = (110, 150, 210)
            elif btn == self.black_random_btn and self.black_engine_type == EngineType.RANDOM:
                btn.color = (120, 120, 120)
                btn.hover_color = (150, 150, 150)
            else:
                btn.color = (60, 60, 70)
                btn.hover_color = (90, 90, 100)
            btn.draw(self.screen)
        
        # Depth section
        y = 230
        depth_label = self.font_small.render(f"Depth: {self.search_depth}", True, (150, 255, 150))
        self.screen.blit(depth_label, (panel_x + 20, y))
        
        for btn in self.depth_buttons:
            if btn.depth == self.search_depth:
                btn.color = (100, 150, 100)
                btn.hover_color = (130, 180, 130)
            else:
                btn.color = (60, 60, 70)
                btn.hover_color = (100, 100, 110)
            btn.draw(self.screen)
        
        # Time section
        y = 350
        time_label = self.font_small.render(f"Time: {self.think_time}s", True, (255, 200, 100))
        self.screen.blit(time_label, (panel_x + 20, y))
        
        for btn in self.time_buttons:
            if btn.time == self.think_time:
                btn.color = (80, 120, 80)
                btn.hover_color = (110, 160, 110)
            else:
                btn.color = (50, 80, 50)
                btn.hover_color = (70, 120, 70)
            btn.draw(self.screen)
        
        y = 490
        pygame.draw.line(self.screen, (100, 100, 100), (panel_x + 20, y), (panel_x + self.PANEL_WIDTH - 20, y), 2)
        
        # Control buttons
        if self.bot_vs_bot:
            self.bot_vs_bot_btn.color = (140, 70, 190)
            self.bot_vs_bot_btn.hover_color = (170, 100, 220)
        else:
            self.bot_vs_bot_btn.color = (100, 50, 150)
            self.bot_vs_bot_btn.hover_color = (140, 80, 190)
        self.bot_vs_bot_btn.draw(self.screen)
        
        # Auto-play toggle
        self.auto_play_btn.text = f"⚡ Auto-Play: {'ON' if self.auto_play else 'OFF'}"
        if self.auto_play:
            self.auto_play_btn.color = (50, 150, 50)
            self.auto_play_btn.hover_color = (70, 190, 70)
        else:
            self.auto_play_btn.color = (150, 50, 50)
            self.auto_play_btn.hover_color = (190, 70, 70)
        self.auto_play_btn.draw(self.screen)
        
        # Next Move button (only enabled in manual mode)
        next_enabled = self.bot_vs_bot and not self.auto_play and self.waiting_for_next and not self.engine_thinking
        if not next_enabled:
            self.next_move_btn.color = (60, 60, 60)
            self.next_move_btn.hover_color = (70, 70, 70)
            self.next_move_btn.text_color = (120, 120, 120)
        else:
            self.next_move_btn.color = (120, 160, 40)
            self.next_move_btn.hover_color = (160, 200, 60)
            self.next_move_btn.text_color = (255, 255, 255)
        self.next_move_btn.draw(self.screen)
        
        self.export_txt_btn.draw(self.screen)
        self.export_pgn_btn.draw(self.screen)
        
        # Undo
        undo_enabled = len(self.move_history) >= 2 and not self.engine_thinking and not self.game_over and not self.bot_vs_bot
        if not undo_enabled:
            self.undo_btn.color = (60, 60, 60)
            self.undo_btn.hover_color = (70, 70, 70)
            self.undo_btn.text_color = (120, 120, 120)
        else:
            self.undo_btn.color = (120, 80, 40)
            self.undo_btn.hover_color = (160, 120, 60)
            self.undo_btn.text_color = (255, 255, 255)
        self.undo_btn.draw(self.screen)
        
        self.new_game_btn.draw(self.screen)
        self.flip_board_btn.draw(self.screen)
    
    def handle_square_click(self, square: int):
        if self.engine_thinking or self.game_over or self.bot_vs_bot:
            return
        
        if self.board.turn != self.player_color:
            return
        
        piece = self.board.piece_at(square)
        
        if piece and piece.color == self.player_color:
            self.selected_square = square
            self.legal_moves = [move for move in self.board.legal_moves if move.from_square == square]
        elif self.selected_square is not None:
            move = None
            for legal_move in self.legal_moves:
                if legal_move.to_square == square:
                    move = legal_move
                    break
            
            if move:
                if move.promotion is None and self.board.piece_at(self.selected_square).piece_type == chess.PAWN:
                    if (self.player_color == chess.WHITE and chess.square_rank(square) == 7) or \
                       (self.player_color == chess.BLACK and chess.square_rank(square) == 0):
                        move = chess.Move(self.selected_square, square, promotion=chess.QUEEN)
                
                self.make_move(move)
            
            self.selected_square = None
            self.legal_moves = []
    
    def make_move(self, move: chess.Move):
        san = self.board.san(move)
        self.board.push(move)
        self.last_move = move
        self.move_history.append(san)
        
        # Get eval from the engine that just moved
        if self.board.turn == chess.BLACK:
            engine = self.player_white_engine
        else:
            engine = self.player_black_engine
        
        if hasattr(engine, 'search_info') and engine.search_info:
            self.eval_history.append(engine.search_info.score)
        
        if self.board.is_game_over():
            self.game_over = True
            result = self.board.result()
            print(f"\n{'='*100}")
            print(f"🏆 GAME OVER! Result: {result}")
            print(f"{'='*100}\n")
            self.bot_vs_bot = False
            self.waiting_for_next = False
        else:
            if self.bot_vs_bot:
                if self.auto_play:
                    # Auto-advance
                    self.start_engine_move()
                else:
                    # Wait for user to press "Next Move"
                    self.waiting_for_next = True
            elif self.board.turn != self.player_color:
                self.start_engine_move()
    
    def start_engine_move(self):
        if not self.engine_thinking:
            self.waiting_for_next = False
            self.engine_thinking = True
            self.cockchess_engine.max_depth = self.search_depth
            self.engine_thread = threading.Thread(target=self.engine_move_thread)
            self.engine_thread.daemon = True
            self.engine_thread.start()
    
    def engine_move_thread(self):
        try:
            # Select correct engine
            if self.board.turn == chess.WHITE:
                engine = self.player_white_engine
            else:
                engine = self.player_black_engine
            
            move = engine.get_best_move(self.board, think_time=self.think_time)
            if move:
                self.pending_engine_move = move
        except Exception as e:
            print(f"❌ Engine error: {e}")
        finally:
            self.engine_thinking = False
    
    def undo_move(self):
        if len(self.move_history) >= 2 and not self.engine_thinking and not self.game_over and not self.bot_vs_bot:
            for _ in range(2):
                if len(self.board.move_stack) > 0:
                    self.board.pop()
                    self.move_history.pop()
                    if self.eval_history:
                        self.eval_history.pop()
            
            if len(self.board.move_stack) > 0:
                self.last_move = self.board.peek()
            else:
                self.last_move = None
            
            self.selected_square = None
            self.legal_moves = []
            self.game_over = False
            
            print("↶ Move undone")
    
    def new_game(self):
        if self.engine_thinking:
            return
        
        self.board = chess.Board()
        self.selected_square = None
        self.legal_moves = []
        self.last_move = None
        self.game_over = False
        self.move_history = []
        self.eval_history = []
        self.pending_engine_move = None
        self.waiting_for_next = False
        self.game_start_time = datetime.datetime.now()
        
        self.cockchess_engine.history_heuristic.clear()
        self.cockchess_engine.killer_moves = [[None, None] for _ in range(200)]
        self.cockchess_engine.tt_age += 1
        
        print(f"\n{'='*100}")
        print("🎮 NEW GAME")
        print(f"White: {self.white_engine_type.value} | Black: {self.black_engine_type.value}")
        print(f"{'='*100}\n")
        
        if self.bot_vs_bot:
            if self.auto_play:
                self.start_engine_move()
            else:
                self.waiting_for_next = True
    
    def toggle_bot_vs_bot(self):
        if not self.engine_thinking:
            self.bot_vs_bot = not self.bot_vs_bot
            mode = "BOT VS BOT" if self.bot_vs_bot else "HUMAN VS BOT"
            print(f"\n🎮 Mode: {mode}")
            
            if self.bot_vs_bot and not self.game_over:
                if self.auto_play:
                    self.start_engine_move()
                else:
                    self.waiting_for_next = True
    
    def toggle_auto_play(self):
        self.auto_play = not self.auto_play
        print(f"⚡ Auto-play: {'ON' if self.auto_play else 'OFF'}")
        
        if self.bot_vs_bot and self.auto_play and self.waiting_for_next:
            self.start_engine_move()
    
    def next_move_manual(self):
        """Manually advance to next move in bot vs bot"""
        if self.bot_vs_bot and not self.auto_play and self.waiting_for_next and not self.engine_thinking:
            self.start_engine_move()
    
    def flip_board(self):
        self.player_color = not self.player_color
    
    def run(self):
        running = True
        
        while running:
            mouse_pos = pygame.mouse.get_pos()
            
            # Update button hover states
            for btn in self.depth_buttons + self.time_buttons:
                btn.update(mouse_pos)
            
            for btn in [self.white_cockchess_btn, self.white_stockfish_btn, self.white_random_btn,
                       self.black_cockchess_btn, self.black_stockfish_btn, self.black_random_btn]:
                btn.update(mouse_pos)
            
            self.bot_vs_bot_btn.update(mouse_pos)
            self.auto_play_btn.update(mouse_pos)
            self.next_move_btn.update(mouse_pos)
            self.export_txt_btn.update(mouse_pos)
            self.export_pgn_btn.update(mouse_pos)
            self.undo_btn.update(mouse_pos)
            self.new_game_btn.update(mouse_pos)
            self.flip_board_btn.update(mouse_pos)
            
            # Apply pending engine move
            if self.pending_engine_move and not self.engine_thinking:
                pygame.time.wait(100)
                self.make_move(self.pending_engine_move)
                self.pending_engine_move = None
            
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    running = False
                
                elif event.type == pygame.MOUSEBUTTONDOWN:
                    pos = pygame.mouse.get_pos()
                    
                    if pos[0] < self.BOARD_SIZE and pos[1] < self.BOARD_SIZE:
                        square = self.coords_to_square(pos)
                        if square is not None:
                            self.handle_square_click(square)
                    
                    else:
                        # White engine selection
                        if self.white_cockchess_btn.is_clicked(pos):
                            self.white_engine_type = EngineType.COCKCHESS
                            self.update_engines()
                            print("White: CockChess Supreme")
                        elif self.white_stockfish_btn.is_clicked(pos):
                            self.white_engine_type = EngineType.STOCKFISH
                            self.update_engines()
                            print("White: Stockfish")
                        elif self.white_random_btn.is_clicked(pos):
                            self.white_engine_type = EngineType.RANDOM
                            self.update_engines()
                            print("White: Random")
                        
                        # Black engine selection
                        elif self.black_cockchess_btn.is_clicked(pos):
                            self.black_engine_type = EngineType.COCKCHESS
                            self.update_engines()
                            print("Black: CockChess Supreme")
                        elif self.black_stockfish_btn.is_clicked(pos):
                            self.black_engine_type = EngineType.STOCKFISH
                            self.update_engines()
                            print("Black: Stockfish")
                        elif self.black_random_btn.is_clicked(pos):
                            self.black_engine_type = EngineType.RANDOM
                            self.update_engines()
                            print("Black: Random")
                        
                        # Depth buttons
                        for btn in self.depth_buttons:
                            if btn.is_clicked(pos):
                                self.search_depth = btn.depth
                                print(f"📊 Depth: {btn.depth}")
                        
                        # Time buttons
                        for btn in self.time_buttons:
                            if btn.is_clicked(pos):
                                self.think_time = btn.time
                                print(f"⏱ Time: {btn.time}s")
                        
                        # Control buttons
                        if self.bot_vs_bot_btn.is_clicked(pos):
                            self.toggle_bot_vs_bot()
                        
                        elif self.auto_play_btn.is_clicked(pos):
                            self.toggle_auto_play()
                        
                        elif self.next_move_btn.is_clicked(pos):
                            self.next_move_manual()
                        
                        elif self.export_txt_btn.is_clicked(pos):
                            self.export_to_txt()
                        
                        elif self.export_pgn_btn.is_clicked(pos):
                            self.export_to_pgn()
                        
                        elif self.undo_btn.is_clicked(pos):
                            self.undo_move()
                        
                        elif self.new_game_btn.is_clicked(pos):
                            self.new_game()
                        
                        elif self.flip_board_btn.is_clicked(pos):
                            self.flip_board()
            
            # Drawing
            self.screen.fill(self.BG_COLOR)
            self.draw_board()
            self.draw_pieces()
            self.draw_panel()
            
            pygame.display.flip()
            self.clock.tick(60)
        
        # Cleanup
        self.cockchess_engine.stop_search = True
        if self.engine_thread and self.engine_thread.is_alive():
            self.engine_thread.join(timeout=2.0)
        
        if self.stockfish_engine.engine:
            self.stockfish_engine.quit()
        
        pygame.quit()
        sys.exit()


if __name__ == "__main__":
    print("="*100)
    print("   🐓👑 COCKCHESS SUPREME - THE STOCKFISH KILLER (ALLEGEDLY) 👑🐓")
    print("="*100)
    print("\n📊 Claimed Rating: 4000+ ELO (totally legit, trust us 😏)")
    print(f"💻 CPU Cores: {multiprocessing.cpu_count()}")
    print(f"💾 RAM: {psutil.virtual_memory().total / (1024**3):.1f} GB")
    print("\n🆕 SUPREME FEATURES:")
    print("   ✓ Compare vs Stockfish engine!")
    print("   ✓ Choose different engines for White/Black")
    print("   ✓ Bot vs Bot with manual control")
    print("   ✓ Auto-play or step-by-step mode")
    print("   ✓ Press 'Next Move' to advance manually")
    print("   ✓ Export games to TXT/PGN")
    print("   ✓ Full engine comparison")
    print("\n🎮 Bot vs Bot Controls:")
    print("   • Enable 'Bot vs Bot Mode'")
    print("   • Toggle 'Auto-Play' ON: Plays automatically")
    print("   • Toggle 'Auto-Play' OFF: Click 'Next Move' to advance")
    print("\n🔥 Engine Selection:")
    print("   • CockChess Supreme: Our 4000 ELO beast")
    print("   • Stockfish: The competition")
    print("   • Random: For testing/fun")
    print("\n📦 Initializing...")
    
    try:
        gui = ChessGUI()
        print("✅ CockChess SUPREME ready!")
        print("\n🚀 Starting...\n")
        
        gui.run()
    except Exception as e:
        print(f"\n❌ Error: {e}")
        import traceback
        traceback.print_exc()
