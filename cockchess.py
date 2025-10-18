# cockchess_ultra_max.py
import chess
import chess.polyglot
import pygame
import sys
import threading
import multiprocessing
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Optional, Tuple, List, Dict
import time
from dataclasses import dataclass
import random
import math

@dataclass
class SearchInfo:
    depth: int
    nodes: int
    score: int
    time: float
    pv: List[chess.Move]
    nps: int
    hashfull: int

class TranspositionEntry:
    def __init__(self, depth: int, score: int, flag: str, best_move: chess.Move = None, age: int = 0):
        self.depth = depth
        self.score = score
        self.flag = flag
        self.best_move = best_move
        self.age = age

class CockChessUltraMax:
    """
    Ultra-strong 3500 ELO multi-threaded chess engine
    """
    
    def __init__(self, max_depth: int = 20, num_threads: int = None):
        self.max_depth = max_depth
        self.num_threads = num_threads or max(1, multiprocessing.cpu_count() - 1)
        self.nodes_searched = 0
        self.tt = {}
        self.tt_size = 100000000  # 100M entries
        self.tt_age = 0
        self.killer_moves = [[None, None] for _ in range(200)]
        self.history_heuristic = {}
        self.counter_moves = {}
        self.search_info = None
        self.searching = False
        self.stop_search = False
        self.pv_table = {}
        
        # Enhanced piece values (more granular)
        self.PIECE_VALUES = {
            chess.PAWN: 100,
            chess.KNIGHT: 325,
            chess.BISHOP: 335,
            chess.ROOK: 500,
            chess.QUEEN: 975,
            chess.KING: 20000
        }
        
        # Advanced evaluation parameters
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
        
        # Contempt (prefer not to draw)
        self.CONTEMPT = 10
        
        self.pst = self._initialize_advanced_pst()
        self.opening_book = self._load_opening_book()
        
        print(f"🔥 Engine initialized with {self.num_threads} threads")
    
    def _initialize_advanced_pst(self) -> Dict:
        """Advanced piece-square tables with refined values"""
        pst = {}
        
        # Pawn PST - encourage center control and advancement
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
        
        # Knight PST - centralization
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
        
        # Bishop PST - long diagonals
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
        
        # Rook PST - seventh rank and files
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
        
        # Queen PST
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
        
        # King middlegame - safety
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
        
        # King endgame - centralization
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
        """Extended opening book"""
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
        """Get move from opening book"""
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
        """Calculate game phase (0 = endgame, 1 = opening/middlegame)"""
        total_material = 0
        for piece_type in [chess.KNIGHT, chess.BISHOP, chess.ROOK, chess.QUEEN]:
            total_material += len(board.pieces(piece_type, chess.WHITE)) * self.PIECE_VALUES[piece_type]
            total_material += len(board.pieces(piece_type, chess.BLACK)) * self.PIECE_VALUES[piece_type]
        
        max_material = (4 * 325 + 4 * 335 + 4 * 500 + 2 * 975)
        phase = min(1.0, total_material / max_material)
        return phase
    
    def evaluate_pawn_structure(self, board: chess.Board, color: chess.Color) -> int:
        """Advanced pawn structure evaluation"""
        score = 0
        pawns = board.pieces(chess.PAWN, color)
        
        for pawn_square in pawns:
            file = chess.square_file(pawn_square)
            rank = chess.square_rank(pawn_square)
            
            # Doubled pawns
            same_file_pawns = [p for p in pawns if chess.square_file(p) == file]
            if len(same_file_pawns) > 1:
                score -= self.DOUBLED_PAWN_PENALTY
            
            # Isolated pawns
            adjacent_files = [file - 1, file + 1]
            has_neighbor = any(chess.square_file(p) in adjacent_files for p in pawns)
            if not has_neighbor:
                score -= self.ISOLATED_PAWN_PENALTY
            
            # Backward pawns
            if color == chess.WHITE:
                supporting_squares = [chess.square(f, rank - 1) for f in adjacent_files if 0 <= f < 8 and rank > 0]
            else:
                supporting_squares = [chess.square(f, rank + 1) for f in adjacent_files if 0 <= f < 8 and rank < 7]
            
            has_support = any(board.piece_at(sq) and board.piece_at(sq).piece_type == chess.PAWN 
                            and board.piece_at(sq).color == color for sq in supporting_squares)
            
            if not has_support and has_neighbor:
                score -= self.BACKWARD_PAWN_PENALTY
            
            # Passed pawns
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
                
                # Extra bonus if protected
                if has_support:
                    score += self.PASSED_PAWN_BONUS[bonus_rank] // 2
        
        return score
    
    def evaluate_king_safety(self, board: chess.Board, color: chess.Color) -> int:
        """Advanced king safety evaluation"""
        score = 0
        king_square = board.king(color)
        
        if king_square is None:
            return 0
        
        king_file = chess.square_file(king_square)
        king_rank = chess.square_rank(king_square)
        
        # Pawn shield
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
            
            # Penalty for broken shield
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
        
        # Attack on king zone
        king_zone = [
            chess.square(f, r)
            for f in range(max(0, king_file - 1), min(8, king_file + 2))
            for r in range(max(0, king_rank - 1), min(8, king_rank + 2))
        ]
        
        attackers = 0
        attack_weight = 0
        for sq in king_zone:
            # Count attackers by type
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
        
        # Open files near king
        for f in range(max(0, king_file - 1), min(8, king_file + 2)):
            pawns_on_file = sum(1 for sq in chess.SQUARES 
                               if chess.square_file(sq) == f 
                               and board.piece_at(sq) 
                               and board.piece_at(sq).piece_type == chess.PAWN
                               and board.piece_at(sq).color == color)
            if pawns_on_file == 0:
                score -= 30  # Open file near king is dangerous
        
        return score
    
    def evaluate_board(self, board: chess.Board) -> int:
        """Ultra-advanced evaluation function"""
        if board.is_checkmate():
            return -999999 if board.turn else 999999
        
        if board.is_stalemate() or board.is_insufficient_material():
            # Apply contempt
            return -self.CONTEMPT if board.turn == chess.WHITE else self.CONTEMPT
        
        if board.can_claim_fifty_moves():
            return 0
        
        score = 0
        phase = self.game_phase(board)
        
        # Material and positional
        for square in chess.SQUARES:
            piece = board.piece_at(square)
            if piece is None:
                continue
            
            value = self.PIECE_VALUES[piece.piece_type]
            
            # Piece-square tables
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
        
        # Bishop pair
        if len(board.pieces(chess.BISHOP, chess.WHITE)) >= 2:
            score += self.BISHOP_PAIR_BONUS
        if len(board.pieces(chess.BISHOP, chess.BLACK)) >= 2:
            score -= self.BISHOP_PAIR_BONUS
        
        # Rook evaluation
        white_rooks = list(board.pieces(chess.ROOK, chess.WHITE))
        black_rooks = list(board.pieces(chess.ROOK, chess.BLACK))
        
        # Connected rooks
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
        
        # Rooks on open/semi-open files and seventh rank
        for color in [chess.WHITE, chess.BLACK]:
            for rook_sq in board.pieces(chess.ROOK, color):
                file = chess.square_file(rook_sq)
                rank = chess.square_rank(rook_sq)
                
                # Seventh rank
                if (color == chess.WHITE and rank == 6) or (color == chess.BLACK and rank == 1):
                    score += self.ROOK_ON_SEVENTH if color == chess.WHITE else -self.ROOK_ON_SEVENTH
                
                # Open files
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
        
        # Pawn structure
        score += self.evaluate_pawn_structure(board, chess.WHITE)
        score -= self.evaluate_pawn_structure(board, chess.BLACK)
        
        # King safety (more important in middlegame)
        if phase > 0.25:
            king_safety = (self.evaluate_king_safety(board, chess.WHITE) - 
                          self.evaluate_king_safety(board, chess.BLACK))
            score += int(king_safety * phase)
        
        # Mobility (very important)
        original_turn = board.turn
        board.turn = chess.WHITE
        white_mobility = board.legal_moves.count()
        board.turn = chess.BLACK
        black_mobility = board.legal_moves.count()
        board.turn = original_turn
        
        score += (white_mobility - black_mobility) * self.MOBILITY_WEIGHT
        
        # Tempo bonus
        score += self.TEMPO_BONUS if board.turn == chess.WHITE else -self.TEMPO_BONUS
        
        # Center control
        center_squares = [chess.E4, chess.E5, chess.D4, chess.D5]
        for sq in center_squares:
            if board.is_attacked_by(chess.WHITE, sq):
                score += 5
            if board.is_attacked_by(chess.BLACK, sq):
                score -= 5
        
        return score if board.turn == chess.WHITE else -score
    
    def quiescence_search(self, board: chess.Board, alpha: int, beta: int, depth: int = 0) -> int:
        """Enhanced quiescence search"""
        self.nodes_searched += 1
        
        if depth > 25 or self.stop_search:
            return self.evaluate_board(board)
        
        stand_pat = self.evaluate_board(board)
        
        if stand_pat >= beta:
            return beta
        
        # Delta pruning
        BIG_DELTA = 975  # Queen value
        if stand_pat < alpha - BIG_DELTA:
            return alpha
        
        if alpha < stand_pat:
            alpha = stand_pat
        
        # Generate tactical moves
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
        """Advanced move ordering for better pruning"""
        move_scores = []
        
        for move in moves:
            score = 0
            
            # Hash move (from TT) - highest priority
            if hash_move and move == hash_move:
                score += 1000000
            
            # Winning captures (MVV-LVA)
            elif board.is_capture(move):
                victim = board.piece_at(move.to_square)
                attacker = board.piece_at(move.from_square)
                if victim and attacker:
                    score += 100000 + self.PIECE_VALUES[victim.piece_type] * 10 - self.PIECE_VALUES[attacker.piece_type]
            
            # Promotions
            elif move.promotion:
                score += 90000 + self.PIECE_VALUES[move.promotion]
            
            # Killer moves
            elif ply < len(self.killer_moves):
                if self.killer_moves[ply][0] == move:
                    score += 80000
                elif self.killer_moves[ply][1] == move:
                    score += 70000
            
            # Counter moves
            if move in self.counter_moves.values():
                score += 60000
            
            # History heuristic
            move_key = (move.from_square, move.to_square)
            if move_key in self.history_heuristic:
                score += min(50000, self.history_heuristic[move_key])
            
            # Checks
            board.push(move)
            if board.is_check():
                score += 40000
            board.pop()
            
            # Castling
            if board.is_castling(move):
                score += 30000
            
            # Central moves
            if move.to_square in [chess.E4, chess.E5, chess.D4, chess.D5]:
                score += 1000
            
            move_scores.append((score, move))
        
        move_scores.sort(reverse=True, key=lambda x: x[0])
        return [move for _, move in move_scores]
    
    def pvs_search(self, board: chess.Board, depth: int, alpha: int, beta: int, 
                   ply: int, allow_null: bool = True, thread_id: int = 0) -> int:
        """Principal Variation Search with advanced pruning"""
        self.nodes_searched += 1
        pv_node = (beta - alpha) > 1
        
        if self.stop_search:
            return 0
        
        # Draw detection
        if board.is_repetition(2) or board.can_claim_fifty_moves():
            # Apply contempt
            return -self.CONTEMPT if board.turn == chess.WHITE else self.CONTEMPT
        
        # Mate distance pruning
        alpha_orig = alpha
        alpha = max(alpha, -999999 + ply)
        beta = min(beta, 999999 - ply - 1)
        if alpha >= beta:
            return alpha
        
        # Transposition table lookup
        board_hash = chess.polyglot.zobrist_hash(board)
        tt_entry = self.tt.get(board_hash)
        hash_move = None
        
        if tt_entry and tt_entry.depth >= depth and tt_entry.age == self.tt_age:
            hash_move = tt_entry.best_move
            if not pv_node:
                if tt_entry.flag == 'EXACT':
                    return tt_entry.score
                elif tt_entry.flag == 'LOWERBOUND':
                    alpha = max(alpha, tt_entry.score)
                elif tt_entry.flag == 'UPPERBOUND':
                    beta = min(beta, tt_entry.score)
                
                if alpha >= beta:
                    return tt_entry.score
        
        # Quiescence search at leaf nodes
        if depth == 0:
            return self.quiescence_search(board, alpha, beta)
        
        if board.is_game_over():
            return self.evaluate_board(board)
        
        in_check = board.is_check()
        
        # Null move pruning (more aggressive)
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
        
        # Razoring
        if depth <= 3 and not in_check and not pv_node:
            eval_score = self.evaluate_board(board)
            razor_margin = 400 * depth
            if eval_score + razor_margin < alpha:
                q_score = self.quiescence_search(board, alpha, beta)
                if q_score < alpha:
                    return q_score
        
        # Futility pruning (more aggressive)
        futility_margin = [0, 250, 400, 600]
        if depth <= 3 and not in_check and not pv_node:
            eval_score = self.evaluate_board(board)
            if eval_score + futility_margin[depth] <= alpha:
                return self.quiescence_search(board, alpha, beta)
        
        # Internal Iterative Deepening
        if depth >= 4 and hash_move is None and pv_node:
            self.pvs_search(board, depth - 2, alpha, beta, ply, True, thread_id)
            tt_entry = self.tt.get(board_hash)
            if tt_entry:
                hash_move = tt_entry.best_move
        
        legal_moves = list(board.legal_moves)
        if not legal_moves:
            return self.evaluate_board(board)
        
        # Move ordering
        legal_moves = self.order_moves(board, legal_moves, ply, hash_move)
        
        best_score = float('-inf')
        best_move = None
        moves_searched = 0
        
        # PVS loop
        for i, move in enumerate(legal_moves):
            board.push(move)
            
            # Check extension
            extension = 0
            if board.is_check():
                extension = 1
            # Passed pawn extension
            elif move.promotion:
                extension = 1
            
            new_depth = depth - 1 + extension
            
            if moves_searched == 0:
                # Search first move with full window
                score = -self.pvs_search(board, new_depth, -beta, -alpha, ply + 1, True, thread_id)
            else:
                # Late Move Reductions (more aggressive)
                do_lmr = (
                    moves_searched >= 3 and
                    depth >= 3 and
                    not in_check and
                    not board.is_check() and
                    not board.is_capture(move) and
                    not move.promotion
                )
                
                if do_lmr:
                    # Adaptive reduction
                    reduction = 1
                    if moves_searched >= 6:
                        reduction = 2
                    if depth > 6 and moves_searched >= 10:
                        reduction = 3
                    if depth > 10 and moves_searched >= 15:
                        reduction = 4
                    
                    reduction = min(reduction, new_depth - 1)
                    
                    # Null window search with reduction
                    score = -self.pvs_search(board, new_depth - reduction, -alpha - 1, -alpha, ply + 1, True, thread_id)
                    
                    # Re-search if it failed high
                    if score > alpha:
                        score = -self.pvs_search(board, new_depth, -alpha - 1, -alpha, ply + 1, True, thread_id)
                else:
                    # Null window search
                    score = -self.pvs_search(board, new_depth, -alpha - 1, -alpha, ply + 1, True, thread_id)
                
                # Re-search with full window if necessary
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
                # Update killers and history
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
                
                break  # Beta cutoff
        
        # Store in transposition table
        if best_score <= alpha_orig:
            flag = 'UPPERBOUND'
        elif best_score >= beta:
            flag = 'LOWERBOUND'
        else:
            flag = 'EXACT'
        
        self.tt[board_hash] = TranspositionEntry(depth, best_score, flag, best_move, self.tt_age)
        
        # TT size management
        if len(self.tt) > self.tt_size:
            # Remove oldest entries
            old_entries = [k for k, v in self.tt.items() if v.age < self.tt_age - 2]
            for key in old_entries[:len(old_entries) // 2]:
                del self.tt[key]
        
        return best_score
    
    def search_move_parallel(self, board: chess.Board, move: chess.Move, depth: int, alpha: int, beta: int) -> Tuple[chess.Move, int]:
        """Search a single move (for parallel search)"""
        board_copy = board.copy()
        board_copy.push(move)
        score = -self.pvs_search(board_copy, depth - 1, -beta, -alpha, 1, True, 0)
        return (move, score)
    
    def iterative_deepening(self, board: chess.Board, max_time: float = 10.0) -> Tuple[chess.Move, SearchInfo]:
        """Iterative deepening with parallel search"""
        self.stop_search = False
        start_time = time.time()
        best_move = None
        best_score = 0
        self.tt_age += 1
        
        for depth in range(1, self.max_depth + 1):
            if time.time() - start_time > max_time * 0.95:
                break
            
            self.nodes_searched = 0
            
            # Aspiration windows (adaptive)
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
                
                # Move ordering with previous best
                if best_move and best_move in legal_moves:
                    legal_moves.remove(best_move)
                    legal_moves.insert(0, best_move)
                else:
                    legal_moves = self.order_moves(board, legal_moves, 0)
                
                # Parallel search for first few moves
                if depth >= 6 and self.num_threads > 1 and len(legal_moves) > 3:
                    # Search first move normally
                    first_move = legal_moves[0]
                    board.push(first_move)
                    score = -self.pvs_search(board, depth - 1, -beta, -alpha, 1, True, 0)
                    board.pop()
                    
                    current_best = first_move
                    current_score = score
                    
                    if score > alpha:
                        alpha = score
                    
                    # Search remaining moves in parallel
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
                    # Sequential search
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
                
                # Check aspiration window
                if aspiration_search and not search_failed:
                    if current_score <= alpha - window:
                        # Fail low - widen window down
                        alpha = float('-inf')
                        search_failed = True
                        continue
                    elif current_score >= beta:
                        # Fail high - widen window up
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
            
            self.search_info = SearchInfo(
                depth=depth,
                nodes=self.nodes_searched,
                score=best_score,
                time=elapsed,
                pv=[best_move] if best_move else [],
                nps=nps,
                hashfull=hashfull
            )
            
            # Display info
            if abs(best_score) > 900000:
                mate_in = (999999 - abs(best_score) + 1) // 2
                score_str = f"M{mate_in:+d}"
            else:
                score_str = f"{best_score/100:+.2f}"
            
            print(f"D{depth:2d} | {score_str:>7} | {self.nodes_searched:>12,} nodes | "
                  f"{nps:>10,} nps | {hashfull:>3}‰ | {best_move} | {elapsed:.2f}s")
            
            # Stop if mate found
            if abs(best_score) > 900000:
                break
            
            # Time management
            if elapsed > max_time * 0.6 and depth >= 8:
                break
        
        return best_move, self.search_info
    
    def get_best_move(self, board: chess.Board, think_time: float = 5.0) -> chess.Move:
        """Get the best move using all CPU power"""
        # Check opening book first
        book_move = self.get_opening_move(board)
        if book_move and book_move in board.legal_moves:
            print(f"📚 Opening book move: {book_move}")
            self.search_info = SearchInfo(
                depth=0,
                nodes=0,
                score=0,
                time=0,
                pv=[book_move],
                nps=0,
                hashfull=0
            )
            return book_move
        
        self.searching = True
        print(f"\n{'='*80}")
        print(f"🧠 Searching with {self.num_threads} threads...")
        move, info = self.iterative_deepening(board, think_time)
        print(f"{'='*80}")
        self.searching = False
        return move


# Enhanced GUI with Bot vs Bot mode
class ChessGUI:
    """Enhanced GUI with bot vs bot mode"""
    
    def __init__(self):
        pygame.init()
        
        self.SQUARE_SIZE = 80
        self.BOARD_SIZE = self.SQUARE_SIZE * 8
        self.PANEL_WIDTH = 400
        self.WIDTH = self.BOARD_SIZE + self.PANEL_WIDTH
        self.HEIGHT = self.BOARD_SIZE + 100
        
        self.LIGHT_SQUARE = (240, 217, 181)
        self.DARK_SQUARE = (181, 136, 99)
        self.HIGHLIGHT_COLOR = (186, 202, 68, 128)
        self.SELECTED_COLOR = (246, 246, 105, 128)
        self.BG_COLOR = (49, 46, 43)
        self.TEXT_COLOR = (255, 255, 255)
        
        self.screen = pygame.display.set_mode((self.WIDTH, self.HEIGHT))
        pygame.display.set_caption("CockChess ULTRA MAX 🐓⚡ - 3500 ELO")
        self.clock = pygame.time.Clock()
        
        self.board = chess.Board()
        cpu_count = multiprocessing.cpu_count()
        self.engine = CockChessUltraMax(max_depth=20, num_threads=max(1, cpu_count - 1))
        self.selected_square = None
        self.legal_moves = []
        self.last_move = None
        self.player_color = chess.WHITE
        self.engine_thinking = False
        self.engine_thread = None
        self.game_over = False
        self.think_time = 5.0
        
        # Bot vs Bot mode
        self.bot_vs_bot = False
        self.auto_play_delay = 500  # ms delay between moves
        self.last_auto_move_time = 0
        
        self.pending_engine_move = None
        
        self.pieces = self.load_pieces()
        
        self.font_large = pygame.font.Font(None, 40)
        self.font_medium = pygame.font.Font(None, 26)
        self.font_small = pygame.font.Font(None, 20)
        self.font_tiny = pygame.font.Font(None, 16)
        
        self.move_history = []
        self.eval_history = []
        
        print(f"🎮 GUI initialized | CPU cores: {cpu_count} | Engine threads: {self.engine.num_threads}")
    
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
                    
                    print(f"✓ Pieces loaded: {font_name}")
                    return pieces
            except:
                continue
        
        print("⚠ Using fallback pieces")
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
                s.fill((255, 255, 0, 80))
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
                            pygame.draw.circle(self.screen, (80, 80, 80, 180), center, 
                                             self.SQUARE_SIZE // 3, 6)
                        else:
                            pygame.draw.circle(self.screen, (80, 80, 80, 180), center, 12)
        
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
        pygame.draw.rect(self.screen, self.BG_COLOR, (panel_x, 0, self.PANEL_WIDTH, self.HEIGHT))
        
        y = 15
        
        title = self.font_large.render("CockChess", True, (255, 215, 0))
        self.screen.blit(title, (panel_x + 15, y))
        y += 40
        
        ultra = self.font_medium.render("ULTRA MAX", True, (255, 50, 50))
        self.screen.blit(ultra, (panel_x + 90, y))
        y += 30
        
        elo = self.font_small.render("⚡ 3500 ELO MONSTER ⚡", True, (100, 255, 100))
        self.screen.blit(elo, (panel_x + 70, y))
        y += 25
        
        cpu_text = f"🔥 {self.engine.num_threads} CPU Threads"
        cpu_label = self.font_tiny.render(cpu_text, True, (255, 150, 50))
        self.screen.blit(cpu_label, (panel_x + 100, y))
        y += 30
        
        pygame.draw.line(self.screen, (100, 100, 100), (panel_x + 15, y), (panel_x + self.PANEL_WIDTH - 15, y), 2)
        y += 15
        
        # Game mode indicator
        if self.bot_vs_bot:
            mode_text = "🤖 BOT VS BOT 🤖"
            mode_color = (255, 100, 255)
        else:
            mode_text = "👤 HUMAN VS BOT"
            mode_color = (100, 200, 255)
        mode_label = self.font_medium.render(mode_text, True, mode_color)
        self.screen.blit(mode_label, (panel_x + 50, y))
        y += 35
        
        turn_text = "White to move" if self.board.turn == chess.WHITE else "Black to move"
        turn_label = self.font_small.render(turn_text, True, self.TEXT_COLOR)
        self.screen.blit(turn_label, (panel_x + 15, y))
        y += 25
        
        material = self.calculate_material()
        material_color = (100, 255, 100) if material > 0 else ((255, 100, 100) if material < 0 else self.TEXT_COLOR)
        material_text = f"Material: {material:+d}"
        material_label = self.font_small.render(material_text, True, material_color)
        self.screen.blit(material_label, (panel_x + 15, y))
        y += 25
        
        move_count = self.board.fullmove_number
        move_label = self.font_small.render(f"Move: {move_count}", True, self.TEXT_COLOR)
        self.screen.blit(move_label, (panel_x + 15, y))
        y += 30
        
        if self.engine_thinking:
            status = self.font_small.render("🧠 Thinking...", True, (255, 255, 0))
            self.screen.blit(status, (panel_x + 15, y))
            
            dots = "." * ((pygame.time.get_ticks() // 300) % 4)
            dots_label = self.font_medium.render(dots, True, (255, 255, 0))
            self.screen.blit(dots_label, (panel_x + 150, y - 2))
        y += 30
        
        if self.engine.search_info:
            info = self.engine.search_info
            
            pygame.draw.rect(self.screen, (60, 60, 60), (panel_x + 15, y, self.PANEL_WIDTH - 30, 140), border_radius=5)
            y += 10
            
            depth_text = f"Depth: {info.depth}"
            nodes_text = f"Nodes: {info.nodes:,}"
            nps_text = f"Speed: {info.nps/1000000:.1f}M nps"
            time_text = f"Time: {info.time:.2f}s"
            hash_text = f"Hash: {info.hashfull/10:.1f}%"
            
            score = info.score
            if abs(score) > 900000:
                mate_in = (999999 - abs(score) + 1) // 2
                score_text = f"MATE IN {mate_in}"
                score_color = (100, 255, 100) if score > 0 else (255, 100, 100)
            else:
                score_text = f"Eval: {score/100:+.2f}"
                if abs(score) < 50:
                    score_color = (200, 200, 200)
                elif score > 0:
                    score_color = (100, 255, 100)
                else:
                    score_color = (255, 100, 100)
            
            for text, color in [(depth_text, (150, 255, 255)), (nodes_text, (150, 200, 255)), 
                               (nps_text, (200, 150, 255)), (time_text, (255, 200, 150)),
                               (hash_text, (255, 255, 150)),
                               (score_text, score_color)]:
                label = self.font_tiny.render(text, True, color)
                self.screen.blit(label, (panel_x + 25, y))
                y += 22
        
        y += 15
        
        pygame.draw.line(self.screen, (100, 100, 100), (panel_x + 15, y), (panel_x + self.PANEL_WIDTH - 15, y), 2)
        y += 10
        
        history_title = self.font_medium.render("Move History", True, (200, 200, 200))
        self.screen.blit(history_title, (panel_x + 15, y))
        y += 30
        
        for i in range(max(0, len(self.move_history) - 8), len(self.move_history), 2):
            move_num = (i // 2) + 1
            white_move = self.move_history[i] if i < len(self.move_history) else ""
            black_move = self.move_history[i + 1] if i + 1 < len(self.move_history) else ""
            
            move_text = f"{move_num}. {white_move:6} {black_move}"
            move_label = self.font_tiny.render(move_text, True, self.TEXT_COLOR)
            self.screen.blit(move_label, (panel_x + 20, y))
            y += 18
        
        # Buttons
        y = self.HEIGHT - 245
        
        # Bot vs Bot toggle
        bot_vs_bot_rect = pygame.Rect(panel_x + 15, y, self.PANEL_WIDTH - 30, 35)
        bot_color = (150, 0, 150) if self.bot_vs_bot else (80, 80, 80)
        pygame.draw.rect(self.screen, bot_color, bot_vs_bot_rect, border_radius=5)
        pygame.draw.rect(self.screen, (255, 255, 255), bot_vs_bot_rect, 2, border_radius=5)
        bot_text = self.font_medium.render("🤖 Bot vs Bot Mode", True, self.TEXT_COLOR)
        text_rect = bot_text.get_rect(center=bot_vs_bot_rect.center)
        self.screen.blit(bot_text, text_rect)
        
        y += 45
        
        time_label = self.font_small.render("Engine Time:", True, self.TEXT_COLOR)
        self.screen.blit(time_label, (panel_x + 15, y))
        y += 25
        
        # Time controls
        time_options_row1 = [(1, "1s"), (3, "3s"), (5, "5s"), (10, "10s")]
        button_width = 75
        for i, (time_val, label) in enumerate(time_options_row1):
            x_pos = panel_x + 15 + i * (button_width + 5)
            color = (0, 150, 0) if self.think_time == time_val else (100, 100, 100)
            button_rect = pygame.Rect(x_pos, y, button_width, 30)
            pygame.draw.rect(self.screen, color, button_rect, border_radius=3)
            pygame.draw.rect(self.screen, (200, 200, 200), button_rect, 2, border_radius=3)
            
            text = self.font_tiny.render(label, True, self.TEXT_COLOR)
            text_rect = text.get_rect(center=button_rect.center)
            self.screen.blit(text, text_rect)
        
        y += 35
        
        time_options_row2 = [(20, "20s"), (30, "30s"), (60, "60s")]
        for i, (time_val, label) in enumerate(time_options_row2):
            x_pos = panel_x + 15 + i * (button_width + 5)
            color = (0, 150, 0) if self.think_time == time_val else (100, 100, 100)
            button_rect = pygame.Rect(x_pos, y, button_width, 30)
            pygame.draw.rect(self.screen, color, button_rect, border_radius=3)
            pygame.draw.rect(self.screen, (200, 200, 200), button_rect, 2, border_radius=3)
            
            text = self.font_tiny.render(label, True, self.TEXT_COLOR)
            text_rect = text.get_rect(center=button_rect.center)
            self.screen.blit(text, text_rect)
        
        y += 40
        
        # Undo button (disabled in bot vs bot)
        undo_enabled = len(self.move_history) >= 2 and not self.engine_thinking and not self.game_over and not self.bot_vs_bot
        undo_rect = pygame.Rect(panel_x + 15, y, self.PANEL_WIDTH - 30, 35)
        undo_color = (150, 100, 0) if undo_enabled else (80, 80, 80)
        pygame.draw.rect(self.screen, undo_color, undo_rect, border_radius=5)
        pygame.draw.rect(self.screen, (255, 255, 255) if undo_enabled else (120, 120, 120), undo_rect, 2, border_radius=5)
        undo_text = self.font_medium.render("↶ Undo Move", True, self.TEXT_COLOR if undo_enabled else (150, 150, 150))
        text_rect = undo_text.get_rect(center=undo_rect.center)
        self.screen.blit(undo_text, text_rect)
        
        y += 45
        
        # New Game and Flip Board
        new_game_rect = pygame.Rect(panel_x + 15, y, (self.PANEL_WIDTH - 35) // 2, 35)
        pygame.draw.rect(self.screen, (0, 150, 0), new_game_rect, border_radius=5)
        pygame.draw.rect(self.screen, (255, 255, 255), new_game_rect, 2, border_radius=5)
        new_game_text = self.font_small.render("New Game", True, self.TEXT_COLOR)
        text_rect = new_game_text.get_rect(center=new_game_rect.center)
        self.screen.blit(new_game_text, text_rect)
        
        flip_rect = pygame.Rect(panel_x + 25 + (self.PANEL_WIDTH - 35) // 2, y, (self.PANEL_WIDTH - 35) // 2, 35)
        pygame.draw.rect(self.screen, (0, 100, 200), flip_rect, border_radius=5)
        pygame.draw.rect(self.screen, (255, 255, 255), flip_rect, 2, border_radius=5)
        flip_text = self.font_small.render("Flip Board", True, self.TEXT_COLOR)
        text_rect = flip_text.get_rect(center=flip_rect.center)
        self.screen.blit(flip_text, text_rect)
    
    def calculate_material(self) -> int:
        material = 0
        for square in chess.SQUARES:
            piece = self.board.piece_at(square)
            if piece:
                value = self.engine.PIECE_VALUES.get(piece.piece_type, 0)
                if piece.color == chess.WHITE:
                    material += value
                else:
                    material -= value
        return material // 100
    
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
        
        if self.engine.search_info:
            self.eval_history.append(self.engine.search_info.score)
        
        if self.board.is_game_over():
            self.game_over = True
            result = self.board.result()
            print(f"\n{'='*80}")
            print(f"🏆 GAME OVER! Result: {result}")
            print(f"{'='*80}\n")
            self.bot_vs_bot = False  # Stop auto-play
        else:
            if self.bot_vs_bot or self.board.turn != self.player_color:
                self.start_engine_move()
    
    def start_engine_move(self):
        if not self.engine_thinking:
            self.engine_thinking = True
            self.engine_thread = threading.Thread(target=self.engine_move_thread)
            self.engine_thread.daemon = True
            self.engine_thread.start()
    
    def engine_move_thread(self):
        try:
            move = self.engine.get_best_move(self.board, think_time=self.think_time)
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
        
        self.engine.tt.clear()
        self.engine.history_heuristic.clear()
        self.engine.killer_moves = [[None, None] for _ in range(200)]
        self.engine.tt_age = 0
        
        print(f"\n{'='*80}")
        print("🎮 NEW GAME STARTED")
        print(f"{'='*80}\n")
        
        # If bot vs bot, start immediately
        if self.bot_vs_bot:
            self.start_engine_move()
    
    def toggle_bot_vs_bot(self):
        if not self.engine_thinking:
            self.bot_vs_bot = not self.bot_vs_bot
            mode = "BOT VS BOT" if self.bot_vs_bot else "HUMAN VS BOT"
            print(f"\n🎮 Mode changed to: {mode}")
            
            if self.bot_vs_bot and not self.game_over:
                self.start_engine_move()
    
    def flip_board(self):
        self.player_color = not self.player_color
    
    def run(self):
        running = True
        
        while running:
            current_time = pygame.time.get_ticks()
            
            # Apply pending engine move
            if self.pending_engine_move and not self.engine_thinking:
                if not self.bot_vs_bot or (current_time - self.last_auto_move_time > self.auto_play_delay):
                    pygame.time.wait(100)
                    self.make_move(self.pending_engine_move)
                    self.pending_engine_move = None
                    self.last_auto_move_time = current_time
            
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    running = False
                
                elif event.type == pygame.MOUSEBUTTONDOWN:
                    pos = pygame.mouse.get_pos()
                    panel_x = self.BOARD_SIZE
                    
                    if pos[0] < self.BOARD_SIZE and pos[1] < self.BOARD_SIZE:
                        square = self.coords_to_square(pos)
                        if square is not None:
                            self.handle_square_click(square)
                    
                    elif pos[0] >= panel_x:
                        # Bot vs Bot toggle
                        if self.HEIGHT - 245 <= pos[1] <= self.HEIGHT - 210:
                            self.toggle_bot_vs_bot()
                        
                        # Time controls row 1
                        elif self.HEIGHT - 200 + 25 <= pos[1] <= self.HEIGHT - 200 + 55:
                            time_options = [1, 3, 5, 10]
                            button_width = 75
                            for i, time_val in enumerate(time_options):
                                x_pos = panel_x + 15 + i * (button_width + 5)
                                if x_pos <= pos[0] <= x_pos + button_width:
                                    self.think_time = time_val
                                    print(f"⏱ Think time: {time_val}s")
                        
                        # Time controls row 2
                        elif self.HEIGHT - 200 + 60 <= pos[1] <= self.HEIGHT - 200 + 90:
                            time_options = [20, 30, 60]
                            button_width = 75
                            for i, time_val in enumerate(time_options):
                                x_pos = panel_x + 15 + i * (button_width + 5)
                                if x_pos <= pos[0] <= x_pos + button_width:
                                    self.think_time = time_val
                                    print(f"⏱ Think time: {time_val}s")
                        
                        # Undo button
                        elif self.HEIGHT - 105 <= pos[1] <= self.HEIGHT - 70:
                            self.undo_move()
                        
                        # New Game / Flip Board
                        elif self.HEIGHT - 60 <= pos[1] <= self.HEIGHT - 25:
                            if panel_x + 15 <= pos[0] <= panel_x + 15 + (self.PANEL_WIDTH - 35) // 2:
                                self.new_game()
                            elif panel_x + 25 + (self.PANEL_WIDTH - 35) // 2 <= pos[0] <= panel_x + self.PANEL_WIDTH - 15:
                                self.flip_board()
            
            self.screen.fill(self.BG_COLOR)
            self.draw_board()
            self.draw_pieces()
            self.draw_panel()
            
            pygame.display.flip()
            self.clock.tick(60)
        
        self.engine.stop_search = True
        if self.engine_thread and self.engine_thread.is_alive():
            self.engine_thread.join(timeout=2.0)
        
        pygame.quit()
        sys.exit()


if __name__ == "__main__":
    print("="*80)
    print("   🐓⚡ COCKCHESS ULTRA MAX - SUPREME CHESS DOMINATION ⚡🐓")
    print("="*80)
    print("\n📊 Target Rating: 3500 ELO")
    print(f"💻 CPU Cores: {multiprocessing.cpu_count()}")
    print(f"🔥 Engine Threads: {max(1, multiprocessing.cpu_count() - 1)}")
    print("\n🆕 New Features:")
    print("   ✓ Multi-threaded parallel search")
    print("   ✓ 🤖 BOT VS BOT MODE - Watch the engine play itself!")
    print("   ✓ Ultra-deep search (20+ ply)")
    print("   ✓ Advanced evaluation with 25+ features")
    print("   ✓ 100M entry transposition table")
    print("   ✓ Aggressive pruning & extensions")
    print("   ✓ Full CPU utilization")
    print("\n🔥 Advanced Features:")
    print("   ✓ Principal Variation Search")
    print("   ✓ Lazy SMP parallel search")
    print("   ✓ Aspiration windows")
    print("   ✓ Late Move Reductions (LMR)")
    print("   ✓ Null move pruning")
    print("   ✓ Futility & Razoring")
    print("   ✓ Advanced pawn structure analysis")
    print("   ✓ King safety evaluation")
    print("   ✓ Mobility & center control")
    print("\n📦 Initializing...")
    
    try:
        gui = ChessGUI()
        print("✅ GUI loaded successfully!")
        print("\n🎮 Controls:")
        print("   • Click 'Bot vs Bot Mode' to watch the engine play itself")
        print("   • Adjust think time (1s-60s)")
        print("   • Click pieces to make your moves (in human mode)")
        print("   • Undo / New Game / Flip Board")
        print("\n🚀 Starting game...\n")
        
        gui.run()
    except Exception as e:
        print(f"\n❌ Error: {e}")
        import traceback
        traceback.print_exc()
