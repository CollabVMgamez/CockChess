# cockchess.py
import chess
import chess.polyglot
import pygame
import sys
import threading
from typing import Optional, Tuple, List, Dict
import time
from dataclasses import dataclass
import random

@dataclass
class SearchInfo:
    depth: int
    nodes: int
    score: int
    time: float
    pv: List[chess.Move]
    nps: int

class TranspositionEntry:
    def __init__(self, depth: int, score: int, flag: str, best_move: chess.Move = None):
        self.depth = depth
        self.score = score
        self.flag = flag
        self.best_move = best_move

class CockChessUltra:
    """Ultra-strong chess engine targeting 2500-3000 ELO"""
    
    def __init__(self, max_depth: int = 12):
        self.max_depth = max_depth
        self.nodes_searched = 0
        self.tt = {}
        self.killer_moves = [[None, None] for _ in range(100)]
        self.history_heuristic = {}
        self.counter_moves = {}
        self.search_info = None
        self.searching = False
        self.stop_search = False
        self.pv_table = {}
        
        self.PIECE_VALUES = {
            chess.PAWN: 100,
            chess.KNIGHT: 320,
            chess.BISHOP: 330,
            chess.ROOK: 500,
            chess.QUEEN: 900,
            chess.KING: 20000
        }
        
        self.BISHOP_PAIR_BONUS = 50
        self.ROOK_OPEN_FILE_BONUS = 25
        self.ROOK_SEMI_OPEN_FILE_BONUS = 15
        self.DOUBLED_PAWN_PENALTY = 15
        self.ISOLATED_PAWN_PENALTY = 20
        self.PASSED_PAWN_BONUS = [0, 10, 20, 35, 60, 100, 160, 0]
        self.MOBILITY_WEIGHT = 5
        self.KING_SAFETY_WEIGHT = 15
        
        self.pst = self._initialize_advanced_pst()
        self.opening_book = self._load_opening_book()
        
    def _initialize_advanced_pst(self) -> Dict:
        pst = {}
        
        pst[chess.PAWN] = [
              0,   0,   0,   0,   0,   0,   0,   0,
             50,  50,  50,  50,  50,  50,  50,  50,
             10,  10,  20,  30,  30,  20,  10,  10,
              5,   5,  10,  27,  27,  10,   5,   5,
              0,   0,   0,  25,  25,   0,   0,   0,
              5,  -5, -10,   0,   0, -10,  -5,   5,
              5,  10,  10, -25, -25,  10,  10,   5,
              0,   0,   0,   0,   0,   0,   0,   0
        ]
        
        pst[chess.KNIGHT] = [
            -50, -40, -30, -30, -30, -30, -40, -50,
            -40, -20,   0,   5,   5,   0, -20, -40,
            -30,   5,  10,  15,  15,  10,   5, -30,
            -30,   0,  15,  20,  20,  15,   0, -30,
            -30,   5,  15,  20,  20,  15,   5, -30,
            -30,   0,  10,  15,  15,  10,   0, -30,
            -40, -20,   0,   0,   0,   0, -20, -40,
            -50, -40, -30, -30, -30, -30, -40, -50
        ]
        
        pst[chess.BISHOP] = [
            -20, -10, -10, -10, -10, -10, -10, -20,
            -10,   5,   0,   0,   0,   0,   5, -10,
            -10,  10,  10,  10,  10,  10,  10, -10,
            -10,   0,  10,  10,  10,  10,   0, -10,
            -10,   5,   5,  10,  10,   5,   5, -10,
            -10,   0,   5,  10,  10,   5,   0, -10,
            -10,   0,   0,   0,   0,   0,   0, -10,
            -20, -10, -10, -10, -10, -10, -10, -20
        ]
        
        pst[chess.ROOK] = [
              0,   0,   0,   5,   5,   0,   0,   0,
             -5,   0,   0,   0,   0,   0,   0,  -5,
             -5,   0,   0,   0,   0,   0,   0,  -5,
             -5,   0,   0,   0,   0,   0,   0,  -5,
             -5,   0,   0,   0,   0,   0,   0,  -5,
             -5,   0,   0,   0,   0,   0,   0,  -5,
              5,  10,  10,  10,  10,  10,  10,   5,
              0,   0,   0,   0,   0,   0,   0,   0
        ]
        
        pst[chess.QUEEN] = [
            -20, -10, -10,  -5,  -5, -10, -10, -20,
            -10,   0,   5,   0,   0,   0,   0, -10,
            -10,   5,   5,   5,   5,   5,   0, -10,
              0,   0,   5,   5,   5,   5,   0,  -5,
             -5,   0,   5,   5,   5,   5,   0,  -5,
            -10,   0,   5,   5,   5,   5,   0, -10,
            -10,   0,   0,   0,   0,   0,   0, -10,
            -20, -10, -10,  -5,  -5, -10, -10, -20
        ]
        
        pst[chess.KING] = [
             20,  30,  10,   0,   0,  10,  30,  20,
             20,  20,   0,   0,   0,   0,  20,  20,
            -10, -20, -20, -20, -20, -20, -20, -10,
            -20, -30, -30, -40, -40, -30, -30, -20,
            -30, -40, -40, -50, -50, -40, -40, -30,
            -30, -40, -40, -50, -50, -40, -40, -30,
            -30, -40, -40, -50, -50, -40, -40, -30,
            -30, -40, -40, -50, -50, -40, -40, -30
        ]
        
        pst['KING_ENDGAME'] = [
            -50, -30, -30, -30, -30, -30, -30, -50,
            -30, -30,   0,   0,   0,   0, -30, -30,
            -30, -10,  20,  30,  30,  20, -10, -30,
            -30, -10,  30,  40,  40,  30, -10, -30,
            -30, -10,  30,  40,  40,  30, -10, -30,
            -30, -10,  20,  30,  30,  20, -10, -30,
            -30, -20, -10,   0,   0, -10, -20, -30,
            -50, -40, -30, -20, -20, -30, -40, -50
        ]
        
        return pst
    
    def _load_opening_book(self) -> Dict:
        book = {
            chess.Board().fen(): ['e2e4', 'd2d4', 'g1f3', 'c2c4'],
            'rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1': 
                ['e7e5', 'c7c5', 'e7e6', 'c7c6'],
            'rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR w KQkq e6 0 2':
                ['g1f3', 'f2f4', 'b1c3'],
            'rnbqkbnr/pppp1ppp/8/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R b KQkq - 1 2':
                ['b8c6', 'g8f6'],
            'rnbqkbnr/pppppppp/8/8/3P4/8/PPP1PPPP/RNBQKBNR b KQkq d3 0 1':
                ['d7d5', 'g8f6', 'e7e6'],
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
        
        max_material = (4 * 320 + 4 * 330 + 4 * 500 + 2 * 900)
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
                if color == chess.WHITE:
                    score += self.PASSED_PAWN_BONUS[rank]
                else:
                    score += self.PASSED_PAWN_BONUS[7 - rank]
        
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
            
            for sq in shield_squares:
                piece = board.piece_at(sq)
                if piece and piece.piece_type == chess.PAWN and piece.color == color:
                    score += 10
        
        elif color == chess.BLACK and king_rank > 5:
            shield_squares = [
                chess.square(f, r)
                for f in [king_file - 1, king_file, king_file + 1]
                for r in [king_rank - 1, king_rank - 2]
                if 0 <= f < 8 and 0 <= r < 8
            ]
            
            for sq in shield_squares:
                piece = board.piece_at(sq)
                if piece and piece.piece_type == chess.PAWN and piece.color == color:
                    score += 10
        
        king_zone = [
            chess.square(f, r)
            for f in range(max(0, king_file - 1), min(8, king_file + 2))
            for r in range(max(0, king_rank - 1), min(8, king_rank + 2))
        ]
        
        attackers = 0
        for sq in king_zone:
            if board.is_attacked_by(not color, sq):
                attackers += 1
        
        score -= attackers * 15
        
        return score
    
    def evaluate_board(self, board: chess.Board) -> int:
        if board.is_checkmate():
            return -999999 if board.turn else 999999
        
        if board.is_stalemate() or board.is_insufficient_material():
            return 0
        
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
                if piece.piece_type == chess.KING and phase < 0.5:
                    table = self.pst['KING_ENDGAME']
                else:
                    table = self.pst[piece.piece_type]
                
                table_value = table[square if piece.color == chess.WHITE else chess.square_mirror(square)]
                if piece.piece_type == chess.KING:
                    mg_value = self.pst[chess.KING][square if piece.color == chess.WHITE else chess.square_mirror(square)]
                    eg_value = self.pst['KING_ENDGAME'][square if piece.color == chess.WHITE else chess.square_mirror(square)]
                    table_value = int(mg_value * phase + eg_value * (1 - phase))
                
                value += table_value
            
            if piece.color == chess.WHITE:
                score += value
            else:
                score -= value
        
        if len(board.pieces(chess.BISHOP, chess.WHITE)) >= 2:
            score += self.BISHOP_PAIR_BONUS
        if len(board.pieces(chess.BISHOP, chess.BLACK)) >= 2:
            score -= self.BISHOP_PAIR_BONUS
        
        for color in [chess.WHITE, chess.BLACK]:
            for rook_sq in board.pieces(chess.ROOK, color):
                file = chess.square_file(rook_sq)
                
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
        
        if phase > 0.3:
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
        score += 10 if board.turn == chess.WHITE else -10
        
        return score if board.turn == chess.WHITE else -score
    
    def quiescence_search(self, board: chess.Board, alpha: int, beta: int, depth: int = 0) -> int:
        self.nodes_searched += 1
        
        if depth > 20 or self.stop_search:
            return self.evaluate_board(board)
        
        stand_pat = self.evaluate_board(board)
        
        if stand_pat >= beta:
            return beta
        
        BIG_DELTA = 900
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
                score += 100000
            elif board.is_capture(move):
                victim = board.piece_at(move.to_square)
                attacker = board.piece_at(move.from_square)
                if victim and attacker:
                    score += 10000 + self.PIECE_VALUES[victim.piece_type] - self.PIECE_VALUES[attacker.piece_type] // 10
            elif move.promotion:
                score += 9000 + self.PIECE_VALUES[move.promotion]
            elif self.killer_moves[ply][0] == move:
                score += 8000
            elif self.killer_moves[ply][1] == move:
                score += 7000
            else:
                move_key = (move.from_square, move.to_square)
                if move_key in self.counter_moves:
                    score += 6000
            
            move_key = (move.from_square, move.to_square)
            if move_key in self.history_heuristic:
                score += min(5000, self.history_heuristic[move_key])
            
            board.push(move)
            if board.is_check():
                score += 4000
            board.pop()
            
            if board.is_castling(move):
                score += 3000
            
            move_scores.append((score, move))
        
        move_scores.sort(reverse=True, key=lambda x: x[0])
        return [move for _, move in move_scores]
    
    def pvs_search(self, board: chess.Board, depth: int, alpha: int, beta: int, 
                   ply: int, allow_null: bool = True) -> int:
        self.nodes_searched += 1
        pv_node = (beta - alpha) > 1
        
        if self.stop_search:
            return 0
        
        if board.is_repetition(2) or board.can_claim_fifty_moves():
            return 0
        
        alpha_orig = alpha
        alpha = max(alpha, -999999 + ply)
        beta = min(beta, 999999 - ply - 1)
        if alpha >= beta:
            return alpha
        
        board_hash = chess.polyglot.zobrist_hash(board)
        tt_entry = self.tt.get(board_hash)
        hash_move = None
        
        if tt_entry and tt_entry.depth >= depth:
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
                score = -self.pvs_search(board, depth - 1 - R, -beta, -beta + 1, ply + 1, False)
                board.pop()
                
                if score >= beta:
                    return beta
        
        if depth <= 3 and not in_check and not pv_node:
            eval_score = self.evaluate_board(board)
            if eval_score + 300 * depth < alpha:
                q_score = self.quiescence_search(board, alpha, beta)
                if q_score < alpha:
                    return q_score
        
        futility_margin = [0, 200, 300, 500]
        if depth <= 3 and not in_check and not pv_node:
            eval_score = self.evaluate_board(board)
            if eval_score + futility_margin[depth] <= alpha:
                return self.quiescence_search(board, alpha, beta)
        
        legal_moves = list(board.legal_moves)
        if not legal_moves:
            return self.evaluate_board(board)
        
        legal_moves = self.order_moves(board, legal_moves, ply, hash_move)
        
        best_score = float('-inf')
        best_move = None
        moves_searched = 0
        
        for i, move in enumerate(legal_moves):
            board.push(move)
            
            extension = 1 if board.is_check() else 0
            new_depth = depth - 1 + extension
            
            if moves_searched == 0:
                score = -self.pvs_search(board, new_depth, -beta, -alpha, ply + 1)
            else:
                do_lmr = (
                    moves_searched >= 4 and
                    depth >= 3 and
                    not in_check and
                    not board.is_check() and
                    not board.is_capture(move) and
                    not move.promotion
                )
                
                if do_lmr:
                    reduction = 1
                    if moves_searched >= 8:
                        reduction = 2
                    if depth > 6 and moves_searched >= 12:
                        reduction = 3
                    
                    score = -self.pvs_search(board, new_depth - reduction, -alpha - 1, -alpha, ply + 1)
                    
                    if score > alpha:
                        score = -self.pvs_search(board, new_depth, -alpha - 1, -alpha, ply + 1)
                else:
                    score = -self.pvs_search(board, new_depth, -alpha - 1, -alpha, ply + 1)
                
                if alpha < score < beta:
                    score = -self.pvs_search(board, new_depth, -beta, -alpha, ply + 1)
            
            board.pop()
            moves_searched += 1
            
            if score > best_score:
                best_score = score
                best_move = move
            
            if score > alpha:
                alpha = score
            
            if alpha >= beta:
                if not board.is_capture(move):
                    if self.killer_moves[ply][0] != move:
                        self.killer_moves[ply][1] = self.killer_moves[ply][0]
                        self.killer_moves[ply][0] = move
                    
                    move_key = (move.from_square, move.to_square)
                    bonus = depth * depth
                    self.history_heuristic[move_key] = self.history_heuristic.get(move_key, 0) + bonus
                    
                    if self.history_heuristic[move_key] > 10000:
                        for key in self.history_heuristic:
                            self.history_heuristic[key] //= 2
                
                break
        
        if best_score <= alpha_orig:
            flag = 'UPPERBOUND'
        elif best_score >= beta:
            flag = 'LOWERBOUND'
        else:
            flag = 'EXACT'
        
        self.tt[board_hash] = TranspositionEntry(depth, best_score, flag, best_move)
        
        if len(self.tt) > 10000000:
            keys_to_remove = list(self.tt.keys())[:len(self.tt) // 2]
            for key in keys_to_remove:
                del self.tt[key]
        
        return best_score
    
    def iterative_deepening(self, board: chess.Board, max_time: float = 10.0) -> Tuple[chess.Move, SearchInfo]:
        self.stop_search = False
        start_time = time.time()
        best_move = None
        best_score = 0
        
        for depth in range(1, self.max_depth + 1):
            if time.time() - start_time > max_time * 0.95:
                break
            
            self.nodes_searched = 0
            
            if depth >= 5:
                window = 50
                alpha = best_score - window
                beta = best_score + window
                aspiration_search = True
            else:
                alpha = float('-inf')
                beta = float('inf')
                aspiration_search = False
            
            while True:
                current_best = None
                current_score = float('-inf')
                
                legal_moves = list(board.legal_moves)
                
                if best_move and best_move in legal_moves:
                    legal_moves.remove(best_move)
                    legal_moves.insert(0, best_move)
                else:
                    legal_moves = self.order_moves(board, legal_moves, 0)
                
                for move in legal_moves:
                    if self.stop_search or time.time() - start_time > max_time:
                        break
                    
                    board.push(move)
                    score = -self.pvs_search(board, depth - 1, -beta, -alpha, 1)
                    board.pop()
                    
                    if score > current_score:
                        current_score = score
                        current_best = move
                    
                    if score > alpha:
                        alpha = score
                
                if aspiration_search:
                    if current_score <= alpha - window:
                        alpha = float('-inf')
                        continue
                    elif current_score >= beta:
                        beta = float('inf')
                        continue
                
                break
            
            if current_best:
                best_move = current_best
                best_score = current_score
            
            elapsed = time.time() - start_time
            nps = int(self.nodes_searched / max(elapsed, 0.001))
            
            self.search_info = SearchInfo(
                depth=depth,
                nodes=self.nodes_searched,
                score=best_score,
                time=elapsed,
                pv=[best_move] if best_move else [],
                nps=nps
            )
            
            score_display = best_score
            if abs(best_score) > 900000:
                mate_in = (999999 - abs(best_score) + 1) // 2
                score_str = f"Mate in {mate_in}"
            else:
                score_str = f"{best_score/100:+.2f}"
            
            print(f"Depth {depth:2d} | {score_str:>10} | {self.nodes_searched:>10,} nodes | "
                  f"{nps:>10,} nps | {best_move} | Time: {elapsed:.2f}s")
            
            if abs(best_score) > 900000:
                break
            
            if elapsed > max_time * 0.7 and depth >= 6:
                break
        
        return best_move, self.search_info
    
    def get_best_move(self, board: chess.Board, think_time: float = 5.0) -> chess.Move:
        book_move = self.get_opening_move(board)
        if book_move and book_move in board.legal_moves:
            print(f"📚 Book move: {book_move}")
            self.search_info = SearchInfo(
                depth=0,
                nodes=0,
                score=0,
                time=0,
                pv=[book_move],
                nps=0
            )
            return book_move
        
        self.searching = True
        move, info = self.iterative_deepening(board, think_time)
        self.searching = False
        return move


class ChessGUI:
    """Enhanced GUI with undo functionality"""
    
    def __init__(self):
        pygame.init()
        
        self.SQUARE_SIZE = 80
        self.BOARD_SIZE = self.SQUARE_SIZE * 8
        self.PANEL_WIDTH = 350
        self.WIDTH = self.BOARD_SIZE + self.PANEL_WIDTH
        self.HEIGHT = self.BOARD_SIZE + 100
        
        self.LIGHT_SQUARE = (240, 217, 181)
        self.DARK_SQUARE = (181, 136, 99)
        self.HIGHLIGHT_COLOR = (186, 202, 68, 128)
        self.SELECTED_COLOR = (246, 246, 105, 128)
        self.BG_COLOR = (49, 46, 43)
        self.TEXT_COLOR = (255, 255, 255)
        
        self.screen = pygame.display.set_mode((self.WIDTH, self.HEIGHT))
        pygame.display.set_caption("CockChess Ultra 🐓⚡ - 2500-3000 ELO")
        self.clock = pygame.time.Clock()
        
        self.board = chess.Board()
        self.engine = CockChessUltra(max_depth=12)
        self.selected_square = None
        self.legal_moves = []
        self.last_move = None
        self.player_color = chess.WHITE
        self.engine_thinking = False
        self.engine_thread = None
        self.game_over = False
        self.think_time = 5.0
        
        # For preventing board changes during thinking
        self.pending_engine_move = None
        
        self.pieces = self.load_pieces()
        
        self.font_large = pygame.font.Font(None, 40)
        self.font_medium = pygame.font.Font(None, 26)
        self.font_small = pygame.font.Font(None, 20)
        self.font_tiny = pygame.font.Font(None, 16)
        
        self.move_history = []
        self.eval_history = []
    
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
                    
                    print(f"✓ Chess pieces loaded using: {font_name}")
                    return pieces
            except:
                continue
        
        print("⚠ Using fallback geometric pieces")
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
            
            if self.selected_square == square:
                s = pygame.Surface((self.SQUARE_SIZE, self.SQUARE_SIZE), pygame.SRCALPHA)
                s.fill(self.SELECTED_COLOR)
                self.screen.blit(s, (x, y))
            
            if self.selected_square is not None:
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
        
        ultra = self.font_medium.render("ULTRA EDITION", True, (255, 100, 100))
        self.screen.blit(ultra, (panel_x + 50, y))
        y += 30
        
        elo = self.font_small.render("⚡ 2500-3000 ELO ⚡", True, (100, 200, 255))
        self.screen.blit(elo, (panel_x + 70, y))
        y += 35
        
        pygame.draw.line(self.screen, (100, 100, 100), (panel_x + 15, y), (panel_x + self.PANEL_WIDTH - 15, y), 2)
        y += 15
        
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
            status = self.font_small.render("🧠 Engine thinking...", True, (255, 255, 0))
            self.screen.blit(status, (panel_x + 15, y))
            
            dots = "." * ((pygame.time.get_ticks() // 500) % 4)
            dots_label = self.font_medium.render(dots, True, (255, 255, 0))
            self.screen.blit(dots_label, (panel_x + 200, y - 2))
        y += 30
        
        if self.engine.search_info:
            info = self.engine.search_info
            
            pygame.draw.rect(self.screen, (60, 60, 60), (panel_x + 15, y, self.PANEL_WIDTH - 30, 120), border_radius=5)
            y += 10
            
            depth_text = f"Depth: {info.depth}"
            nodes_text = f"Nodes: {info.nodes:,}"
            nps_text = f"Speed: {info.nps/1000:.0f}k nps"
            time_text = f"Time: {info.time:.2f}s"
            
            score = info.score
            if abs(score) > 900000:
                mate_in = (999999 - abs(score) + 1) // 2
                score_text = f"Mate in {mate_in}"
                score_color = (100, 255, 100) if score > 0 else (255, 100, 100)
            else:
                score_text = f"Eval: {score/100:+.2f}"
                if abs(score) < 50:
                    score_color = (200, 200, 200)
                elif score > 0:
                    score_color = (100, 255, 100)
                else:
                    score_color = (255, 100, 100)
            
            for text, color in [(depth_text, self.TEXT_COLOR), (nodes_text, (150, 200, 255)), 
                               (nps_text, (200, 150, 255)), (time_text, (255, 200, 150)),
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
        
        for i in range(max(0, len(self.move_history) - 10), len(self.move_history), 2):
            move_num = (i // 2) + 1
            white_move = self.move_history[i] if i < len(self.move_history) else ""
            black_move = self.move_history[i + 1] if i + 1 < len(self.move_history) else ""
            
            move_text = f"{move_num}. {white_move:6} {black_move}"
            move_label = self.font_tiny.render(move_text, True, self.TEXT_COLOR)
            self.screen.blit(move_label, (panel_x + 20, y))
            y += 18
        
        # Buttons
        y = self.HEIGHT - 210
        
        time_label = self.font_small.render("Engine Time:", True, self.TEXT_COLOR)
        self.screen.blit(time_label, (panel_x + 15, y))
        y += 25
        
        # First row: 1s, 3s, 5s, 10s
        time_options_row1 = [(1, "1s"), (3, "3s"), (5, "5s"), (10, "10s")]
        button_width = 65
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
        
        # Second row: 20s, 30s, 60s
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
        
        # Undo button
        undo_enabled = len(self.move_history) >= 2 and not self.engine_thinking and not self.game_over
        undo_rect = pygame.Rect(panel_x + 15, y, self.PANEL_WIDTH - 30, 35)
        undo_color = (150, 100, 0) if undo_enabled else (80, 80, 80)
        pygame.draw.rect(self.screen, undo_color, undo_rect, border_radius=5)
        pygame.draw.rect(self.screen, (255, 255, 255) if undo_enabled else (120, 120, 120), undo_rect, 2, border_radius=5)
        undo_text = self.font_medium.render("↶ Undo Move", True, self.TEXT_COLOR if undo_enabled else (150, 150, 150))
        text_rect = undo_text.get_rect(center=undo_rect.center)
        self.screen.blit(undo_text, text_rect)
        
        y += 45
        
        # New Game button
        new_game_rect = pygame.Rect(panel_x + 15, y, (self.PANEL_WIDTH - 35) // 2, 35)
        pygame.draw.rect(self.screen, (0, 150, 0), new_game_rect, border_radius=5)
        pygame.draw.rect(self.screen, (255, 255, 255), new_game_rect, 2, border_radius=5)
        new_game_text = self.font_small.render("New Game", True, self.TEXT_COLOR)
        text_rect = new_game_text.get_rect(center=new_game_rect.center)
        self.screen.blit(new_game_text, text_rect)
        
        # Flip Board button
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
        if self.engine_thinking or self.game_over:
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
            print(f"\n{'='*60}")
            print(f"GAME OVER! Result: {result}")
            print(f"{'='*60}\n")
        else:
            if self.board.turn != self.player_color:
                self.start_engine_move()
    
    def start_engine_move(self):
        self.engine_thinking = True
        self.engine_thread = threading.Thread(target=self.engine_move_thread)
        self.engine_thread.daemon = True
        self.engine_thread.start()
    
    def engine_move_thread(self):
        try:
            move = self.engine.get_best_move(self.board, think_time=self.think_time)
            if move:
                # Store the move to be applied in the main thread
                self.pending_engine_move = move
        except Exception as e:
            print(f"Engine error: {e}")
        finally:
            self.engine_thinking = False
    
    def undo_move(self):
        """Undo the last two moves (player + engine)"""
        if len(self.move_history) >= 2 and not self.engine_thinking and not self.game_over:
            # Undo twice (engine move and player move)
            for _ in range(2):
                if len(self.board.move_stack) > 0:
                    self.board.pop()
                    self.move_history.pop()
                    if self.eval_history:
                        self.eval_history.pop()
            
            # Update last move
            if len(self.board.move_stack) > 0:
                self.last_move = self.board.peek()
            else:
                self.last_move = None
            
            self.selected_square = None
            self.legal_moves = []
            self.game_over = False
            
            print("↶ Undid last move")
    
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
        self.engine.killer_moves = [[None, None] for _ in range(100)]
        
        print("\n" + "="*60)
        print("NEW GAME STARTED")
        print("="*60 + "\n")
    
    def flip_board(self):
        self.player_color = not self.player_color
    
    def run(self):
        running = True
        
        while running:
            # Apply pending engine move (only when not thinking)
            if self.pending_engine_move and not self.engine_thinking:
                pygame.time.wait(100)
                self.make_move(self.pending_engine_move)
                self.pending_engine_move = None
            
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
                        # Time control buttons - first row
                        if self.HEIGHT - 210 + 25 <= pos[1] <= self.HEIGHT - 210 + 55:
                            time_options = [1, 3, 5, 10]
                            button_width = 65
                            for i, time_val in enumerate(time_options):
                                x_pos = panel_x + 15 + i * (button_width + 5)
                                if x_pos <= pos[0] <= x_pos + button_width:
                                    self.think_time = time_val
                                    print(f"⏱ Engine think time set to {time_val}s")
                        
                        # Time control buttons - second row
                        elif self.HEIGHT - 210 + 60 <= pos[1] <= self.HEIGHT - 210 + 90:
                            time_options = [20, 30, 60]
                            button_width = 65
                            for i, time_val in enumerate(time_options):
                                x_pos = panel_x + 15 + i * (button_width + 5)
                                if x_pos <= pos[0] <= x_pos + button_width:
                                    self.think_time = time_val
                                    print(f"⏱ Engine think time set to {time_val}s")
                        
                        # Undo button
                        elif self.HEIGHT - 115 <= pos[1] <= self.HEIGHT - 80:
                            self.undo_move()
                        
                        # New Game button
                        elif self.HEIGHT - 70 <= pos[1] <= self.HEIGHT - 35:
                            if panel_x + 15 <= pos[0] <= panel_x + 15 + (self.PANEL_WIDTH - 35) // 2:
                                self.new_game()
                        
                        # Flip Board button
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
            self.engine_thread.join(timeout=1.0)
        
        pygame.quit()
        sys.exit()


if __name__ == "__main__":
    print("="*70)
    print("   🐓⚡ COCKCHESS ULTRA V2 - NEXT GENERATION ENGINE ⚡🐓")
    print("="*70)
    print("\n📊 Target Rating: 4000 ELO)
    print("\n🆕 New Features:")
    print("   ✓ Undo button (takes back your move and engine's move)")
    print("   ✓ Extended time controls: 1s, 3s, 5s, 10s, 20s, 30s, 60s")
    print("   ✓ Board doesn't change while engine is thinking")
    print("\n🔥 Advanced Features:")
    print("   ✓ Principal Variation Search (PVS)")
    print("   ✓ Null Move Pruning")
    print("   ✓ Late Move Reductions (LMR)")
    print("   ✓ Aspiration Windows")
    print("   ✓ Advanced Evaluation")
    print("   ✓ Opening Book")
    print("\n📦 Initializing...")
    
    try:
        gui = ChessGUI()
        print("✅ GUI loaded successfully!")
        print("\n🎮 Controls:")
        print("   • Click pieces to move")
        print("   • Click time buttons to adjust engine think time")
        print("   • Click Undo to take back your last move")
        print("   • New Game / Flip Board buttons")
        print("\n🚀 Starting game...\n")
        
        gui.run()
    except Exception as e:
        print(f"\n❌ Error: {e}")
        import traceback
        traceback.print_exc()

