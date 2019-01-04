#use "setup.ml" ;;
#use "sig_game.ml" ;;

type space = X | O | E

type board = space list list

let string_of_space : space -> string = function
    X -> "X"
  | O -> "O"
  | E -> "_" ;;

let rec make_column : int -> space list = function
    1 -> [E]
  | x -> E::make_column (x-1) ;;

let make_board : int * int -> board = function (r,c) ->
  let col = make_column r in
    let rec make_board_helper : int -> board = function n ->
      match n with
          0 -> []
        | x -> col::make_board_helper (x-1)
  in make_board_helper c ;;

let rec transpose : 'a list list -> 'a list list = function boa ->
  match boa with
    [] | [] :: _ -> failwith "A board must have at least one row/column."
  | (hd1 :: []) :: tl -> (List.fold_right List.append boa []) :: []
  | (hd1 :: tl1) :: tl -> ((List.map List.hd boa)) ::
                           (transpose (List.map List.tl boa)) ;;

let string_of_board : board * int -> string = function boa, c ->
  let rec int_list : int * int list -> int list = function
      1, acc -> 1::acc
    | x, acc -> int_list (x-1, x::acc) in
  (List.fold_right
    (fun w x -> ("[ " ^ (List.fold_right
        (fun y z -> (string_of_space y) ^ " " ^ z) w ("]\n" ^ x))))
      (transpose boa)
      ("  " ^ (List.fold_right
                (fun x y -> (string_of_int x) ^ " " ^ y)
                (int_list (c, [])) ""))) ;;

let rec is_four : space list -> bool = function
    s1::s2::s3::s4::rest ->
      (s1 = s2 && s2 = s3 && s3 = s4 && s1 != E) || (is_four (s2::s3::s4::rest))
  | _ -> false ;;

let all_diagonals : board -> board = function boa ->
  let rec left_diagonals : board * int * int -> space list list =
  function (boa, row, column) ->
    let rec get_single : board * int * int -> space list =
    function boa, r, c ->
      if c = List.length boa || r = List.length (List.hd boa) then []
      else (List.nth (List.nth boa c) r) :: get_single (boa, r + 1, c + 1) in
    match (List.length boa) - column with
      | 0 ->
        (match (List.length (List.hd boa)) - row with
          | 0 -> []
          | r -> get_single (boa, row, 0)::
                  left_diagonals (boa, row+1, column))
      | c ->
          get_single (boa, 0, column)::left_diagonals (boa, 0, column + 1) in
  (left_diagonals (boa, 0, 0))@
  (left_diagonals (List.map List.rev boa, 0, 0)) ;;

let is_win : board -> bool = function boa ->
  (List.exists is_four boa) ||
  (List.exists is_four (transpose boa)) ||
  (List.exists is_four (all_diagonals boa)) ;;

module Connect4 = functor (I: sig val initial_rows : int
                                  val initial_cols : int end) ->
struct
  type which_player = P1 | P2

  type status =
  | Win of which_player
  | Draw
  | Ongoing of which_player

  type state = State of (status * board)

  type move = Move of int

  let string_of_player : which_player -> string = function
    P1 -> "Player 1"
  | P2 -> "Player 2"

  let string_of_state : state -> string = function State (st, boa) ->
    (match st with
      Win x -> (string_of_player x) ^ " wins!\n"
    | Draw -> "It's a draw!\n"
    | Ongoing x -> "It is " ^ (string_of_player x) ^ "'s turn.\n") ^
    (string_of_board (boa, I.initial_cols))

  let string_of_move : move -> string = function
    Move x -> "of dropping their piece into column " ^ (string_of_int x)

  let initial_state : state =
    if (I.initial_cols > 0)&&(I.initial_rows > 0)
    then State (Ongoing P1, make_board (I.initial_rows, I.initial_cols))
    else failwith "The board must have at least 1 row and 1 column"

  let legal_moves : state -> move list = function State (stat, board) ->
    let rec legal_moves_helper : board * int -> move list = function
      | [], num -> []
      | head::tail, num ->
          if (List.hd head) = E
          then (Move num)::legal_moves_helper (tail, num+1)
          else legal_moves_helper (tail, num+1)
    in legal_moves_helper (board, 1)

  let game_status : state -> status = function State (status, boa) -> status

  let next_state : state * move -> state =
  function (State (Ongoing p, boa), Move x) ->
    let rec space_of_player : which_player -> space = function P1 -> X | P2 -> O
    and other_player : which_player -> which_player = function
        P1 -> P2
      | P2 -> P1
    and place_piece : space list * space list * space -> space list =
      function
        E::tl, acc, s -> tl@(s::acc)
      | hd::tl, acc, s -> place_piece (tl, hd::acc, s)
      | _ -> failwith "no"
    and replace : 'a list * 'a * int * 'a list -> 'a list = function
      (hd::tl, x, i, acc) ->
        (match i with
             0 -> (List.rev (x::acc))@tl
           | n -> replace (tl, x, n-1, hd::acc))
      | _ -> failwith "this really shouldn't happen" in
    let new_board : board =
          replace
            (boa,
            place_piece (List.rev (List.nth boa (x-1)), [], space_of_player p),
            x-1, []) in
    (match is_win new_board with
        true -> State (Win p, new_board)
      | false ->
          (match legal_moves (State (Ongoing (other_player p), new_board)) with
               [] -> State (Draw, new_board)
             | _ -> State (Ongoing (other_player p), new_board)))
    | _ -> failwith "In order to find a next state, the game must be ongoing"

  let move_of_string : string -> move = function x ->
    try
      Move (int_of_string x)
    with
      _ -> failwith "Please input an integer."

  let estimate_value : state -> float = function State (stat, boa) ->
    let rec col_eval : space list -> float = function
        E::X::X::X::_ -> 50.0
      | E::O::O::O::_ -> -50.0
      | E::E::X::X::_ -> 10.0
      | E::E::O::O::_ -> -10.0
      | E::E::E::X::_ -> 1.0
      | E::E::E::O::_ -> -1.0
      | E::tl -> col_eval tl
      | _ -> 0.0
    and board_col_eval : board -> float = function bd ->
      List.fold_right (fun x y -> x +. y) (List.map col_eval bd) 0.0
    and group_eval : space list -> float = function lst ->
      if (List.exists (fun x -> x = X) lst) &&
         (List.exists (fun x -> x = O) lst)
      then 0.0
      else let player_pieces = (List.filter (fun x -> x != E) lst) in
        match (List.length player_pieces), player_pieces with
            0, [] -> 0.0
          | 1, X::_ -> 1.0
          | 2, X::_ -> 10.0
          | 3, X::_ -> 50.0
          | 1, _ -> -1.0
          | 2, _ -> -10.0
          | 3, _ -> -50.0
          | _ -> failwith "Inputted group is too long"
    and piece_groups : space list -> board = function
        x::y::z::w::tl -> (x::y::z::[w])::(piece_groups (y::z::w::tl))
      | _ -> []
    and board_row_eval : board -> float = function bd ->
      List.fold_right (fun x y -> x +. y)
        (List.map group_eval
          (List.flatten (List.map piece_groups (transpose bd)))) 0.0
    and board_diag_eval : board -> float = function bd ->
      List.fold_right (fun x y -> x +. y)
        (List.map group_eval
          (List.flatten (List.map piece_groups (all_diagonals bd)))) 0.0
    in
    match stat with
        Win x -> (match x with P1 -> max_float | P2 -> min_float)
      | Draw -> 0.0
      | Ongoing x ->
          board_col_eval boa +. board_row_eval boa +. board_diag_eval boa
end ;;

module TradConnect4 : GAME = Connect4 (struct let initial_rows = 6
                                              let initial_cols = 7 end) ;;

module TestModule = Connect4 (struct let initial_rows = 6
                                     let initial_cols = 7 end) ;;

open TestModule ;;

"TEST CASES for string_of_space:" ;;
check_expect (string_of_space X) "X" ;;
check_expect (string_of_space O) "O" ;;
check_expect (string_of_space E) "_" ;;

"TEST CASES for make_column:" ;;
check_expect (make_column 6) [E ; E ; E ; E ; E ; E] ;;
check_expect (make_column 1) [E] ;;

"TEST CASES for make_board:" ;;
check_expect (make_board (5,7)) [[E ; E ; E ; E ; E] ;
                                 [E ; E ; E ; E ; E] ;
                                 [E ; E ; E ; E ; E] ;
                                 [E ; E ; E ; E ; E] ;
                                 [E ; E ; E ; E ; E] ;
                                 [E ; E ; E ; E ; E] ;
                                 [E ; E ; E ; E ; E] ] ;;
check_expect (make_board (1,1)) [[E]] ;;
check_expect (make_board (9,2)) [[E ; E ; E ; E ; E ; E ; E ; E ; E] ;
                                 [E ; E ; E ; E ; E ; E ; E ; E ; E]] ;;

"TEST CASES for transpose:" ;;
check_expect (transpose [[E ; E ; E ; E ; O] ;
                         [E ; E ; E ; E ; X] ;
                         [E ; X ; O ; X ; O] ;
                         [E ; E ; O ; X ; X] ;
                         [E ; E ; E ; O ; O] ;
                         [E ; E ; E ; E ; X] ;
                         [E ; E ; E ; E ; E]])
             [[E ; E ; E ; E ; E ; E ; E];
              [E ; E ; X ; E ; E ; E ; E];
              [E ; E ; O ; O ; E ; E ; E];
              [E ; E ; X ; X ; O ; E ; E];
              [O ; X ; O ; X ; O ; X ; E]] ;;
check_expect (transpose [[X]]) [[X]] ;;
check_expect (transpose [[O] ; [X] ; [E]]) [[O ; X ; E]] ;;

"TEST ERRORS for transpose:" ;;
check_error
  (fun () -> transpose [])
  "A board must have at least one row/column." ;;
check_error
  (fun () -> transpose [[] ; [] ; []])
  "A board must have at least one row/column." ;;

"TEST CASES for string_of_board:" ;;
check_expect (string_of_board ([[E ; E ; E ; E ; O] ;
                                [E ; E ; E ; E ; X] ;
                                [E ; X ; O ; X ; O] ;
                                [E ; E ; O ; X ; X] ;
                                [E ; E ; E ; O ; O] ;
                                [E ; E ; E ; E ; X] ;
                                [E ; E ; E ; E ; E]], 7))
             ("[ _ _ _ _ _ _ _ ]\n" ^
              "[ _ _ X _ _ _ _ ]\n" ^
              "[ _ _ O O _ _ _ ]\n" ^
              "[ _ _ X X O _ _ ]\n" ^
              "[ O X O X O X _ ]\n" ^
              "  1 2 3 4 5 6 7 ") ;;
check_expect (string_of_board ([[O]], 1)) "[ O ]\n  1 " ;;
check_expect (string_of_board ([[O] ; [X] ; [E]], 3)) "[ O X _ ]\n  1 2 3 " ;;

"TEST CASES for is_four:" ;;
check_expect (is_four [ E ; E ; E ; E ; E ]) false ;;
check_expect (is_four [ O ; E ; X ; X ; X ; X ; E ]) true ;;
check_expect (is_four []) false ;;
check_expect (is_four [ O ; E ; O ; O ; O ]) false ;;
check_expect (is_four [ X ; X ; X ]) false ;;
check_expect (is_four [ O ; O ; O ; O ]) true ;;
check_expect (is_four [ X ; O ; O ; O ; O]) true ;;

"TEST CASES for all_diagonals:" ;;
check_expect (all_diagonals ([[E ; E ; E ; E ; O] ;
                              [E ; E ; E ; E ; X] ;
                              [E ; X ; O ; X ; O] ;
                              [E ; E ; O ; X ; X] ;
                              [E ; E ; E ; O ; O] ;
                              [E ; E ; E ; E ; X] ;
                              [E ; E ; E ; E ; E]]))
              ([[E; E; O; X; O];
                [E; X; O; O; X];
                [E; E; E; E; E];
                [E; E; E; E];
                [E; E; E];
                [E; E];
                [E];
                [E; E; O; X; O];
                [E; E; X; X];
                [E; E; O];
                [E; X];
                [O];
                [O; E; O; E; E];
                [X; X; O; E; E];
                [O; X; E; E; E];
                [X; O; E; E];
                [O; E; E];
                [X; E];
                [E];
                [O; E; O; E; E];
                [E; E; X; E];
                [E; E; E];
                [E; E];
                [E]]) ;;

"TEST CASES for is_win:" ;;
check_expect (is_win [[E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E]]) false ;;
check_expect (is_win [[E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [X ; X ; X ; X ; E]]) true ;;
check_expect (is_win [[E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; O ; E] ;
                  [E ; E ; E ; O ; E] ;
                  [E ; E ; E ; O ; E] ;
                  [X ; X ; X ; O ; E]]) true ;;
check_expect (is_win [[E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [E ; E ; E ; E ; E] ;
                  [O ; E ; E ; E ; E] ;
                  [X ; O ; E ; O ; E] ;
                  [X ; X ; O ; O ; E] ;
                  [X ; X ; X ; O ; E]]) true ;;

"TEST CASES for string_of_player:" ;;
check_expect (string_of_player P1) "Player 1" ;;
check_expect (string_of_player P2) "Player 2" ;;

"TEST CASES for string_of_state:" ;;
check_expect (string_of_state (State (Win P2,
                               [[E ; E ; E ; X ; O] ;
                                [E ; E ; E ; X ; X] ;
                                [E ; X ; O ; X ; O] ;
                                [E ; E ; O ; X ; X] ;
                                [E ; E ; E ; O ; O] ;
                                [E ; E ; E ; E ; X] ;
                                [E ; E ; E ; E ; E]])))
             ("Player 2 wins!\n" ^
              "[ _ _ _ _ _ _ _ ]\n" ^
              "[ _ _ X _ _ _ _ ]\n" ^
              "[ _ _ O O _ _ _ ]\n" ^
              "[ X X X X O _ _ ]\n" ^
              "[ O X O X O X _ ]\n" ^
              "  1 2 3 4 5 6 7 ") ;;
check_expect (string_of_state (State (Draw,
                [[O ; O ; X ; O] ;
                 [X ; X ; X ; O] ;
                 [X ; O ; O ; O] ;
                 [X ; X ; O ; X] ;
                 [O ; O ; X ; O] ;
                 [X ; X ; X ; O] ;
                 [X ; O ; O ; O]])))
             ("It's a draw!\n" ^
              "[ O X X X O X X ]\n" ^
              "[ O X O X O X O ]\n" ^
              "[ X X O O X X O ]\n" ^
              "[ O O O X O O O ]\n" ^
              "  1 2 3 4 5 6 7 ");;
check_expect (string_of_state (State (Ongoing P1,
                               [[E ; E ; E ; E ; O] ;
                                [E ; E ; E ; E ; X] ;
                                [E ; X ; O ; X ; O] ;
                                [E ; E ; O ; X ; X] ;
                                [E ; E ; E ; O ; O] ;
                                [E ; E ; E ; E ; X] ;
                                [E ; E ; E ; E ; E]])))
             ("It is Player 1's turn.\n" ^
              "[ _ _ _ _ _ _ _ ]\n" ^
              "[ _ _ X _ _ _ _ ]\n" ^
              "[ _ _ O O _ _ _ ]\n" ^
              "[ _ _ X X O _ _ ]\n" ^
              "[ O X O X O X _ ]\n" ^
              "  1 2 3 4 5 6 7 ") ;;

"TEST CASES for string_of_move:" ;;
check_expect (string_of_move (Move 1)) "of dropping their piece into column 1" ;;
check_expect (string_of_move (Move 2)) "of dropping their piece into column 2" ;;
check_expect (string_of_move (Move 4)) "of dropping their piece into column 4" ;;

"TEST CASES for initial_state:" ;;
check_expect initial_state (State (Ongoing P1,
                [[E; E; E; E; E; E];
                 [E; E; E; E; E; E];
                 [E; E; E; E; E; E];
                 [E; E; E; E; E; E];
                 [E; E; E; E; E; E];
                 [E; E; E; E; E; E];
                 [E; E; E; E; E; E]])) ;;

"TEST CASES for legal_moves:" ;;
check_expect (legal_moves (State (Ongoing P2,
                               [[E ; E ; E ; E ; E] ;
                                [E ; E ; E ; E ; X] ;
                                [E ; X ; O ; X ; O] ;
                                [E ; E ; O ; X ; X] ;
                                [E ; E ; E ; O ; O] ;
                                [E ; E ; E ; E ; X] ;
                                [E ; E ; E ; E ; E]])))
              ([Move 1 ; Move 2 ; Move 3 ; Move 4 ; Move 5 ; Move 6 ; Move 7]);;
check_expect (legal_moves (State (Ongoing P1,
                               [[O ; O ; O ; X ; O] ;
                                [E ; E ; E ; X ; X] ;
                                [O ; X ; O ; O ; O] ;
                                [X ; O ; O ; X ; X] ;
                                [O ; X ; O ; X ; O] ;
                                [E ; E ; E ; O ; X] ;
                                [X ; X ; X ; O ; X]]))) ([Move 2 ; Move 6]) ;;
check_expect (legal_moves (State (Draw,
                               [[O ; O ; X ; O ; O] ;
                                [X ; O ; O ; X ; X] ;
                                [O ; X ; O ; X ; O] ;
                                [X ; O ; O ; X ; X] ;
                                [O ; X ; X ; O ; O] ;
                                [X ; O ; O ; X ; X] ;
                                [X ; X ; O ; X ; X]]))) ([]) ;;

check_expect (legal_moves (State (Win P2,
                               [[O ; O ; X ; O ; O] ;
                                [X ; O ; O ; X ; X] ;
                                [O ; X ; O ; X ; O] ;
                                [X ; O ; O ; O ; X] ;
                                [O ; X ; X ; O ; O] ;
                                [X ; O ; O ; X ; X] ;
                                [X ; X ; O ; X ; X]]))) ([]) ;;

"TEST CASES for game_status:" ;;
check_expect (game_status (State (Win P1,
                [[X ; E ; O ; E] ;
                 [O ; X ; O ; E] ;
                 [O ; X ; X ; E] ;
                 [O ; X ; O ; X]]))) (Win P1) ;;
check_expect (game_status (State (Draw,
                [[O ; O ; X ; O] ;
                 [X ; X ; X ; O] ;
                 [X ; O ; O ; O] ;
                 [X ; O ; X ; X]]))) Draw ;;
check_expect (game_status (State (Ongoing P2,
                [[X ; E ; O ; E] ;
                 [O ; X ; O ; E] ;
                 [O ; X ; X ; E] ;
                 [O ; X ; O ; X]]))) (Ongoing P2) ;;

"TEST CASES for next_state:" ;;
check_expect
  (next_state (State (Ongoing P1, [[E; E; E; E; E; E];
                                   [E; E; E; E; E; O];
                                   [E; E; E; E; O; X];
                                   [E; E; E; E; O; X];
                                   [E; E; E; E; E; X];
                                   [E; E; E; E; E; E];
                                   [E; E; E; E; E; E]]), Move 1))
  (State (Ongoing P2, [[E; E; E; E; E; X];
                       [E; E; E; E; E; O];
                       [E; E; E; E; O; X];
                       [E; E; E; E; O; X];
                       [E; E; E; E; E; X];
                       [E; E; E; E; E; E];
                       [E; E; E; E; E; E]])) ;;
check_expect
  (next_state (State (Ongoing P2, [[E; E; E; E; E; X];
                                   [E; E; E; E; E; O];
                                   [E; E; E; E; O; X];
                                   [E; E; E; E; O; X];
                                   [E; E; E; E; O; X];
                                   [E; E; E; E; E; E];
                                   [E; E; E; E; E; E]]), Move 2))
  (State (Win P2, [[E; E; E; E; E; X];
                   [E; E; E; E; O; O];
                   [E; E; E; E; O; X];
                   [E; E; E; E; O; X];
                   [E; E; E; E; O; X];
                   [E; E; E; E; E; E];
                   [E; E; E; E; E; E]])) ;;

"TEST ERRORS for next_state:" ;;
check_error
  (fun () -> next_state (State (Draw, [[O ; O ; X ; O] ;
                                       [X ; X ; X ; O] ;
                                       [X ; O ; O ; O] ;
                                       [X ; X ; O ; X] ;
                                       [O ; O ; X ; O] ;
                                       [X ; X ; X ; O] ;
                                       [X ; O ; O ; O]]), Move 1))
  "In order to find a next state, the game must be ongoing" ;;


"TEST CASES for move_of_string:" ;;
check_expect (move_of_string "4") (Move 4) ;;
check_error (fun () -> move_of_string "CS17") "Please input an integer." ;;

"TEST CASES for estimate_value:" ;;
check_expect (estimate_value (State (Ongoing P1, [[E ; E ; E]]))) 0.0 ;;
check_expect (estimate_value (State (Ongoing P1,
                               [[E ; E ; E ; E ; O] ;
                                [E ; E ; E ; E ; X] ;
                                [E ; X ; O ; X ; O] ;
                                [E ; E ; O ; X ; X] ;
                                [E ; E ; E ; O ; O] ;
                                [E ; E ; E ; E ; X] ;
                                [E ; E ; E ; E ; E]]))) (-28.0) ;;
