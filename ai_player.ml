#use "sig_game.ml" ;;
#use "game.ml" ;;

module AIPlayer = functor (Game: GAME) ->
struct
  module PlayerGame = Game

  (* TODO *)
  let next_move s =
    let rec vals :
      PlayerGame.state * PlayerGame.move list -> (PlayerGame.move * float) list =
      function sta, mlst -> match mlst with
          hd::tl ->
            (hd, minimax (PlayerGame.next_state (sta,hd),3))::
            (vals (sta,tl))
        | [] -> []
    and successors :
      PlayerGame.state * PlayerGame.move list -> PlayerGame.state list =
      function sta,mlst -> match mlst with
          hd::tl -> PlayerGame.next_state (sta, hd)::successors (sta,tl)
        | [] -> []
    and minimax : PlayerGame.state * int -> float = function
        sta, 0 -> PlayerGame.estimate_value sta
      | sta, depth ->
          match PlayerGame.game_status sta with
              Draw -> 0.0
            | Win P1 -> max_float
            | Win P2 -> (-.max_float)
            | Ongoing P1 ->
                List.fold_right (fun x y -> max x y)
                  (List.map (fun x -> minimax (x,depth-1))
                    (successors (sta, PlayerGame.legal_moves sta)))
                      (-.max_float)
            | Ongoing P2 ->
                List.fold_right (fun x y -> min x y)
                  (List.map (fun x -> minimax (x,depth-1))
                    (successors (sta, PlayerGame.legal_moves sta)))
                      max_float
    and choose_move :
        (PlayerGame.move * float) list * ('a -> 'b) -> PlayerGame.move =
      function lst,p -> match lst with
          (m1,v1)::(m2,v2)::tl -> choose_move ((if (p v1 v2) = v1
                                                then (m1,v1)
                                                else (m2,v2))::tl, p)
        | [(m1,v1)] -> m1
        | _ -> failwith "there are no moves available whoops" in
    match PlayerGame.game_status s with
        Ongoing x ->
          (match x with
              P1 -> choose_move (vals (s, PlayerGame.legal_moves s), max)
            | P2 -> choose_move (vals (s, PlayerGame.legal_moves s), min))
      | _ -> failwith "the game should really be ongoing to find the next value"
end ;;

module AIConnect4Player = AIPlayer (TestModule) ;;

open AIConnect4Player ;;