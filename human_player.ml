#use "sig_game.ml" ;;

module HumanPlayer = functor (Game: GAME) ->
struct
  module PlayerGame = Game

  let rec next_move s =
    try
      let m = PlayerGame.move_of_string (read_line ()) in
      if List.mem m (PlayerGame.legal_moves s) then m
      else
        let () = print_endline "Illegal move."
        in next_move s
    with
      End_of_file -> failwith "exiting."
    | Failure message -> print_endline message ; next_move s
end ;;
