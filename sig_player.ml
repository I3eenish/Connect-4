#use "sig_game.ml" ;;

(* describes either a human or AI player,
 * which selects the next move *)
module type PLAYER =
sig
  module PlayerGame : GAME
  (* given a state, selects a move *)
  val next_move : PlayerGame.state -> PlayerGame.move
end
