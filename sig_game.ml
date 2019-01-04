module type GAME =
sig
  (* TYPES *)

  (* this specifies a player:
   * which player won, which player's turn it is, etc. *)
  type which_player = P1 | P2

  (* represents the status of the game:
   * if it's over, who won,
   * whose turn it is, if it isn't *)
  type status =
    Win of which_player (* this says who wins *)
  | Draw
  | Ongoing of which_player (* this says whose turn it is *)

  (* expresses the state of the game,
   * i.e., what the board looks like, whose turn it is,
   * or anything else associated with a game at a given turn *)
  type state

  (* describes a game's moves that a player can make *)
  type move

  (* PRINTING FUNCTIONS *)
  val string_of_player : which_player -> string
  val string_of_state  : state        -> string
  val string_of_move   : move         -> string

  (* GAME LOGIC *)

  (* the state of the game when it begins *)
  val initial_state : state

  (* produces the set of legal moves at a state, represented as a list *)
  val legal_moves : state -> move list

  (* returns the status of the game at the given state *)
  val game_status : state -> status

  (* given a state and a legal move, yields the next state
     Note that this procedure is curried. *)
  val next_state : state * move -> state

  (* SPECIFIC TO HUMAN PLAYERS *)

  (* for transforming player input into
   * the internal representation of a move *)
  val move_of_string : string -> move

  (* SPECIFIC TO AI PLAYERS *)

  (* estimate the value (for player 1) of a given state *)
  val estimate_value : state -> float
end
