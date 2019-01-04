exception Overflow

let ( == ) a b = (a = b)

let ( != ) a b = (a <> b)

let ( + ) a b =
  let c = a + b in
  if (a lxor b) lor (a lxor (lnot c)) < 0 then c else raise Overflow

let ( - ) a b =
  let c = a - b in
  if (a lxor (lnot b)) lor (b lxor c) < 0 then c else raise Overflow

let ( * ) a b =
  let c = a * b in
  if Int64.of_int c = Int64.mul (Int64.of_int a) (Int64.of_int b)
  then c else raise Overflow

let ( / ) a b =
  if a = min_int && b = -1 then raise Overflow else a / b

let ( ~- ) x = if x <> min_int then -x else raise Overflow

type 'a result = 
  | Actual_Result of 'a 
  | Expected_Result of 'a
  | Actual_Error of string
  | Expected_Error of string ;;

type 'a check_result =
  | Test_Passed 
  | Test_Failed of 'a result * 'a result ;;

(* check-expect
Inputs: actual and expected results
Output: Test_Passed if results or equal, or Test_Failed otherwise *)
let check_expect (input : 'a) (expected : 'a) : 'a check_result =
  if (input = expected) then Test_Passed
  else Test_Failed (Actual_Result (input), Expected_Result (expected)) ;;

(* check_within
Input: Three floats, input, expected, and within. Input is a given value to be checked.
Output: The boolean "true" if input lies within the range (expected - within) and (expected + within),
		and "false" otherwise. *)
let check_within (input : float) (expected : float) (within : float) : float check_result =
  if abs_float (input -. expected) <= abs_float within then Test_Passed
  else Test_Failed (Actual_Result (input), Expected_Result (expected)) ;;

(* check_error
Input: a one-argument procedure 'thunk' that returns the thing you want to test when it's applied to an int
       and a string of the error message of the 'failwith' clause in the procedure
Output: a Test_Passed or Test_Failed *)
let check_error (input : unit -> 'a) (expect : string) : 'a check_result =
  try 
    ignore (input());
    Test_Failed (Actual_Result (input()), Expected_Error (expect))
  with 
    | (Failure err) when err = expect -> Test_Passed
    | (Failure err) ->
                       Test_Failed (Actual_Error (err), Expected_Error (expect)) ;;
