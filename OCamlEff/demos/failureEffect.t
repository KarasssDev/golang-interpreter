  $ ./failureEffect.exe <<-EOF
  >  effect Failure : string -> int
  >  ;;
  >  let binary_int_of_str = function 
  >    | "0" -> 0
  >    | "1" -> 1
  >    | s -> perform (Failure s)
  >  ;;
  >  let rec sum_up = function 
  >    | [] -> 0
  >    | s :: ss -> binary_int_of_str s + sum_up ss
  >  ;;
  >  let lst = ["0";"hope";"1";"it";"0";"works";"1"];;
  >  let result = match sum_up lst with 
  >    | effect (Failure _) k -> continue k 0
  >    | res -> res
  >  ;; 
  val Failure = effect
  val binary_int_of_str = <fun>
  val lst = ["0"; "hope"; "1"; "it"; "0"; "works"; "1"]
  val result = 2
  val sum_up = <fun>
