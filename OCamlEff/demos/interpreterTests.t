  $ ./interpreterTests.exe <<-EOF
  >  let fib n k = if n < 2 then n else fib (n-1) (fun l -> fib (n-2) (fun r -> k (l+r)));;
  Typing error: (NoVariable "fib")
  =====================================
  $ ./interpreterTests.exe <<-EOF
  > let x = (1/0);;
  Division_by_zero
  =====================================
  $ ./interpreterTests.exe <<-EOF
  >  effect E: (int -> int -> int list -> bool) -> int
  >  ;;
  >  let helper x = match perform (E x) with
  >     | effect (E s) k -> continue k (s*s)
  >     | l -> l
  >  ;;
  >  let res = match perform (E 5) with
  >     | effect (E s) k -> continue k (s*s)
  >     | l -> helper l
  >  ;;
  Typing error: UnificationFailed
  =====================================
  $ ./interpreterTests.exe <<-EOF
  >  let rec fib n k = if n < 2 then k n else fib (n-1) (fun l -> fib (n-2) (fun r -> k (l+r)));;
  >  let ans = fib 6 (fun x -> x);;
  val fib : int -> (int -> '_19) -> '_19 = <fun>
  val ans : int = 8
  =====================================
  $ ./interpreterTests.exe <<-EOF
  >  effect E: int -> int
  >  ;;
  >  let helper x = match perform (E x) with
  >     | effect (E s) k -> continue k (s*s)
  >     | l -> l
  >  ;;
  >  let res = match perform (E 5) with
  >     | effect (E s) k -> continue k (s*s)
  >     | l -> helper l
  >  ;;
  val E : int -> int eff = effect
  val helper : int -> int = <fun>
  val res : int = 625
  =====================================
  $ ./interpreterTests.exe <<-EOF
  >  effect EmptyListException : int
  >  ;;
  >  let list_hd = function
  >     | [] -> perform EmptyListException
  >     | hd :: _ -> hd
  >  ;;
  >  let empty = []
  >  ;;
  >  let non_empty = [1; 2; 3]
  >  ;;
  >  let safe_list_hd l = match list_hd l with
  >    | effect EmptyListException k -> 0, false
  >    | res -> res, true
  >  ;;
  >    let empty_hd = safe_list_hd empty
  >  ;;
  >    let non_empty_hd = safe_list_hd non_empty
  >  ;;
  val EmptyListException : int eff = effect
  val list_hd : int list -> int = <fun>
  val empty : '_5 list = []
  val non_empty : int list = [1; 2; 3]
  val safe_list_hd : int list -> int * bool = <fun>
  val empty_hd : int * bool = (0, false)
  val non_empty_hd : int * bool = (1, true)
  =====================================
  $ ./interpreterTests.exe <<-EOF
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
  val Failure : string -> int eff = effect
  val binary_int_of_str : string -> int = <fun>
  val sum_up : string list -> int = <fun>
  val lst : string list = ["0"; "hope"; "1"; "it"; "0"; "works"; "1"]
  val result : int = 2
  =====================================
  $ ./interpreterTests.exe <<-EOF
  >  let rec fix f x = f (fix f) x
  >  ;;
  >  let f self n = if n <= 1 then n else self (n - 1) * n
  >  ;;
  >  let fact10 = fix f 10
  val fix : (('_2 -> '_5) -> '_2 -> '_5) -> '_2 -> '_5 = <fun>
  val f : (int -> int) -> int -> int = <fun>
  val fact10 : int = 3628800
  =====================================
  $ ./interpreterTests.exe <<-EOF
  >  let mtx1 = [[1; 2; 3; 4];[1; 2; 3; 4];[1; 2; 3; 4]]
  >  ;;
  >  let mtx2 = [[0; 1; 0; 8];[0; 0; 1; 3]; [1; 0; 1; 2]]
  >  ;;
  >  let rec sum_up_row = function
  >  | [], [] -> []
  >  | hd1 :: tl1, hd2 :: tl2 -> (hd1 + hd2) :: sum_up_row (tl1, tl2)
  > ;;
  >  let rec sum_up_matrix = function
  >  | [], [] -> []
  >  | hd1 :: tl1, hd2 :: tl2 -> (sum_up_row (hd1, hd2)) :: sum_up_matrix (tl1, tl2)
  >  ;;
  >  let mtx3 = sum_up_matrix (mtx1, mtx2)
  val mtx1 : int list list = [[1; 2; 3; 4]; [1; 2; 3; 4]; [1; 2; 3; 4]]
  val mtx2 : int list list = [[0; 1; 0; 8]; [0; 0; 1; 3]; [1; 0; 1; 2]]
  val sum_up_row : int list * int list -> int list = <fun>
  val sum_up_matrix : int list list * int list list -> int list list = <fun>
  val mtx3 : int list list = [[1; 3; 3; 12]; [1; 2; 4; 7]; [2; 2; 4; 6]]
  =====================================
  $ ./interpreterTests.exe <<-EOF
  >  let rec fold f init = function
  >    | [] -> init
  >    | hd :: tl -> fold f (f init hd) tl
  >  ;;
  >  let sum = fold (fun x y -> x + y) 0
  >  ;;
  >  let sum_of_first_three = sum [1; 2; 3]
  val fold : ('_12 -> '_6 -> '_12) -> '_12 -> '_6 list -> '_12 = <fun>
  val sum : int list -> int = <fun>
  val sum_of_first_three : int = 6
  =====================================
