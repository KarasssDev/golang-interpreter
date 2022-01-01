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
  val E = effect
  val helper = <fun>
  val res = 625
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
  val EmptyListException = effect
  val list_hd = <fun>
  val empty = []
  val non_empty = [1; 2; 3]
  val safe_list_hd = <fun>
  val empty_hd = (0, false)
  val non_empty_hd = (1, true)
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
  val Failure = effect
  val binary_int_of_str = <fun>
  val sum_up = <fun>
  val lst = ["0"; "hope"; "1"; "it"; "0"; "works"; "1"]
  val result = 2
  =====================================
  $ ./interpreterTests.exe <<-EOF
  >  let rec fix f x = f (fix f) x
  >  ;;
  >  let f self n = if n <= 1 then n else self (n - 1) * n
  >  ;;
  >  let fact10 = fix f 10
  val fix = <fun>
  val f = <fun>
  val fact10 = 3628800
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
  val mtx1 = [[1; 2; 3; 4]; [1; 2; 3; 4]; [1; 2; 3; 4]]
  val mtx2 = [[0; 1; 0; 8]; [0; 0; 1; 3]; [1; 0; 1; 2]]
  val sum_up_row = <fun>
  val sum_up_matrix = <fun>
  val mtx3 = [[1; 3; 3; 12]; [1; 2; 4; 7]; [2; 2; 4; 6]]
  =====================================
  $ ./interpreterTests.exe <<-EOF
  >  let rec fold f init = function 
  >    | [] -> init 
  >    | hd :: tl -> fold f (f init hd) tl
  >  ;;
  >  let sum = fold (fun x y -> x + y) 0
  >  ;;
  >  let sum_of_first_ten = sum [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
  val fold = <fun>
  val sum = <fun>
  val sum_of_first_ten = 55
  =====================================

