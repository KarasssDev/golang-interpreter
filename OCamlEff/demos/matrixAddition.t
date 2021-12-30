  $ ./matrixAddition.exe <<-EOF
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
  val mtx3 = [[1; 3; 3; 12]; [1; 2; 4; 7]; [2; 2; 4; 6]]
  val sum_up_matrix = <fun>
  val sum_up_row = <fun>
