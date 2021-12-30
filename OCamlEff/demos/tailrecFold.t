  $ ./tailrecFold.exe <<-EOF
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
