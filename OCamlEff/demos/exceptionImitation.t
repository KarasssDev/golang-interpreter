  $ ./exceptionImitation.exe <<-EOF
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
  val empty = []
  val empty_hd = (0, false)
  val list_hd = <fun>
  val non_empty = [1; 2; 3]
  val non_empty_hd = (1, true)
  val safe_list_hd = <fun>
