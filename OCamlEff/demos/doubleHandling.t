  $ ./doubleHandling.exe <<-EOF
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
