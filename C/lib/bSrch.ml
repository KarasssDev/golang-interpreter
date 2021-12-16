let take n l =
  let rec take' n l acc =
    match l with
    | h :: tl when n > 0 -> take' (n - 1) tl (h :: acc)
    | _ -> List.rev acc
  in
  take' n l []

let rec take_after n l =
  match l with _ :: tl when n > 0 -> take_after (n - 1) tl | _ -> l

let b_srch v l =
  let lft ps = take (List.length ps / 2) ps in
  let rgt ps = take_after (List.length ps / 2) ps in
  let rec b_srch' v = function
    | [ (l, r) ] -> l <= v && v <= r
    | ps when v < fst @@ List.hd @@ rgt ps -> b_srch' v @@ lft ps
    | ps -> b_srch' v @@ rgt ps
  in
  b_srch' v @@ List.sort compare l
