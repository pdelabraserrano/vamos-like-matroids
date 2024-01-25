def sum : List Nat → Nat
  | [] => 0
  | head :: tail =>
    head + sum tail


#eval sum []
#eval sum [1, 7, 12]

def max : List Nat → Nat
  | [] => 0
  | head :: tail =>
    let m := max tail
    if m > head then
      m
    else
      head


#eval max [12, 20, 200]
