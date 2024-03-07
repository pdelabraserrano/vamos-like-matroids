abbrev l := [1, 2, 5]

#eval l.map (· ^ 2)

#eval l.map (· + 1)

#eval l.map (· * 2)

def List.mapHeather (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | head :: tail => (f head) :: (tail.mapHeather f)

#eval l.mapHeather (· ^ 2)
