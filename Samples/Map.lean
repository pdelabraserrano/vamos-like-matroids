/-- Sample of how the map function works and implementation of an arbitrary .mapHeather
function to test the logic behind it -/

abbrev l := [1, 2, 5]

#eval l.map (· ^ 2) -- returns [1, 4, 25]

#eval l.map (· + 1) -- returns [2, 3, 6]

#eval l.map (· * 2) -- returns [2, 4, 10]

def List.mapHeather (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | head :: tail => (f head) :: (tail.mapHeather f)

#eval l.mapHeather (· ^ 2) -- returns [1, 4, 25]
