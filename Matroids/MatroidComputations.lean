import Matroids.NearlySame

def combinations : Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, k + 1 => (combinations n (k + 1)) ++ ((combinations n k).map (· ++ [n]))

abbrev A := combinations 6 3
#eval A

abbrev B := elimNearlySame [0, 1, 2] A
#eval B

abbrev C1 := elimNearlySame [0, 3, 4] B
abbrev D := elimNearlySame [1, 3, 5] C1

abbrev C2 := elimNearlySame [3, 4, 5] B
#eval C2
