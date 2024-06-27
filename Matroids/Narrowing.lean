import Matroids.MatroidComputations
--unused

/--
-- First possibility (7 Triangles): [0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5], [2, 3, 6], [1, 4, 6], [0, 5, 6]
def narrowing (l : List (List Nat)) : List (List Nat) → List (List Nat)
  | [], [] => []
  | h1 :: t1 =>
    elimNearlySame l.map t1
  | h1 :: h2 :: t1 =>
    h2 :: h1 :: t2
    elimNearlySame h2 h1::t2

#eval narrowing [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5], [2, 3, 6], [1, 4, 6], [0, 5, 6]] A
--/
