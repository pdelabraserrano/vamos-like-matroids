import Matroids.Relabelling
import Matroids.Test.AllPossibilities
import Matroids.Test.PartialMatroid
open List

instance : Inhabited PartialMatroid := ⟨[],[]⟩

#eval (permutation 3).map (fun f ↦ (List.range 3).map f) -- returns [[1, 2, 0], [2, 1, 0], [2, 0, 1], [0, 2, 1], [1, 0, 2], [0, 1, 2]]

#eval (List.range 8).map (permutation 8).head! -- returns [1, 2, 3, 4, 5, 6, 7, 0]

--#eval all [0, 2, 10] Even' -- returns true

-- #eval Nat.factorial 4 -- returns 24

#eval (permutation 8).head! 0 -- returns 1

-- #eval sameUpToRelabelling PartialMatroid.paa PartialMatroid.Vamos (permutation 8).head! -- returns true

#eval relabelling [[1,2,3],[4,5,6]] (· + 1) -- returns [[2, 3, 4], [5, 6, 7]]

abbrev pa1 : PartialMatroid where
  matroid:= [[0,1,2],[1,2,3]]
  remainingOptions := []

abbrev pa2 : PartialMatroid where
  matroid:= [[0,2,3],[1,2,3]]
  remainingOptions := []

-- #eval permutationsComparison 4 pa1 pa2 -- returns true

-- #eval permutationsComparison 8 PartialMatroid.paa PartialMatroid.Vamos -- returns true

-- #eval (pruning [PartialMatroid.Vamos, PartialMatroid.paa]).length

-- abbrev test1 : PartialMatroid := (take 2 Vamos1.head!).head!
-- abbrev test2 : PartialMatroid := (take 2 Vamos1.head!).getLast!

def swapSixAndSeven (N : Nat) : Nat :=
  if N == 6 then
    7
  else if N == 7 then
    6
  else
    N

-- #eval sameUpToRelabelling test1 test2 swapSixAndSeven

-- #eval let B := test2 ; let g := swapSixAndSeven ; ((relabelling B.matroid g).map List.sort).sort -- returns [[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [1, 3, 5, 7], [2, 3, 4, 5], [2, 3, 6, 7]]
-- #eval let A := test1 ; A.matroid -- returns [[1, 3, 5, 7], [0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [2, 3, 4, 5], [2, 3, 6, 7]]


-- #eval test2

-- #eval permutationsComparison 8 test1 test2


--#time
--#eval (pruning (Vamos1.head!)).length


--#eval complementToOriginal [[1,2,3,4],[2,4,5,7]] [[3,4,5,6],[0,2,3,5]] --true
--#eval complementToOriginal [[1,2,3,4],[2,4,5,7]] [[3,4,5,6],[0,1,3,5]] --false

#exit
#time
#eval pruning (FourTrianglesOnSixPoints.head!)

#time
#eval (pruning ((take 4 Vamos7.head!))).length
