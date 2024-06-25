import Matroids.Relabelling

#eval (permutation 3).map (fun f ↦ (List.range 3).map f) -- returns [[1, 2, 0], [2, 1, 0], [2, 0, 1], [0, 2, 1], [1, 0, 2], [0, 1, 2]]

#eval (List.range 8).map (permutation 8).head! -- returns [1, 2, 3, 4, 5, 6, 7, 0]

#eval all [0, 2, 10] Even' -- returns true

#eval Nat.factorial 4 -- returns 24

#eval @Finset.univ (Perm (Fin 2)) -- !!! returns an error

#eval (permutation 8).head! 0 -- returns 1

#eval sameUpToRelabelling PartialMatroid.paa PartialMatroid.Vamos (permutation 8).head! -- returns true

#eval relabelling [[1,2,3],[4,5,6]] (· + 1) -- returns [[2, 3, 4], [5, 6, 7]]

abbrev pa1 : PartialMatroid where
  matroid:= [[0,1,2],[1,2,3]]
  remainingOptions := []

abbrev pa2 : PartialMatroid where
  matroid:= [[0,2,3],[1,2,3]]
  remainingOptions := []

#eval permutationsComparison 4 pa1 pa2 -- returns true

#eval permutationsComparison 8 PartialMatroid.paa PartialMatroid.Vamos -- returns true
