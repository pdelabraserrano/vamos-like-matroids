import Matroids.PartialMatroid

-- Initial list of possible combinations
abbrev A73 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 7 3

#eval A73

abbrev A53 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 5 3

abbrev A63 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 6 3

abbrev A74 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 7 4

abbrev A84 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 8 4

abbrev paa : PartialMatroid where
  matroid := [[0,1,2,7], [0,3,4,7], [1,2,3,4], [1,2,5,6], [3,4,5,6]]
  remainingOptions := []


abbrev B1 : PartialMatroid := augment [0, 1, 2] A73
abbrev C1 : PartialMatroid := augment [0, 3, 4] B1
abbrev D1 : PartialMatroid := augment [1, 3, 5] C1
abbrev E1 := augment [2, 4, 5] D1

#eval E1
#eval augment [2, 3, 6] E1
#eval D1
#eval D1.remainingOptions
#eval D1.remainingOptions.map (augment · D1)


#eval [1, 0, 2] < [1, 0, 3]
#eval [3, 4, 5] < [3, 5, 6]
