import Matroids.AllPossibilities
import Matroids.Test.PartialMatroid
open PartialMatroid

#eval [1,1,1,2,2,2,3] < [1,1,2,2,2,2] -- returns true

#eval [1,1,2,2,2,2] < [2,2,2,2,2,2] -- returns true


#check List.concat

def augmentationsTwo (A : PartialMatroid) : List PartialMatroid :=
  ((augmentations A).map augmentations).join

def augmentationsThree (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsTwo).join

def augmentationsFour (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsThree).join

def augmentationsFive (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsFour).join


-- #eval D1 -- returns { matroid := [[1, 3, 5], [0, 3, 4], [0, 1, 2]], remainingOptions := [] }


#eval augmentations D1 -- returns []

#eval augmentationsTwo D1 -- returns []

#eval augmentationsThree D1 -- returns []

#eval augmentationsFour D1 -- returns []

#eval augmentationsFive D1 -- returns []

#eval (augmentationsFinal 3 E1) -- returns []

#eval (augmentationsFinal 4 A73) -- returns (to long to comment)

#eval (augmentationsFinal 2 A63) -- returns (to long to comment)

#eval (augmentationsFinal 4 A73) -- returns (to long to comment)

#eval (augmentationsFinal 2 A84).length -- returns 1855

#eval (augmentationsFinal 4 A63) -- returns (to long to comment)

#eval D1.matroid.join -- returns [1, 3, 5, 0, 3, 4, 0, 1, 2]
