import Matroids.AllPossibilities
import Matroids.Test.PartialMatroid
open PartialMatroid

/-- info: true -/
#guard_msgs in
#eval [1,1,1,2,2,2,3] < [1,1,2,2,2,2]


/-- info: true -/
#guard_msgs in
#eval [1,1,2,2,2,2] < [2,2,2,2,2,2]


def augmentationsTwo (A : PartialMatroid) : List PartialMatroid :=
  ((augmentations A).map augmentations).join

def augmentationsThree (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsTwo).join

def augmentationsFour (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsThree).join

def augmentationsFive (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsFour).join

/-- info: { matroid := [[0, 1, 2], [0, 3, 4], [1, 3, 5]], remainingOptions := [] } -/
#guard_msgs in
#eval D1

/-- info: [] -/
#guard_msgs in
#eval augmentations D1

/-- info: [] -/
#guard_msgs in
#eval augmentationsTwo D1

/-- info: [] -/
#guard_msgs in
#eval augmentationsThree D1

#eval augmentationsFour D1 -- returns []

#eval augmentationsFive D1 -- returns []

/-- info: [] -/
#guard_msgs in
#eval (augmentationsFinal 3 E1)

#eval (augmentationsFinal 4 A73) -- returns (to long to comment)

#eval (augmentationsFinal 2 A63) -- returns (to long to comment)

#eval (augmentationsFinal 4 A73) -- returns (to long to comment)

/-- info: 1855 -/
#guard_msgs in
#eval (augmentationsFinal 2 A84).length

#eval (augmentationsFinal 4 A63) -- returns (to long to comment)

/-- info: [0, 1, 2, 0, 3, 4, 1, 3, 5] -/
#guard_msgs in
#eval D1.matroid.join
