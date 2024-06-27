import Matroids.Relabelling
import Matroids.AllPossibilities

open List
open PartialMatroid

abbrev Vamos0 := groupByBucket (augmentationsFinal 0 Vamos)
abbrev Vamos1 := groupByBucket (augmentationsFinal 1 Vamos)
abbrev Vamos2 := groupByBucket (augmentationsFinal 2 Vamos)
abbrev Vamos3 := groupByBucket (augmentationsFinal 3 Vamos)
abbrev Vamos4 := groupByBucket (augmentationsFinal 4 Vamos)
abbrev Vamos5 := groupByBucket (augmentationsFinal 5 Vamos)
abbrev Vamos6 := groupByBucket (augmentationsFinal 6 Vamos)
abbrev Vamos7 := groupByBucket (augmentationsFinal 7 Vamos)
abbrev Vamos8 := groupByBucket (augmentationsFinal 8 Vamos)

#check Vamos0

#time -- 0.018 s
#eval (Vamos3.map sizeOfPrunedBucket) -- returns [1]

#exit

#time -- 0.018 s
#eval (Vamos0.map sizeOfPrunedBucket) -- returns [1]

#time -- 49.753 sec
#eval (Vamos1.map sizeOfPrunedBucket) -- returns [1]

#time --339.491 sec
#eval (Vamos2.map sizeOfPrunedBucket) -- returns [1, 1, 1, 1, 1, 1]

#eval Vamos7.head!
