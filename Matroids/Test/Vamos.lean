import Matroids.Buckets
import Matroids.Vamos
import Matroids.AllPossibilities
import Matroids.Relabelling

open PartialMatroid


#eval Vamos

#eval groupByBucket (augmentationsFinal 5 Vamos) -- returns (to long to comment)

#eval countBuckets (augmentationsFinal 8 Vamos)--2
#eval countBuckets (augmentationsFinal 7 Vamos)--16
#eval countBuckets (augmentationsFinal 6 Vamos) -- 8,8,8,32
#eval countBuckets (augmentationsFinal 5 Vamos) --32,32,64
#eval countBuckets (augmentationsFinal 4 Vamos) -- 8, 8, 16, 16, 16, 32, 32, 36, 64
#eval countBuckets (augmentationsFinal 3 Vamos) --32, 32, 144
#eval countBuckets (augmentationsFinal 2 Vamos) --8, 8, 8, 16, 16, 32
#eval countBuckets (augmentationsFinal 1 Vamos) --16
#eval countBuckets (augmentationsFinal 0 Vamos) --1

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

#time
#eval List.sum (Vamos3.map sizeOfPrunedBucket)

#exit

#time -- 0.018 sec
#eval List.sum (Vamos0.map sizeOfPrunedBucket) -- returns [1] -- 1

#time -- 49.753 sec
#eval List.sum (Vamos1.map sizeOfPrunedBucket) -- returns [1] -- + 1 = 2

#time --339.491 sec / 6 min
#eval List.sum (Vamos2.map sizeOfPrunedBucket) -- returns [1, 1, 1, 1, 1, 1] -- + 6 = 8

#time -- 3538.507 sec / 1hr
#eval (Vamos3.map sizeOfPrunedBucket) -- returns [1, 1, 5] -- + 7 = 15

#time -- 1471.504 sec / 25 min
#eval (Vamos4.map sizeOfPrunedBucket) -- returns [1, 1, 1, 1, 1, 1, 1, 1, 5] -- + 13 = 28

#time -- 1016.151 sec / 17 min
#eval (Vamos5.map sizeOfPrunedBucket) -- returns [1, 1, 3] -- + 5 = 33

#time -- 301.063 sec / 5 min
#eval (Vamos6.map sizeOfPrunedBucket) -- returns [1, 1, 1, 1] -- + 4 = 37

#time -- 97.294 sec / 1.5 min
#eval (Vamos7.map sizeOfPrunedBucket) -- returns [1] -- + 1 = 38

#time -- 7.426 sec
#eval (Vamos8.map sizeOfPrunedBucket) -- returns [1] -- + 1 = 39 (desired result)

#eval Vamos7.head!
