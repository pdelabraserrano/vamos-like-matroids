import Matroids.AllPossibilities
open PartialMatroid

#eval [1,1,1,2,2,2,3] < [1,1,2,2,2,2] -- returns true

#eval [1,1,2,2,2,2] < [2,2,2,2,2,2] -- returns true

-- #eval D1 -- returns { matroid := [[1, 3, 5], [0, 3, 4], [0, 1, 2]], remainingOptions := [] }

#eval augmentations D1 -- returns []

#eval augmentationsTwo D1 -- returns []

#eval augmentationsThree D1 -- returns []

#eval augmentationsFour D1 -- returns []

#eval augmentationsFive D1 -- returns []

#eval (augmentationsFinal 3 E1) -- returns []

#eval (augmentationsFinal 4 A73) -- returns (to long to comment)

#eval (augmentationsFinal 4 A63) -- returns (to long to comment)

#eval (augmentationsFinal 4 A73) -- returns (to long to comment)

#eval (augmentationsFinal 2 A84).length -- returns 1855

#eval (augmentationsFinal 4 A63) -- returns (to long to comment)

#eval D1.matroid.join -- returns [1, 3, 5, 0, 3, 4, 0, 1, 2]

#eval fact 7 -- returns 5040

abbrev A73Bucket := (augmentationsFinal 4 A73).map findBucket

#eval A73Bucket -- returns (to long to comment)

abbrev A73BucketSorted := A73Bucket.sort

#eval count A73BucketSorted -- returns [210, 840, 1260]

#eval A73BucketSorted -- returns (to long to comment)

#eval ((augmentationsFinal 4 A73).map findBucket) -- returns (to long to comment)

#eval countBuckets (augmentationsFinal 2 A84) -- returns [35, 560, 1260]

-- (augmentationsFinal 4 A73) -> How many combinations of 4 triangles (3) can we make with seven points
#eval countBuckets (augmentationsFinal 4 A73) -- returns [210, 840, 1260]

#eval countBuckets (augmentationsFinal 5 A73) -- returns [420, 630]

#eval groupByBucket (augmentationsFinal 4 A73) -- returns (to long to comment)

#eval groupByValue ((augmentationsFinal 4 A73).mergeSort (fun l1 l2 => findBucket l1 < findBucket l2)) findBucket -- returns (to long to comment)

-- To find where a list begins and ends simply cmd + f "}]"
#eval groupByBucket (augmentationsFinal 4 A73) -- returns (to long to comment)

-- Test with six points, 4 triangles
abbrev A63Bucket := (augmentationsFinal 4 A63).map findBucket

#eval A63Bucket -- returns (to long to comment)

abbrev A63BucketSorted := A63Bucket.sort

#eval count A63BucketSorted -- returns [30]

#eval A63BucketSorted -- returns (to long to comment)

#eval groupByBucket (augmentationsFinal 4 A63) -- returns (to long to comment)

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

abbrev FourTrianglesOnSixPoints := groupByBucket (augmentationsFinal 4 A63)
abbrev Vamos7 := groupByBucket (augmentationsFinal 7 Vamos)
abbrev Vamos1 := groupByBucket (augmentationsFinal 1 Vamos)


#check Vamos7
#eval Vamos7.head!
