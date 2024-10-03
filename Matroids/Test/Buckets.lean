import Matroids.AllPossibilities
import Matroids.Buckets
import Matroids.Test.PartialMatroid

open PartialMatroid


abbrev A73Bucket := (augmentationsFinal 4 A73).map findBucket

#eval A73Bucket -- returns (to long to comment)

abbrev A73BucketSorted := A73Bucket.sort

/-- info: [210, 840, 1260] -/
#guard_msgs in
#eval count A73BucketSorted

#eval A73BucketSorted -- returns (to long to comment)

#eval ((augmentationsFinal 4 A73).map findBucket) -- returns (to long to comment)

/-- info: [35, 560, 1260] -/
#guard_msgs in
#eval countBuckets (augmentationsFinal 2 A84)

-- (augmentationsFinal 4 A73) -> How many combinations of 4 triangles (3) can we make with seven points
/-- info: [210, 840, 1260] -/
#guard_msgs in
#eval countBuckets (augmentationsFinal 4 A73)

/-- info: [420, 630] -/
#guard_msgs in
#eval countBuckets (augmentationsFinal 5 A73)

#eval groupByBucket (augmentationsFinal 4 A73) -- returns (to long to comment)

#eval groupByValue ((augmentationsFinal 4 A73).mergeSort (fun l1 l2 => findBucket l1 < findBucket l2)) findBucket -- returns (to long to comment)

-- To find where a list begins and ends simply cmd + f "}]"
#eval groupByBucket (augmentationsFinal 4 A73) -- returns (to long to comment)

-- Test with six points, 4 triangles
abbrev A63Bucket := (augmentationsFinal 4 A63).map findBucket

#eval A63Bucket -- returns (to long to comment)

abbrev A63BucketSorted := A63Bucket.sort

/-- info: [30] -/
#guard_msgs in
#eval count A63BucketSorted

#eval A63BucketSorted -- returns (to long to comment)

#eval groupByBucket (augmentationsFinal 4 A63) -- returns (to long to comment)

abbrev FourTrianglesOnSixPoints := groupByBucket (augmentationsFinal 4 A63)

#eval List.pairs [1, 2, 3, 4]

#eval complementAux [1,2,3,4] [0,1,2,3,4,5,6,7]

#eval complement [[0,1,2,3],[0,1,6,7],[1,2,6,7]]

#eval isMember 2 [1,3,4]
