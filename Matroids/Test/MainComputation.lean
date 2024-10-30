import Matroids.MainComputation

/-! # Running the main computation

This file runs the main computation of the project, producing a list of the "Vámos-like" matroids.
(There should be 39 of them, and the `#guard_msgs` command will fail if this is not the case.)
maxHeartbeats 30000 limits the number of steps this computation can perform. Will throw an error if
it goes above that number

 -/

-- Invariant 1 & 2: 23.8 seconds
-- New time (Invariant 1, 2, 3): 10.1 seconds

/-- info: 39 -/
#guard_msgs in
set_option maxHeartbeats 30000 in
#eval mainComputation.length
