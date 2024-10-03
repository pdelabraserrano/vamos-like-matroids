import Matroids.MainComputation

/-! # Running the main computation

This file runs the main computation of the project, producing a list of the "Vámos-like" matroids.
(There should be 39 of them, and the `#guard_msgs` command will fail if this is not the case.)

 -/

-- Invariant 1 & 2: 23.8 seconds
-- New time (Invariant 1, 2, 3): 10.1 seconds

/-- info: 39 -/
#guard_msgs in
#eval mainComputation.length
