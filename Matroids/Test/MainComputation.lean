import Matroids.MainComputation

/-! # Running the main computation

This file runs the main computation of the project, producing a list of the "Vámos-like" matroids.
(There should be 39 of them, and the `#guard_msgs` command will fail if this is not the case.)

This file takes a *long* time to run, about 2 hours.  It is deliberately not included in a standard
build of the project. -/

/-- info: 39 -/
#guard_msgs in
#eval mainComputation.length
