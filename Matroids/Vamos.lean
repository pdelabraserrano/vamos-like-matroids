import Matroids.PartialMatroid

open PartialMatroid

/-! # Code to ---

This file provides functions ----

## Main definitions

* `Vamos`: THE Vamos matroid put within the partial matriod structure (because it is a partial
matroid)
-/

abbrev Vamos : PartialMatroid where
  matroid := [[0,1,2,3], [0,1,4,5], [0,1,6,7], [2,3,4,5], [2,3,6,7]]
  -- should redo
  remainingOptions := [--[0, 1, 2, 4],
                       --[0, 1, 3, 4],
                       --[0, 2, 3, 4],
                       --[1, 2, 3, 4],
                       --[0, 1, 2, 5],
                       --[0, 1, 3, 5],
                       --[0, 2, 3, 5],
                       --[1, 2, 3, 5],
                       --[0, 1, 4, 5],
                       --[0, 2, 4, 5],
                       --[1, 2, 4, 5],
                       --[0, 3, 4, 5],
                       --[1, 3, 4, 5],
                       --[2, 3, 4, 5],
                       --[0, 1, 2, 6],
                       --[0, 1, 3, 6],
                       --[0, 2, 3, 6],
                       --[1, 2, 3, 6],
                       --[0, 1, 4, 6],
                       [0, 2, 4, 6],
                       [1, 2, 4, 6],
                       [0, 3, 4, 6],
                       [1, 3, 4, 6],
                       --[2, 3, 4, 6],
                       --[0, 1, 5, 6],
                       [0, 2, 5, 6],
                       [1, 2, 5, 6],
                       [0, 3, 5, 6],
                       [1, 3, 5, 6],
                       --[2, 3, 5, 6],
                       --[0, 4, 5, 6],
                       --[1, 4, 5, 6],
                       --[2, 4, 5, 6],
                       --[3, 4, 5, 6],
                       --[0, 1, 2, 7],
                       --[0, 1, 3, 7],
                       --[0, 2, 3, 7],
                       --[1, 2, 3, 7],
                       --[0, 1, 4, 7],
                       [0, 2, 4, 7],
                       [1, 2, 4, 7],
                       [0, 3, 4, 7],
                       [1, 3, 4, 7],
                       --[2, 3, 4, 7],
                       --[0, 1, 5, 7],
                       [0, 2, 5, 7],
                       [1, 2, 5, 7],
                       [0, 3, 5, 7],
                       [1, 3, 5, 7],
                       --[2, 3, 5, 7],
                       --[0, 4, 5, 7],
                       --[1, 4, 5, 7],
                       --[2, 4, 5, 7],
                       --[3, 4, 5, 7],
                       --[0, 1, 6, 7],
                       --[0, 2, 6, 7],
                       --[1, 2, 6, 7],
                       --[0, 3, 6, 7],
                       --[1, 3, 6, 7],
                       --[2, 3, 6, 7],
                       --[0, 4, 6, 7],
                       --[1, 4, 6, 7],
                       --[2, 4, 6, 7],
                       --[3, 4, 6, 7],
                       --[0, 5, 6, 7],
                       --[1, 5, 6, 7],
                       --[2, 5, 6, 7],
                       --[3, 5, 6, 7],
                       --[4, 5, 6, 7]
                       ]
