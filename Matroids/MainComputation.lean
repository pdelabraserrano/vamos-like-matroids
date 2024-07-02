import Matroids.Buckets
import Matroids.Relabelling
import Matroids.Vamos
import Matroids.AllPossibilities

/-! # Code to ---

This file provides functions ----

## Main definitions

* `mainComputation`: ---
-/

irreducible_def mainComputation : List (List (List ℕ)) :=
  -- take the augmentations by `i` quadrangles of the Vamos sparse paving matroid, and group
  --("bucket") by basic numeric statistics
  let Vamos (i : ℕ) : List (List PartialMatroid) :=
    PartialMatroid.groupByBucket (PartialMatroid.augmentationsFinal i Vamos)
  -- eliminate duplicates within each bucket
  let prunedVamos (i : ℕ) : List (List PartialMatroid) := (Vamos i).map pruning
  -- concatenate buckets and then concatenate over all `i`
  let joinedPrunedVamos : List PartialMatroid :=
    ((List.range 9).map fun i ↦ (prunedVamos i).join).join
  -- forget the information about what more could be augmented to each and just present the
  -- quadrangle information
  joinedPrunedVamos.map PartialMatroid.matroid
