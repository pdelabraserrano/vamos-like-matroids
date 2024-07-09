import Matroids.Buckets
import Matroids.Relabelling
import Matroids.Vamos
import Matroids.AllPossibilities

/-! # Code to ---

This file provides functions ----

## Main definitions

* `mainComputation`: ---
-/

/-- take the augmentations by `i` quadrangles of the Vamos sparse paving matroid, and group
("bucket") by basic numeric statistics -/
def augmentedVamos (i : ℕ) : List (List PartialMatroid) :=
  PartialMatroid.groupByBucket (PartialMatroid.augmentationsFinal i Vamos)

/-- eliminate duplicates within each bucket -/
irreducible_def prunedVamos (i : ℕ) : List (List PartialMatroid) := (augmentedVamos i).map pruning

/-- concatenate buckets and then concatenate over all `i` -/
def joinedPrunedVamos : List PartialMatroid :=
  ((List.range 9).map fun i ↦ (prunedVamos i).join).join

/-- forget the information about what more could be augmented to each and just present the
quadrangle information -/
def mainComputation : List (List (List ℕ)) :=
  joinedPrunedVamos.map PartialMatroid.matroid
