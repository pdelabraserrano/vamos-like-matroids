import Matroids.PartialMatroid

/-! # Code to ---

This file provides functions ----

## Main definitions

* `augmentations`: ---
* `augmentationsFinal`: ---
-/

namespace PartialMatroid

/-- all the partial matroids which can be obtained by adding one figure to the
partial matroid A. Looks at the possibilities from remaining options and adds one more. -/
def augmentations (A : PartialMatroid) : List PartialMatroid := A.remainingOptions.map  (augment · A)


/-- Function that allows us to see all the partial matroids possible when we want to add x figures.
Takes in a natural number x and a partial matroid containing remaning options. -/
def augmentationsFinal : Nat → PartialMatroid → List PartialMatroid
   | 0, A => [A]
   | n + 1, A =>
      let addNEdges : PartialMatroid → List PartialMatroid := augmentationsFinal n
      ((augmentations A).map addNEdges).join
