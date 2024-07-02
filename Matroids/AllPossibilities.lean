import Matroids.PartialMatroid

/-! # Code to ---

This file provides functions begin adding things from the remaining options. It only produces
qualified partial matroids. From here, we still need to check whether or not there are repeat
partial matroids

## Main definitions

* `augmentations`: augments elements from remaining options (only one at a time); utilizes `augment`
* `augmentationsFinal`: allows us to augment a set number of things from remaining options. Finds
all combinations of size n to augment to the partial matroid; utilizes `augmentations `
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
