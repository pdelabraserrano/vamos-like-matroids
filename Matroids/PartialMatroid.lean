import Matroids.NearlySame

/-! # Code to create a PartialMatroid structure and

This file provides functions to set up the basic partial matroid structure, and automatically update
the set of remaining options every time we add another figure to the partial matroid by eliminating
any remainng options that become unqualified to be augmented into the partial matroid. Al

## Main definitions

* `PartialMatroid`: sets up the structure of partial matroid: showing the partial matroid and its
remaining options.
* `elimSmaller`: Seeks to make sure that we do not identify partial matroids with different orders
but same set of augments from the remaining options as different.
* `augment`: adds figures to partial matroids and eliminates from remaining options
-/

structure PartialMatroid where
  matroid : List (List Nat)
  remainingOptions : List (List Nat)
  deriving Repr

namespace PartialMatroid

/-- Goes through the remaining options and ensures that we add new things in an increasing
order Eg. keeps (x,y,z) eliminates (y,x,z). This is used to conserve computing power later on when
checking for repeat partial matroids-/
def elimSmaller (l : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | h1 :: t1 =>
    if h1 > l then
      elimSmaller l t1
    else
      h1 :: elimSmaller l t1

/--Adds an additional figure to the partial matroid and then eliminates any figure/option from the
remaining options that share all or all but one point with the figure that was just added -/
def augment (l : List Nat) (M : PartialMatroid) : PartialMatroid :=
  -- if !(l ∈ M.remainingOptions) then fail "can't add this" else
  { matroid := l :: M.matroid, remainingOptions := elimSmaller l (elimNearlySame l M.remainingOptions) }

-- old version with duplication
  -- { matroid := l :: M.matroid, remainingOptions := elimNearlySame l M.remainingOptions }
