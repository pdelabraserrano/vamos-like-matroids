import Matroids.AllPossibilities
import Matroids.Verification.Basic

open PartialMatroid

lemma augmentationsFinal_lawful (i : ℕ) (M : PartialMatroid)
    (hM : LawfulSparsePavingMatroid n r M.matroid)
    (remainingOptions_mem_range : M.remainingOptions.Forall (List.Forall fun i ↦ i < n))
    (remainingOptions_length_eq_rank : M.remainingOptions.Forall (fun l ↦ l.length = r))
    (remainingOptions_sorted_of_mem : ∀ m ∈ M.remainingOptions, m.Sorted (· < ·))
    -- (remainingOptions_sorted : M.remainingOptions.Sorted (· < ·))
    (remainingOptions_not_nearlySame : ∀ l₁ ∈ M.matroid, ∀ l₂ ∈ M.remainingOptions, ¬ NearlySame l₁ l₂) :
    (augmentationsFinal i M).Forall (fun M' ↦ LawfulSparsePavingMatroid n r M'.matroid) :=
  sorry
