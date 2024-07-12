import Matroids.AllPossibilities
import Matroids.Verification.Basic

open PartialMatroid

lemma augmentationsFinal_lawful (i : ℕ) (M : PartialMatroid)
    (hM : LawfulSparsePavingMatroid n r M.matroid)
    (remainingOptions_mem_range : M.remainingOptions.Forall (List.Forall fun i ↦ i < n))
    (remainingOptions_length_eq_rank : M.remainingOptions.Forall (fun l ↦ l.length = r))
    (remainingOptions_sorted_of_mem : M.remainingOptions.Forall fun m ↦ m.Sorted (· < ·))
    -- (remainingOptions_sorted : M.remainingOptions.Sorted (· < ·))
    (remainingOptions_not_nearlySame :
      M.matroid.Forall fun l₁ ↦ M.remainingOptions.Forall fun l₂ ↦ ¬ NearlySame l₁ l₂) :
    (augmentationsFinal i M).Forall (fun M' ↦ LawfulSparsePavingMatroid n r M'.matroid) := by
      unfold augmentationsFinal
      match i, M with
      | 0, A => simp [hM]
      | N + 1, A =>
        simp [augmentationsFinal]
        rw [List.forall_iff_forall_mem]
        intro a ha
        sorry
