import Matroids.PartialMatroid
import Matroids.Verification.Basic
import Matroids.Verification.Miscellaneous

open PartialMatroid

lemma augment_lawful (l : List Nat) (A : PartialMatroid)
  (hA : LawfulSparsePavingMatroid n r A.matroid)
  (remainingOptions_mem_range : A.remainingOptions.Forall (List.Forall fun j ↦ j < n))
  (remainingOptions_length_eq_rank : A.remainingOptions.Forall (fun l ↦ l.length = r))
  (remainingOptions_sorted_of_mem : A.remainingOptions.Forall fun m ↦ m.Sorted (· < ·)) :
   LawfulSparsePavingMatroid n r A.matroid := by
    sorry


lemma augment_notAdding (l : List Nat) (A : PartialMatroid) :
    ∀ k, k ∈ (augment l A).remainingOptions → k ∈ A.remainingOptions := by
  sorry
