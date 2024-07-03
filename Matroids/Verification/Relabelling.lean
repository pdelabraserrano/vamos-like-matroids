import Matroids.Verification.Basic
import Matroids.Relabelling

/-- If `A` is a list of `PartialMatroid`s, all of which are valid (n, r)-sparse paving matroids,
then when the `pruning` operation is performed, every `PartialMatroid` in the the resulting
list of partial matroids is still a valid (n, r)-sparse paving matroids. -/
lemma pruning_lawful (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (pruning A).Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid) := by
  induction A with
  | nil => simp
  | cons h t IH =>
    simp at hA
    obtain ⟨h_ok, t_ok⟩ := hA
    apply IH at t_ok
    simp [pruning]
    split_ifs
    · exact t_ok
    · simp
      constructor
      · exact h_ok
      · exact t_ok

/-- If `A` is a list of `PartialMatroid`s, all of which are valid (n, r)-sparse paving matroids,
then when the `pruning` operation is performed, every `PartialMatroid` in `A` is isomorphic (up to
permutation of 0, 1, 2, ... n - 1) to one of the `PartialMatroid`s in the pruned list. -/
theorem permutationsComparison_mem_pruning_of_mem {A : List PartialMatroid}
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    A.Forall fun M ↦ ∃ M' ∈ pruning A, permutationsComparison n M.matroid M'.matroid := by
  sorry
