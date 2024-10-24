import Matroids.Verification.Basic
import Matroids.Buckets
import Matroids.Verification.Relabelling
import Matroids.Verification.Count
import Matroids.Verification.Miscellaneous

open PartialMatroid


lemma groupByFirstInvariant_lawful (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (groupByFirstInvariant A).Forall
    (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
      unfold groupByFirstInvariant
      apply forall_groupByValue
      apply List.forall_mergeSort
      apply hA

lemma groupBySecondInvariant_lawful (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (groupBySecondInvariant A).Forall
    (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
      unfold groupBySecondInvariant
      apply forall_groupByValue
      apply List.forall_mergeSort
      apply hA

lemma groupByThirdInvariant_lawful (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (groupByThirdInvariant A).Forall
    (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
      unfold groupByThirdInvariant
      apply forall_groupByValue
      apply List.forall_mergeSort
      apply hA


/-- If `A` is a list of `PartialMatroid`s, all of which are valid (n, r)-sparse paving matroids,
then when the `groupByBucket` operation is performed, every `PartialMatroid` in the the resulting
list of list of partial matroids is still a valid (n, r)-sparse paving matroids. -/
lemma groupByBucket_lawful (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (groupByBucket A).Forall
    (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
  unfold groupByBucket
  apply List.Forall.join
  rw [List.forall_map_iff]
  rw [List.forall_iff_forall_mem]
  intro q hq
  apply groupByThirdInvariant_lawful
  simp at hq
  obtain hhq | qhq := hq
  · rw [List.forall_iff_forall_mem]
    intro w hw
    unfold groupBySecondInvariant at hhq
    simp[groupByValue] at hhq
    obtain hhqh | hhqq := hhq
    · sorry
    --apply groupByFirstInvariant_lawful at hhq
    --apply hw at hhq
    --rw [pruning_lawful] at hhq
    sorry
  · rw [List.forall_iff_forall_mem]
    obtain ⟨ qqhq, qhqq, qhqqq ⟩ := qhq
    intro p hp

    sorry

lemma groupByFirstInvariant_normalized (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (groupByFirstInvariant A).Forall
    (fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) := by
   unfold groupByFirstInvariant
   apply forall_groupByValue
   apply List.forall_mergeSort
   apply hA


lemma groupBySecondInvariant_normalized (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (llA.map groupBySecondInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  unfold groupBySecondInvariant
  apply List.Forall.join
  sorry

lemma groupByThirdInvariant_normalized (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (llA.map groupByThirdInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  unfold groupByThirdInvariant
  sorry

lemma groupByBucket_normalized (lA : List PartialMatroid)
    (hlA : lA.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (groupByBucket lA).Forall
    (fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) := by
    unfold groupByBucket
    rw [List.forall_map_iff]
    rw [List.forall_iff_forall_mem]
    intro lB hlB
    apply groupByThirdInvariant_normalized
    apply groupBySecondInvariant_normalized
    rw [List.forall_iff_forall_mem]
    intro B hB
    have := groupByFirstInvariant_normalized lA
    simp_rw [List.forall_iff_forall_mem] at *
    apply this
    apply hlA
    apply hlB
    apply hB



/- Lemma for countBuckets (related to Theorem 1): If the input is an list partial matroids
(order does matter, for both the lists and for the members) with range i < n and lenght = r, then
the output will be a lawful sparse paving matroid -/
/- After rethinking, we might not need to prove anything about countBuckets since it is not used
directly in the main computation.-/

/-- For all partial matroids in a bucket, they do not exist in other buckets even as permutations of
partial matroids.
(will probably get used for Theorem 3) -/
lemma nonisomorphic_groupByBucket (A : List PartialMatroid) :
    (groupByBucket A).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ ¬ permutationsComparison 8 M₁.matroid M₂.matroid :=
  sorry
