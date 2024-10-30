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

lemma groupBySecondInvariant_lawful (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (llA.map groupBySecondInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid) := by
  unfold groupBySecondInvariant
  apply List.Forall.join
  rw [List.forall_iff_forall_mem]
  intro llB hllB
  rw[List.mem_map] at hllB
  obtain ⟨lB, hlB⟩ := hllB
  obtain ⟨hlB1, hlB2⟩ := hlB
  rw [←hlB2] at *
  apply forall_groupByValue
  rw [List.forall_iff_forall_mem]
  intro C hC
  apply List.reverse_mem_mergeSort at hC
  rw [List.forall_iff_forall_mem] at *
  apply hllA at hlB1
  rw [List.forall_iff_forall_mem] at hlB1
  apply hlB1 at hC
  apply hC

lemma groupByThirdInvariant_lawful (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (llA.map groupByThirdInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid) := by
  unfold groupByThirdInvariant
  apply List.Forall.join
  rw [List.forall_iff_forall_mem]
  intro llB hllB
  rw[List.mem_map] at hllB
  obtain ⟨lB, hlB⟩ := hllB
  obtain ⟨hlB1, hlB2⟩ := hlB
  rw [←hlB2] at *
  apply forall_groupByValue
  rw [List.forall_iff_forall_mem]
  intro C hC
  apply List.reverse_mem_mergeSort at hC
  rw [List.forall_iff_forall_mem] at *
  apply hllA at hlB1
  rw [List.forall_iff_forall_mem] at hlB1
  apply hlB1 at hC
  apply hC


/-- If `A` is a list of `PartialMatroid`s, all of which are valid (n, r)-sparse paving matroids,
then when the `groupByBucket` operation is performed, every `PartialMatroid` in the the resulting
list of list of partial matroids is still a valid (n, r)-sparse paving matroids. -/
lemma groupByBucket_lawful (lA : List PartialMatroid)
    (hA : lA.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (groupByBucket lA).Forall
    (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
  unfold groupByBucket
  apply groupByThirdInvariant_lawful
  apply groupBySecondInvariant_lawful
  apply groupByFirstInvariant_lawful
  apply hA

lemma groupByFirstInvariant_normalized (lA : List PartialMatroid)
    (hlA : lA.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (groupByFirstInvariant lA).Forall
    (fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) := by
   unfold groupByFirstInvariant
   apply forall_groupByValue
   apply List.forall_mergeSort
   apply hlA


lemma groupBySecondInvariant_normalized (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (llA.map groupBySecondInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  unfold groupBySecondInvariant
  apply List.Forall.join
  rw [List.forall_iff_forall_mem]
  intro llB hllB
  rw[List.mem_map] at hllB
  obtain ⟨lB, hlB⟩ := hllB
  obtain ⟨hlB1, hlB2⟩ := hlB
  rw [←hlB2] at *
  apply forall_groupByValue
  rw [List.forall_iff_forall_mem]
  intro C hC
  apply List.reverse_mem_mergeSort at hC
  rw [List.forall_iff_forall_mem] at *
  apply hllA at hlB1
  rw [List.forall_iff_forall_mem] at hlB1
  apply hlB1 at hC
  apply hC

lemma groupByThirdInvariant_normalized (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (llA.map groupByThirdInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  unfold groupByThirdInvariant
  apply List.Forall.join
  rw [List.forall_iff_forall_mem]
  intro llB hllB
  rw[List.mem_map] at hllB
  obtain ⟨lB, hlB⟩ := hllB
  obtain ⟨hlB1, hlB2⟩ := hlB
  rw [←hlB2] at *
  apply forall_groupByValue
  rw [List.forall_iff_forall_mem]
  intro C hC
  apply List.reverse_mem_mergeSort at hC
  rw [List.forall_iff_forall_mem] at *
  apply hllA at hlB1
  rw [List.forall_iff_forall_mem] at hlB1
  apply hlB1 at hC
  apply hC

lemma groupByBucket_normalized (lA : List PartialMatroid)
    (hlA : lA.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (groupByBucket lA).Forall
    (fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) := by
    unfold groupByBucket
    apply groupByThirdInvariant_normalized
    apply groupBySecondInvariant_normalized
    apply groupByFirstInvariant_normalized
    apply hlA




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
