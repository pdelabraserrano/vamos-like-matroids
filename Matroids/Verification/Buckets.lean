import Matroids.Verification.Basic
import Matroids.Buckets
import Matroids.Verification.Relabelling
import Matroids.Verification.Count

open PartialMatroid

lemma List.forall_mergeSort (r : α → α → Prop) [DecidableRel r] {l : List α} {P : α → Prop }
  (h : l.Forall P) : (l.mergeSort (r)).Forall P := by
    rw [List.forall_iff_forall_mem]
    intro i hi
    rw [List.forall_iff_forall_mem] at h
    apply h
    rw[List.Perm.mem_iff]
    sorry
    sorry
    apply l

/-- If `A` is a list of `PartialMatroid`s, all of which are valid (n, r)-sparse paving matroids,
then when the `groupByBucket` operation is performed, every `PartialMatroid` in the the resulting
list of list of partial matroids is still a valid (n, r)-sparse paving matroids. -/
lemma groupByBucket_lawful (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (groupByBucket A).Forall
    (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
  unfold groupByBucket
  apply groupByValue_lawful
  apply List.forall_mergeSort
  apply hA






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
