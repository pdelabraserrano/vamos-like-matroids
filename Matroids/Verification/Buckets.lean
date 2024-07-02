import Matroids.Verification.Basic
import Matroids.Buckets

/-- If `A` is a list of `PartialMatroid`s, all of which are valid (n, r)-sparse paving matroids,
then when the `groupByBucket` operation is performed, every `PartialMatroid` in the the resulting
list of list of partial matroids is still a valid (n, r)-sparse paving matroids. -/
lemma groupByBucket_lawful (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (PartialMatroid.groupByBucket A).Forall
      (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :=
  sorry
