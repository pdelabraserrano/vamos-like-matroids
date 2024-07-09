import Matroids.Verification.Basic
import Matroids.Count
import Matroids.PartialMatroid

/- Lemma for count (related to Theorem 1):  If the input is an list of partial matroids
(order does matter, for both the lists and for the members) with range i < n and lenght = r, then
the output will be a list of natural numbers that counts the single ocurrences of lawful sparse
paving matroids-/

#eval count ([[0, 1], [0, 1], [1, 0], [0, 1, 3,2], [0, 1, 9], [0, 1], [0,2]]) /- Note, this is not
a list of partial matroids-/

lemma groupByValueAux_lawful (f: PartialMatroid → List ℕ) (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)):
    (groupByValueAux f A).1.Forall  (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)
     ∧  (groupByValueAux f A).2.Forall (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
     unfold groupByValueAux
     sorry


/- If the operation `groupByValue` is performed on a list of `PartialMatroids` which are valid
(n, r) sparse paving matroids then the `PartialMatroid`s in the output list of lists will all be
valid (n, r) sparse paving matroids.
(will probably get used for Theorem 1) -/
lemma groupByValue_lawful (f : PartialMatroid → List ℕ) (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (groupByValue A f).Forall
    (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
  unfold groupByValue
  simp
  apply groupByValueAux_lawful
  exact hA
