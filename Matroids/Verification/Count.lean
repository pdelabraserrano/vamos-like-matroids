import Matroids.Verification.Basic
import Matroids.Count
import Matroids.PartialMatroid

/- Lemma for count (related to Theorem 1):  If the input is an list of partial matroids
(order does matter, for both the lists and for the members) with range i < n and lenght = r, then
the output will be a list of natural numbers that counts the single ocurrences of lawful sparse
paving matroids-/

#eval count ([[0, 1], [0, 1], [1, 0], [0, 1, 3,2], [0, 1, 9], [0, 1], [0,2]]) /- Note, this is not
a list of partial matroids-/

lemma forall_groupByValueAux (f : α → List ℕ) (A : List α) (hA : A.Forall P) :
    (groupByValueAux f A).1.Forall P ∧ (groupByValueAux f A).2.Forall (fun l ↦ l.Forall P) := by
  match A with
  | [] => simp [groupByValueAux]
  | [pm] =>
    simp [groupByValueAux]
    apply hA
  | a :: b :: t =>
    simp [groupByValueAux]
    simp at hA
    obtain ⟨h_ok, t_ok⟩ := hA
    obtain ⟨th_ok, tt_ok⟩ := t_ok
    have H := forall_groupByValueAux f (b :: t) (P := P)
    have tt_ok1 : List.Forall P (b :: t)
    · simp
      constructor
      · exact th_ok
      · exact tt_ok
    apply H at tt_ok1
    obtain ⟨tth_ok1, ttt_ok1⟩ := tt_ok1
    constructor
    . split_ifs
      · simp
        constructor
        · exact h_ok
        · apply tth_ok1
      · simp
        exact h_ok
    · split_ifs
      · simp
        exact ttt_ok1
      · simp
        constructor
        · apply tth_ok1
        · exact ttt_ok1


/- If the operation `groupByValue` is performed on a list of objects of type `α`, all of which have
a certain property `P`, then the objects of type `α`'s in the output list of lists will all have
poperty `P`.
(will probably get used for Theorem 1) -/
lemma forall_groupByValue (f : α → List ℕ) (A : List α) (hA : A.Forall P) :
    (groupByValue A f).Forall (fun l ↦ l.Forall P) := by
  unfold groupByValue
  simp
  apply forall_groupByValueAux
  exact hA
