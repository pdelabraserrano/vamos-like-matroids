import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Notation

variable {α β : Type*}

@[simp] theorem Matrix.cons_val_three {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ → α) :
    vecCons x u 3 = vecHead (vecTail (vecTail u)) :=
  rfl

/-- Map a partially-defined (i.e. dependent) function `f` over a list, if the dependency is
satisfied for every element of the list. -/
def List.dependentMap {P : α → Prop} (f : ∀ a, P a → β) : ∀ (l : List α), l.Forall P → List β
  | [], _ => []
  | h :: t, hl =>
    let hl' : _ ∧ _ := (List.forall_cons _ _ _).1 hl
    f h hl'.1 :: dependentMap f t hl'.2


lemma List.forall_append_iff {L1 L2 : List α} {P : α → Prop} :
     List.Forall P (L1 ++ L2) ↔ (List.Forall P L1) ∧ (List.Forall P L2) := by
  induction L1 with
  | nil =>
    simp
  | cons h t IH =>
    simp
    constructor
    · intro h1
      obtain ⟨th1, hh1⟩ := h1
      obtain ⟨IH1, _⟩ := IH
      apply IH1 at hh1
      obtain ⟨thh1, hhh1⟩ := hh1
      constructor
      · constructor
        · exact th1
        · exact thh1
      · exact hhh1
    · intro h1
      obtain ⟨th1, hh1⟩ := h1
      obtain ⟨_, IH2⟩ := IH
      obtain ⟨tth1, hth1⟩ := th1
      constructor
      · exact tth1
      · apply IH2
        constructor
        · exact hth1
        · exact hh1


lemma List.Forall.join {L : List (List α)} {P : α → Prop} (hl : L.Forall fun l ↦ l.Forall P) :
    L.join.Forall P := by
  unfold join
  match L with
  | []      => simp [join]
  | a :: as =>
    simp [join]
    have IH := List.Forall.join (L := as) (P := P)
    have h1 : Forall (fun l => Forall P l) as
    · simp at hl
      obtain ⟨th1, hh1⟩ := hl
      exact hh1
    apply IH at h1
    simp at hl
    obtain ⟨th1, hh1⟩ := hl
    rw [forall_append_iff]
    constructor
    · exact th1
    · exact h1

lemma List.mem_mergeSort (r : α → α → Prop) [h: DecidableRel r] {l : List α} (h : a ∈ l) :
    a ∈ l.mergeSort r := by
  rw [List.Perm.mem_iff]
  · apply h
  · apply List.perm_mergeSort

lemma List.forall_mergeSort (r : α → α → Prop) [h: DecidableRel r] {l : List α} {P : α → Prop }
    (h1 : l.Forall P) : (l.mergeSort (r)).Forall P := by
  rw [List.forall_iff_forall_mem]
  intro i hi
  rw [List.forall_iff_forall_mem] at h1
  apply h1
  rw [List.Perm.mem_iff]
  apply hi
  apply List.Perm.symm
  apply List.perm_mergeSort
