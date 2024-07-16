import Matroids.PartialMatroid
import Matroids.Verification.Basic
import Matroids.Verification.Miscellaneous

open PartialMatroid List

-- two ways of phrasing the same thing:
-- 1) Forall (fun a ↦ a < n) l
-- 2) ∀ a ∈ l, a < n

lemma augment_lawful (l : List Nat) (A : PartialMatroid)
    (hA : LawfulSparsePavingMatroid n r A.matroid)
    (l_mem_range : Forall (fun a ↦ a < n) l)
    (l_length_eq_rank : l.length = r)
    (l_sorted_of_mem : l.Sorted (· < ·))
    (l_not_nearlySame_as_matroid : A.matroid.Forall fun l₁ ↦ ¬ NearlySame l₁ l) :
    LawfulSparsePavingMatroid n r (augment l A).matroid := by
  sorry

lemma augment_not_nearlySame (l : List Nat) (A : PartialMatroid)
    (hA : A.matroid.Forall (fun l₁ ↦ A.remainingOptions.Forall (fun l₂ ↦ ¬NearlySame l₁ l₂))):
    Forall (fun l₁ ↦ Forall (fun l₂ ↦ ¬NearlySame l₁ l₂) (augment l A).remainingOptions)
      (augment l A).matroid := by
  sorry

lemma elimNearlySame_notAdding (l : List Nat) (A : List (List Nat)) :
    ∀ k, k ∈ (elimNearlySame l A) → k ∈ A := by
  unfold elimNearlySame
  match A with
  | [] => simp [elimNearlySame]
  | h1 :: t1 =>
    simp [elimNearlySame]
    intro a ha
    sorry




lemma elimGreater_notAdding (l : List Nat) (A : List (List Nat)) :
    ∀ k, k ∈ (elimGreater l A) → k ∈ A := by
  unfold elimGreater
  match A with
  | [] => simp [elimGreater]
  | h1 :: t1 =>
    simp [elimGreater]
    intro k hk
    split_ifs at hk
    · have IH := elimGreater_notAdding (l := h1) (A := t1)
      let l : k ∈ elimGreater h1 t1
      ·sorry
      sorry
    sorry


lemma augment_notAdding (l : List Nat) (A : PartialMatroid) :
    ∀ k, k ∈ (augment l A).remainingOptions → k ∈ A.remainingOptions := by
  unfold augment
  simp
  intro k hk
  apply elimGreater_notAdding at hk
  apply elimNearlySame_notAdding
  exact hk
