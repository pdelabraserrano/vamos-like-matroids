import Matroids.NearlySame
import Matroids.Verification.Basic
import Matroids.Verification.Miscellaneous

lemma NearlySameAux.comm {l₁ l₂ : List Nat} {a b c : Bool} :
    NearlySameAux l₁ l₂ = (a, b, c) ↔ NearlySameAux l₂ l₁ = (a, c, b) := by
  match l₁,l₂ with
    | [], [] =>
      simp [NearlySameAux]
      tauto
    | [], [_] =>
      simp [NearlySameAux]
      tauto
    | [], _ :: _ :: _ =>
      simp [NearlySameAux]
      tauto
    | [_], [] =>
      simp [NearlySameAux]
      tauto
    | _ :: _ :: _, [] =>
      simp [NearlySameAux]
      tauto
    | h1 :: t1, h2 :: t2 =>
      simp [NearlySameAux]
      have IH :
        NearlySameAux t1 t2 = (a, b, c) ↔ NearlySameAux t2 t1 = (a, c, b) := NearlySameAux.comm
      split_ifs
      · apply IH
      · tauto
      · tauto
      · tauto
      · tauto
      · tauto
      · omega
      · omega
      · sorry
      · sorry
      · tauto
      · omega
      · omega
      · sorry
      · sorry
      · tauto
      · sorry
      · sorry
      · omega
      · omega
      · tauto
      · sorry
      · sorry
      · omega
      · omega


lemma NearlySameAux2.comm {l₁ l₂ : List Nat} :
    let (a, b, c) := NearlySameAux l₁ l₂
    NearlySameAux l₂ l₁ = (a, c, b) := by sorry

lemma NearlySame.comm {l₁ l₂: List Nat} : NearlySame l₁ l₂ = NearlySame l₂ l₁ := by
  unfold NearlySame
  sorry
