import Matroids.Verification.Basic
import Matroids.Vamos

lemma vamos_lawful : LawfulSparsePavingMatroid 8 4 Vamos.matroid := sorry

lemma vamos_remainingOptions_mem_range :
    Vamos.remainingOptions.Forall (List.Forall fun i ↦ i < 8) :=
  sorry

lemma vamos_remainingOptions_length_eq_rank : Vamos.remainingOptions.Forall (fun l ↦ l.length = 4) :=
  sorry

lemma vamos_remainingOptions_sorted_of_mem :
    Vamos.remainingOptions.Forall fun m ↦ m.Sorted (· < ·) :=
  sorry

lemma vamos_remainingOptions_not_nearlySame :
    Vamos.matroid.Forall fun l₁ ↦ Vamos.remainingOptions.Forall fun l₂ ↦ ¬ NearlySame l₁ l₂ :=
  sorry
