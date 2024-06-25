/-- Implementation of differnet relabelling Auxiliary functions to
explore different syntax -/

def relabellingAux (g : Nat → Nat) (B : List Nat) : List Nat :=
  (B.map) g

def relabellingAux2 (g : Nat → Nat) : List Nat → List Nat :=
  fun (B : List Nat)  ↦ (B.map) g

def relabellingAux3 : (Nat → Nat) → List Nat → List Nat :=
  fun g ↦ fun B ↦ (B.map) g
