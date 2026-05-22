/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Relation

/-- Restricción de R al dominio A: R ↾ A = {p ∈ R | ∃ a ∈ A, ∃ b, p = ⟪a, b⟫}. -/
def HFSet.restrict (R A : HFSet) : HFSet :=
  let UR2 := HFSet.sUnion (HFSet.sUnion R)
  HFSet.sep R (fun p => ∃ a ∈ A, ∃ b ∈ UR2, p = ⟪a, b⟫)

open HFSet in
/-- Notación R ↾ A para la restricción. -/
notation:80 R " ↾ " A => HFSet.restrict R A

/-- Preimagen de B bajo R: {a ∈ ⋃⋃R | ∃ b ∈ B, ⟪a, b⟫ ∈ R}. -/
def HFSet.preimage (R B : HFSet) : HFSet :=
  HFSet.sep (HFSet.sUnion (HFSet.sUnion R)) (fun a => ∃ b ∈ B, ⟪a, b⟫ ∈ R)
