/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Relation

open Classical in
/-- Restricción de R al dominio A: R ↾ A = {p ∈ R | ∃ a ∈ A, ∃ b, p = ⟪a, b⟫}. -/
noncomputable def HFSet.restrict (R A : HFSet) : HFSet :=
  HFSet.sep R (fun p => ∃ a b, p = ⟪a, b⟫ ∧ a ∈ A)

open HFSet in
/-- Notación R ↾ A para la restricción. -/
notation:80 R " ↾ " A => HFSet.restrict R A

open Classical in
/-- Preimagen de B bajo R: {a ∈ ⋃⋃R | ∃ b ∈ B, ⟪a, b⟫ ∈ R}. -/
noncomputable def HFSet.preimage (R B : HFSet) : HFSet :=
  HFSet.sep (HFSet.sUnion (HFSet.sUnion R)) (fun a => ∃ b, b ∈ B ∧ ⟪a, b⟫ ∈ R)