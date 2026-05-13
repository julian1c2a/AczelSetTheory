/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Relation
import AczelSetTheory.Operations.OrderedPair
import AczelSetTheory.Operations.Powerset

open Classical in
/-- La relación inversa (conversa) de R:
    R⁻¹ᵣ = {⟪b, a⟫ | ⟪a, b⟫ ∈ R}.
    El universo es 𝒫(𝒫(⋃⋃R)) porque ⟪b, a⟫ = {{b}, {b, a}} ⊆ 𝒫(⋃⋃R). -/
noncomputable def HFSet.relInv (R : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset (HFSet.sUnion (HFSet.sUnion R))))
    (fun p => ∃ a b, ⟪a, b⟫ ∈ R ∧ p = ⟪b, a⟫)

/-- Notación postfija para la relación inversa. -/
postfix:75 "⁻¹ᵣ" => HFSet.relInv
