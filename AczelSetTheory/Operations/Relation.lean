/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.OrderedPair
import AczelSetTheory.Operations.Union
import AczelSetTheory.Axioms.Decidable

namespace HFSet

/-- R es una relación si todo elemento es un par ordenado. -/
def isRelation
  (R : HFSet) :
    Prop
      :=
  ∀ z, z ∈ R → ∃ a b, z = ⟪a, b⟫

/-- Dominio de R: {a ∈ ⋃⋃R | ∃ b ∈ ⋃⋃R, ⟪a, b⟫ ∈ R}. -/
def domain
  (R : HFSet) :
    HFSet
      :=
  let S := sUnion (sUnion R)
  sep S (fun a => ∃ b, b ∈ S ∧ ⟪a, b⟫ ∈ R)

/-- Rango de R: {b ∈ ⋃⋃R | ∃ a ∈ ⋃⋃R, ⟪a, b⟫ ∈ R}. -/
def range
  (R : HFSet) :
    HFSet
      :=
  let S := sUnion (sUnion R)
  sep S (fun b => ∃ a, a ∈ S ∧ ⟪a, b⟫ ∈ R)

end HFSet
