/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.OrderedPair
import AczelSetTheory.Operations.Powerset

open Classical in
/-- La función identidad sobre A:
    idFunc A = {⟪a, a⟫ | a ∈ A}.
    El universo es 𝒫(𝒫(A)) porque ⟪a, a⟫ = {{a}, {a, a}} ⊆ 𝒫(A)
    para cualquier a ∈ A (ambos, {a} y {a, a}, son subsets de A). -/
noncomputable def HFSet.idFunc (A : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset A))
    (fun p => ∃ a, a ∈ A ∧ p = HFSet.orderedPair a a)
