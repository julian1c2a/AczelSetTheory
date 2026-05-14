/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.OrderedPair
import AczelSetTheory.Operations.Powerset
import AczelSetTheory.Operations.Union

open Classical in
/-- Producto cartesiano de A y B:
    prodHF A B = {⟪a, b⟫ | a ∈ A, b ∈ B}.
    El universo es 𝒫(𝒫(A ∪ B)) porque ⟪a, b⟫ = {{a}, {a, b}} ⊆ 𝒫(A ∪ B)
    para cualquier a ∈ A, b ∈ B (tanto {a} como {a, b} son subsets de A ∪ B). -/
noncomputable def HFSet.prodHF (A B : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset (HFSet.union A B)))
    (fun p => ∃ a b, a ∈ A ∧ b ∈ B ∧ p = HFSet.orderedPair a b)

/-- Notación infija: A ×ₛ B para el producto cartesiano de conjuntos hereditariamente finitos. -/
infixl:80 " ×ₛ " => HFSet.prodHF
