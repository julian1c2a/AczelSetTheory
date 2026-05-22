/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Composition
import AczelSetTheory.Operations.Powerset

/-- Composición funcional de relaciones como conjunto de pares:
    funComp f g = {⟪a, c⟫ | ∃ b, ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f}.
    Universo: 𝒫(𝒫(⋃⋃f ∪ ⋃⋃g)) — todos los pares con componentes en ⋃⋃f ∪ ⋃⋃g.
    Nota: distinto de relComp, que separa solo los segundos componentes c. -/
def HFSet.funComp (f g : HFSet) : HFSet :=
  let Ug2 := HFSet.sUnion (HFSet.sUnion g)
  let Uf2 := HFSet.sUnion (HFSet.sUnion f)
  HFSet.sep
    (HFSet.powerset (HFSet.powerset
      (HFSet.union (HFSet.sUnion (HFSet.sUnion f)) (HFSet.sUnion (HFSet.sUnion g)))))
    (fun p => ∃ a ∈ Ug2, ∃ b ∈ Ug2, ∃ c ∈ Uf2, p = ⟪a, c⟫ ∧ ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f)

/-- Notación para la composición funcional de relaciones. -/
infixl:90 " ∘f " => HFSet.funComp
