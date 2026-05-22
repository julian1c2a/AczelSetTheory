/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Relation
import AczelSetTheory.Operations.OrderedPair

/-- Composición de relaciones: S ∘ᵣ R = {c | ∃ a b, ⟪a,b⟫ ∈ R ∧ ⟪b,c⟫ ∈ S}.
    Con la notación infixl `S ∘ᵣ R`, los argumentos son (S R) = relComp S R.
    Para que ∃ a b, ⟪a,b⟫ ∈ R ∧ ⟪b,c⟫ ∈ S sea correcto con relComp S R,
    el universo es ⋃⋃S (rango de S) y el predicado usa los argumentos en orden inverso. -/
def HFSet.relComp (S R : HFSet) : HFSet :=
  let UR2 := HFSet.sUnion (HFSet.sUnion R)
  HFSet.sep (HFSet.sUnion (HFSet.sUnion S)) (fun c => ∃ a ∈ UR2, ∃ b ∈ UR2, ⟪a, b⟫ ∈ R ∧ ⟪b, c⟫ ∈ S)

/-- Notación estándar: S ∘ᵣ R ("primero R, luego S"). -/
infixl:90 " ∘ᵣ " => HFSet.relComp

/-- Imagen de A bajo R: {b ∈ ⋃⋃R | ∃ a ∈ A, ⟪a, b⟫ ∈ R}.
    Variante relacional de `image`, sin requerir que R sea función. -/
def HFSet.imageRel (R A : HFSet) : HFSet :=
  HFSet.sep (HFSet.sUnion (HFSet.sUnion R)) (fun b => ∃ a ∈ A, ⟪a, b⟫ ∈ R)
