/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Relation

namespace HFSet

/-- f es una función (relación univaluada): relación + para cada a,
    a lo sumo un b con ⟪a, b⟫ ∈ f. -/
def isFunction
  (f : HFSet) :
    Prop
      :=
  isRelation f ∧ ∀ a b₁ b₂, ⟪a, b₁⟫ ∈ f → ⟪a, b₂⟫ ∈ f → b₁ = b₂

/-- f es una función total de A en B: función con domain f = A y range f ⊆ B. -/
def isTotalFunction
  (f A B : HFSet) :
    Prop
      :=
  isFunction f ∧ domain f = A ∧ ∀ b, b ∈ range f → b ∈ B

/-- Aplicación de una función f a un argumento a.
    Requiere prueba de que a está en el dominio. Noncomputable (Classical.choose). -/
noncomputable def apply
  (f a : HFSet) (h : ∃ b, ⟪a, b⟫ ∈ f) :
    HFSet
      :=
  Classical.choose h

end HFSet
