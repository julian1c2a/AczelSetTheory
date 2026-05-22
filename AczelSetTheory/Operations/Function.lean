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
    Busca el único b tal que ⟪a, b⟫ ∈ f y lo devuelve.
    Devuelve ∅ si a no está en el dominio (función total sobre su dominio). -/
def apply (f a : HFSet) : HFSet :=
  HFSet.snd (HFSet.sInter (HFSet.sep f (fun p => HFSet.fst p = a)))

end HFSet
