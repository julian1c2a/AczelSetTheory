/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Relation
import AczelSetTheory.Operations.Separation

namespace HFSet

/-- Imagen de un conjunto A bajo una función (relación) f:
    {b ∈ range f | ∃ a ∈ A, ⟪a, b⟫ ∈ f}. -/
def image
  (f A : HFSet) :
    HFSet
      :=
  sep (range f) (fun b => ∃ a, a ∈ A ∧ ⟪a, b⟫ ∈ f)

end HFSet
