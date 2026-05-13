import AczelSetTheory.Operations.Pair
import AczelSetTheory.Notation

namespace HFSet

/-- Par ordenado de Kuratowski: ⟨a, b⟩ = {{a}, {a, b}} -/
def orderedPair (a b : HFSet) : HFSet :=
  pair (singleton a) (pair a b)

/-- Notación ⟪a, b⟫ para el par ordenado -/
notation "⟪" a ", " b "⟫" => orderedPair a b

-- ==================================================================
-- Proyecciones del par ordenado (noncomputable, vía Classical.choose)
-- ==================================================================

/-- Primera proyección: fst ⟪a, b⟫ = a.
    Requiere una prueba de que p es un par ordenado. -/
noncomputable def fst (p : HFSet) (h : ∃ a b, p = ⟪a, b⟫) : HFSet :=
  Classical.choose h

/-- Segunda proyección: snd ⟪a, b⟫ = b.
    Requiere una prueba de que p es un par ordenado. -/
noncomputable def snd (p : HFSet) (h : ∃ a b, p = ⟪a, b⟫) : HFSet :=
  Classical.choose (Classical.choose_spec h)

end HFSet
