import AczelSetTheory.Operations.Pair
import AczelSetTheory.Notation

namespace HFSet

/-- Par ordenado de Kuratowski: ⟨a, b⟩ = {{a}, {a, b}} -/
def orderedPair (a b : HFSet) : HFSet :=
  pair (singleton a) (pair a b)

/-- Notación ⟪a, b⟫ para el par ordenado -/
notation "⟪" a ", " b "⟫" => orderedPair a b

end HFSet
