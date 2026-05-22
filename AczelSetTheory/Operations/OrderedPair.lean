import AczelSetTheory.Operations.Pair
import AczelSetTheory.Operations.Intersection
import AczelSetTheory.Operations.Union
import AczelSetTheory.Operations.Setminus
import AczelSetTheory.Axioms.Decidable
import AczelSetTheory.Notation

namespace HFSet

/-- Par ordenado de Kuratowski: ⟨a, b⟩ = {{a}, {a, b}} -/
def orderedPair (a b : HFSet) : HFSet :=
  pair (singleton a) (pair a b)

/-- Notación ⟪a, b⟫ para el par ordenado -/
notation "⟪" a ", " b "⟫" => orderedPair a b

-- ==================================================================
-- Proyecciones del par ordenado (computables, vía fórmulas en Kuratowski)
-- ==================================================================

/-- Primera proyección: `fst ⟪a, b⟫ = a`.

    Para `p = {{a}, {a,b}}` (par Kuratowski):
    - `⋂ p  = {a} ∩ {a,b} = {a}`
    - `⋂(⋂ p) = ⋂{a} = a`

    No necesita prueba de estructura; devuelve `∅` para no-pares. -/
def fst (p : HFSet) : HFSet :=
  HFSet.sInter (HFSet.sInter p)

/-- Segunda proyección: `snd ⟪a, b⟫ = b`.

    Sea `u = ⋃ p` y `i = ⋂ p`. Para `p = {{a},{a,b}}`:
    - `u = {a,b}`,  `i = {a}`
    - Si `a = b`: `u = i = {a}`, entonces `snd = ⋂{a} = a = b`.
    - Si `a ≠ b`: `u \ i = {b}`, entonces `snd = ⋂{b} = b`.

    No necesita prueba de estructura; devuelve `∅` para no-pares. -/
def snd (p : HFSet) : HFSet :=
  let u := HFSet.sUnion p
  let i := HFSet.sInter p
  if ∀ x, x ∈ u → x ∈ i   -- equivale a u ⊆ i, i.e. a = b
  then HFSet.sInter i
  else HFSet.sInter (HFSet.setminus u i)

end HFSet
