/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/HFListOps.lean
-- Conversión HFList → HFSet (olvida el orden, elimina duplicados)
-- y lemas de membresía que conectan las dos estructuras.
--
-- Público:
--   HFList.toHFSet  : HFList → HFSet
--   HFList.toHFSet_nil   : toHFSet nil = ∅
--   HFList.toHFSet_cons  : toHFSet (cons h t) = insert h (toHFSet t)
--   HFList.mem_toHFSet   : x ∈ toHFSet l ↔ x ∈ l   (Prop-membresía)
--   FinList.toHFSet      : FinList n → HFSet

import AczelSetTheory.HFList
import AczelSetTheory.Axioms.Adjunction

open Peano

namespace HFList

-- ─────────────────────────────────────────────────────────────────
-- Definición: lista ordenada → conjunto (olvida orden, elimina dups)
-- ─────────────────────────────────────────────────────────────────

/-- Convierte una `HFList` en un `HFSet` descartando el orden e insertando
    cada elemento en el conjunto resultado. -/
def toHFSet : HFList → HFSet
  | .nil      => HFSet.empty
  | .cons h t => HFSet.insert h (toHFSet t)

-- ─────────────────────────────────────────────────────────────────
-- Lemas de reducción
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem toHFSet_nil : toHFSet nil = HFSet.empty := rfl

@[simp] theorem toHFSet_cons (h : HFSet) (t : HFList) :
    toHFSet (cons h t) = HFSet.insert h (toHFSet t) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Membresía: x ∈ toHFSet l ↔ x ∈ l (como proposición de lista)
-- ─────────────────────────────────────────────────────────────────

/-- La membresía en el conjunto resultante es equivalente a pertenecer
    a la lista original (como proposición, no por posición). -/
theorem mem_toHFSet {x : HFSet} {l : HFList} :
    x ∈ toHFSet l ↔ x ∈ l := by
  induction l with
  | nil =>
      constructor
      · exact fun h => absurd h (HFSet.not_mem_empty x)
      · exact fun h => absurd h (not_mem_nil x)
  | cons hd tl ih =>
      show x ∈ HFSet.insert hd (toHFSet tl) ↔ x ∈ HFList.cons hd tl
      rw [HFSet.mem_insert, mem_cons_iff]
      exact ⟨fun h => h.imp_right ih.mp, fun h => h.imp_right ih.mpr⟩

/-- Si `x` está en la lista, está en el conjunto. -/
theorem mem_toHFSet_of_mem {x : HFSet} {l : HFList} (h : x ∈ l) :
    x ∈ toHFSet l :=
  mem_toHFSet.mpr h

end HFList

-- ─────────────────────────────────────────────────────────────────
-- FinList.toHFSet: conversión de n-tupla a conjunto
-- ─────────────────────────────────────────────────────────────────

namespace FinList

variable {n : ℕ₀}

/-- Convierte una n-tupla de `HFSet`s en un `HFSet` (olvida aridad y orden). -/
def toHFSet (t : FinList n) : HFSet := t.val.toHFSet

@[simp] theorem toHFSet_empty : (FinList.empty : FinList 𝟘).toHFSet = HFSet.empty := rfl

@[simp] theorem toHFSet_cons (x : HFSet) (t : FinList n) :
    (FinList.cons x t).toHFSet = HFSet.insert x t.toHFSet := rfl

/-- Membresía en la imagen conjunto de una n-tupla. -/
theorem mem_toHFSet {x : HFSet} {t : FinList n} :
    x ∈ t.toHFSet ↔ x ∈ t.val :=
  HFList.mem_toHFSet

end FinList
