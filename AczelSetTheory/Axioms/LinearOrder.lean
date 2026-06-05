/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/LinearOrder.lean
-- Instancia `StrictLinearOrder HFSet` vía la comparación lexicográfica sobre CList.
-- Habilita `FinGroup HFSet` y en general cualquier estructura de Peano parametrizada
-- por un tipo con orden lineal estricto decidible.

import AczelSetTheory.HFSets
import AczelSetTheory.CList.Order
import AczelSetTheory.Axioms.OrdinalNat
import Peano.PeanoNat.StrictOrder

open Peano

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- 1. Instancia LT
-- ─────────────────────────────────────────────────────────────────

/-- Orden en HFSet: A < B cuando la forma normal de A es menor que la de B
    en el orden lexicográfico de CList. -/
instance : LT HFSet where
  lt A B := CList.lt A.repr B.repr = true

-- ─────────────────────────────────────────────────────────────────
-- 2. Propiedades del orden
-- ─────────────────────────────────────────────────────────────────

private theorem lt_repr_iff (A B : HFSet) :
    A < B ↔ CList.lt A.repr B.repr = true := Iff.rfl

theorem lt_irrefl (A : HFSet) : ¬ A < A := by
  simp [lt_repr_iff, CList.lt_irrefl]

theorem lt_trans {A B C : HFSet} (h1 : A < B) (h2 : B < C) : A < C :=
  CList.lt_trans A.repr B.repr C.repr h1 h2

theorem lt_trich (A B : HFSet) (h1 : ¬ A < B) (h2 : ¬ B < A) : A = B := by
  rw [lt_repr_iff] at h1 h2
  have h1' : CList.lt A.repr B.repr = false := by
    cases h : CList.lt A.repr B.repr <;> simp_all
  have h2' : CList.lt B.repr A.repr = false := by
    cases h : CList.lt B.repr A.repr <;> simp_all
  exact (canonicalEq_iff_eq A B).mp (CList.lt_antisymm A.repr B.repr h1' h2')

-- ─────────────────────────────────────────────────────────────────
-- 3. Decidabilidad de <
-- ─────────────────────────────────────────────────────────────────

instance instDecidableLt (A B : HFSet) : Decidable (A < B) :=
  show Decidable (CList.lt A.repr B.repr = true) from
  match CList.lt A.repr B.repr with
  | true  => isTrue rfl
  | false => isFalse nofun

-- ─────────────────────────────────────────────────────────────────
-- 4. Instancia StrictLinearOrder
-- ─────────────────────────────────────────────────────────────────

instance : StrictLinearOrder HFSet where
  decLt  := instDecidableLt
  irrefl := lt_irrefl
  trans  := fun h1 h2 => lt_trans h1 h2
  trich  := lt_trich

end HFSet
