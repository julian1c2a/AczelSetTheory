/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Combinatorics/Counting.lean
--
-- Principios de conteo NATIVOS sobre `HFSet`.
--
-- Capa temática propia (paralela a `Algebra/` y `Topology/`), construida
-- directamente sobre `HFSet` — NO es transporte de Peano (ver DECISIONS.md
-- → ADR-000: la teoría nueva vive en Aczel nativo).
--
-- Público:
--   HFSet.pigeonhole                  : f función-clase A→B inyectiva → card A ≤ card B
--   HFSet.exists_collision_of_card_lt : card B < card A → ∃ x≠y en A con f x = f y

import AczelSetTheory.Axioms.CardImage
import AczelSetTheory.Axioms.OrdinalNat
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Subset

namespace HFSet

open Peano

-- ─────────────────────────────────────────────────────────────────
-- §1. Principio del palomar (pigeonhole)
-- ─────────────────────────────────────────────────────────────────

/-- **Principio del palomar** (forma directa). Si `f : HFSet → HFSet` es una
    función-clase que lleva `A` en `B` y es inyectiva sobre `A`, entonces
    `card A ≤ card B`.

    Prueba: la imagen `{ y ∈ B | ∃ x ∈ A, y = f x }` tiene cardinal `card A`
    (por inyectividad) y es un subconjunto de `B`. -/
theorem pigeonhole {A B : HFSet} {f : HFSet → HFSet}
    (hf_into : ∀ x, x ∈ A → f x ∈ B)
    (hf_inj  : ∀ x y, x ∈ A → y ∈ A → f x = f y → x = y) :
    card A ≤ card B := by
  have hcard : card (sep B (fun y => ∃ x ∈ A, y = f x)) = card A :=
    card_classImage_inj f B A hf_into hf_inj
  have hsub : sep B (fun y => ∃ x ∈ A, y = f x) ⊆ B :=
    fun x hx => ((mem_sep B _ x).mp hx).1
  have hle := card_le_of_subset hsub
  rw [hcard] at hle
  exact hle

-- ─────────────────────────────────────────────────────────────────
-- §2. Forma de colisión: dos palomas en el mismo agujero
-- ─────────────────────────────────────────────────────────────────

/-- **Principio del palomar** (forma de colisión). Si `card B < card A` y `f`
    lleva `A` en `B`, entonces existen dos elementos distintos de `A` con la
    misma imagen bajo `f`. -/
theorem exists_collision_of_card_lt {A B : HFSet} {f : HFSet → HFSet}
    (hf_into : ∀ x, x ∈ A → f x ∈ B)
    (hlt : lt₀ (card B) (card A)) :
    ∃ x y, x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ f x = f y := by
  apply Classical.byContradiction
  intro h
  -- ¬(∃ colisión) ⟹ f es inyectiva sobre A
  have hf_inj : ∀ x y, x ∈ A → y ∈ A → f x = f y → x = y := by
    intro x y hx hy hfxy
    apply Classical.byContradiction
    intro hxy
    exact h ⟨x, y, hx, hy, hxy, hfxy⟩
  -- pero entonces card A ≤ card B, contradiciendo card B < card A
  exact absurd hlt (nlt_of_le (pigeonhole hf_into hf_inj))

end HFSet
