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

-- ─────────────────────────────────────────────────────────────────
-- §3. Conteo de inyecciones: tallas iguales y no-biyección
-- ─────────────────────────────────────────────────────────────────

/-- Un subconjunto con la misma cardinalidad que el total es el total
    (conjuntos finitos). -/
theorem eq_of_subset_of_card_eq {A B : HFSet} (hsub : A ⊆ B)
    (hcard : card A = card B) : A = B := by
  apply Classical.byContradiction
  intro hne
  -- A ⊆ B con A ≠ B ⟹ existe testigo b ∈ B \ A
  have hex : ∃ b, b ∈ B ∧ b ∉ A := by
    apply Classical.byContradiction
    intro hnex
    apply hne
    apply extensionality
    intro x
    exact ⟨fun hxA => hsub x hxA,
           fun hxB => Classical.byContradiction (fun hxA => hnex ⟨x, hxB, hxA⟩)⟩
  obtain ⟨b, hbB, hbA⟩ := hex
  have hlt := card_lt_of_ssubset hsub b hbB hbA
  rw [hcard] at hlt
  exact absurd hlt (lt_irrefl _)

/-- Si `f : A → B` es inyectiva y `card A = card B`, entonces `f` es sobreyectiva
    sobre `B`: todo `b ∈ B` tiene preimagen en `A`. Es la forma "inyectiva ⟹
    biyectiva" para conjuntos finitos de la misma talla. -/
theorem surjective_of_injective_of_card_eq {A B : HFSet} {f : HFSet → HFSet}
    (hf_into : ∀ x, x ∈ A → f x ∈ B)
    (hf_inj  : ∀ x y, x ∈ A → y ∈ A → f x = f y → x = y)
    (hcard   : card A = card B) :
    ∀ y, y ∈ B → ∃ x ∈ A, y = f x := by
  have hcard_img : card (sep B (fun y => ∃ x ∈ A, y = f x)) = card A :=
    card_classImage_inj f B A hf_into hf_inj
  have hsub : sep B (fun y => ∃ x ∈ A, y = f x) ⊆ B :=
    fun x hx => ((mem_sep B _ x).mp hx).1
  have himg_eq : sep B (fun y => ∃ x ∈ A, y = f x) = B :=
    eq_of_subset_of_card_eq hsub (hcard_img.trans hcard)
  intro y hy
  rw [← himg_eq] at hy
  exact ((mem_sep B _ y).mp hy).2

/-- No-biyección entre tallas distintas: si `f : A → B` es inyectiva y
    `card A ≠ card B`, entonces `f` no es sobreyectiva — existe `y ∈ B` sin
    preimagen en `A`. -/
theorem not_surjective_of_card_ne {A B : HFSet} {f : HFSet → HFSet}
    (hf_into : ∀ x, x ∈ A → f x ∈ B)
    (hf_inj  : ∀ x y, x ∈ A → y ∈ A → f x = f y → x = y)
    (hne     : card A ≠ card B) :
    ∃ y, y ∈ B ∧ ¬ ∃ x ∈ A, y = f x := by
  apply Classical.byContradiction
  intro h
  have hsurj : ∀ y, y ∈ B → ∃ x ∈ A, y = f x := by
    intro y hy
    apply Classical.byContradiction
    intro hny
    exact h ⟨y, hy, hny⟩
  exact hne (card_eq_of_classBij hf_into hf_inj hsurj)

end HFSet
