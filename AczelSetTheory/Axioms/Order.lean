/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/Order.lean
-- Lemas sobre predicados de orden para HFSets.
--
-- Contenido:
--   Implicaciones entre clases: totalOrder → partialOrder → preorder, etc.
--   Casos vacíos: todo R es preorden/orden en ∅.
--   Unicidad: mínimo/máximo únicos en órdenes antisimétricos.
--   Monotonía del mínimo: mínimo ⟹ minimal.
--   Restricción: las propiedades de orden se heredan a subconjuntos.
--   Reflexividad ⟹ no-irreflexa para elementos del dominio.
--   Combinaciones: total ⟹ conexa, tricotómica ⟹ conexa.

import AczelSetTheory.Operations.Order
import AczelSetTheory.Axioms.Adjunction

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- Implicaciones entre clases de órdenes
-- ─────────────────────────────────────────────────────────────────

theorem isPartialOrder_of_totalOrder {R A : HFSet} (h : isTotalOrder R A) :
    isPartialOrder R A := h.1

theorem isPreorder_of_partialOrder {R A : HFSet} (h : isPartialOrder R A) :
    isPreorder R A := ⟨h.1, h.2.2⟩

theorem isPreorder_of_totalOrder {R A : HFSet} (h : isTotalOrder R A) :
    isPreorder R A :=
  isPreorder_of_partialOrder (isPartialOrder_of_totalOrder h)

theorem isStrictOrder_of_strictTotalOrder {R A : HFSet} (h : isStrictTotalOrder R A) :
    isStrictOrder R A := h.1

-- ─────────────────────────────────────────────────────────────────
-- Total ⟹ conexa; tricotómica ⟹ conexa
-- ─────────────────────────────────────────────────────────────────

theorem isConnected_of_isTotal {R A : HFSet} (h : isTotal R A) :
    isConnected R A :=
  fun x hx y hy _ => h x hx y hy

theorem isConnected_of_isTrichotomous {R A : HFSet} (h : isTrichotomous R A) :
    isConnected R A := by
  intro x hx y hy hne
  rcases h x hx y hy with hxy | rfl | hyx
  · exact Or.inl hxy
  · exact absurd rfl hne
  · exact Or.inr hyx

-- ─────────────────────────────────────────────────────────────────
-- Irreflexiva + transitiva ⟹ antisimétrica
-- ─────────────────────────────────────────────────────────────────

-- Nota: irreflexividad sola no implica antisimetría; se necesita también transitividad.
theorem isAntisymmetric_of_strictOrder {R A : HFSet}
    (hirr : isIrreflexive R A) (htr : isTransitive R A) :
    isAntisymmetric R A :=
  fun x hx y hy hxy hyx => absurd (htr x hx y hy x hx hxy hyx) (hirr x hx)

-- ─────────────────────────────────────────────────────────────────
-- Casos vacíos: toda relación es orden en ∅
-- ─────────────────────────────────────────────────────────────────

theorem isReflexive_empty (R : HFSet) : isReflexive R empty :=
  fun _ hx => absurd hx (not_mem_empty _)

theorem isIrreflexive_empty (R : HFSet) : isIrreflexive R empty :=
  fun _ hx => absurd hx (not_mem_empty _)

theorem isSymmetric_empty (R : HFSet) : isSymmetric R empty :=
  fun _ hx => absurd hx (not_mem_empty _)

theorem isAntisymmetric_empty (R : HFSet) : isAntisymmetric R empty :=
  fun _ hx => absurd hx (not_mem_empty _)

theorem isTransitive_empty (R : HFSet) : isTransitive R empty :=
  fun _ hx => absurd hx (not_mem_empty _)

theorem isTotal_empty (R : HFSet) : isTotal R empty :=
  fun _ hx => absurd hx (not_mem_empty _)

theorem isTrichotomous_empty (R : HFSet) : isTrichotomous R empty :=
  fun _ hx => absurd hx (not_mem_empty _)

theorem isPreorder_empty (R : HFSet) : isPreorder R empty :=
  ⟨isReflexive_empty R, isTransitive_empty R⟩

theorem isPartialOrder_empty (R : HFSet) : isPartialOrder R empty :=
  ⟨isReflexive_empty R, isAntisymmetric_empty R, isTransitive_empty R⟩

theorem isTotalOrder_empty (R : HFSet) : isTotalOrder R empty :=
  ⟨isPartialOrder_empty R, isTotal_empty R⟩

theorem isStrictOrder_empty (R : HFSet) : isStrictOrder R empty :=
  ⟨isIrreflexive_empty R, isTransitive_empty R⟩

-- ─────────────────────────────────────────────────────────────────
-- Unicidad del mínimo y máximo (en órdenes antisimétricos)
-- ─────────────────────────────────────────────────────────────────

theorem minimum_unique {R A x y : HFSet}
    (hanti : isAntisymmetric R A)
    (hx : isMinimum R A x) (hy : isMinimum R A y) : x = y :=
  hanti x hx.1 y hy.1 (hx.2 y hy.1) (hy.2 x hx.1)

theorem maximum_unique {R A x y : HFSet}
    (hanti : isAntisymmetric R A)
    (hx : isMaximum R A x) (hy : isMaximum R A y) : x = y :=
  hanti x hx.1 y hy.1 (hy.2 x hx.1) (hx.2 y hy.1)

-- ─────────────────────────────────────────────────────────────────
-- Mínimo ⟹ minimal (para órdenes antisimétricos)
-- ─────────────────────────────────────────────────────────────────

theorem isMinimal_of_isMinimum {R A x : HFSet}
    (hanti : isAntisymmetric R A) (hmin : isMinimum R A x) :
    isMinimal R A x :=
  ⟨hmin.1, fun y hy hyx => hanti y hy x hmin.1 hyx (hmin.2 y hy)⟩

theorem isMaximal_of_isMaximum {R A x : HFSet}
    (hanti : isAntisymmetric R A) (hmax : isMaximum R A x) :
    isMaximal R A x :=
  ⟨hmax.1, fun y hy hxy => hanti y hy x hmax.1 (hmax.2 y hy) hxy⟩

-- ─────────────────────────────────────────────────────────────────
-- Para órdenes totales: minimal = mínimo
-- ─────────────────────────────────────────────────────────────────

theorem isMinimum_of_isMinimal_total {R A x : HFSet}
    (htot : isTotalOrder R A) (hmin : isMinimal R A x) :
    isMinimum R A x := by
  refine ⟨hmin.1, fun y hy => ?_⟩
  rcases htot.2 x hmin.1 y hy with hxy | hyx
  · exact hxy
  · rw [hmin.2 y hy hyx]
    exact htot.1.1 x hmin.1

-- ─────────────────────────────────────────────────────────────────
-- Restricción: las propiedades se heredan a subconjuntos
-- ─────────────────────────────────────────────────────────────────

theorem isReflexive_restrict {R A B : HFSet} (h : isReflexive R A) (hB : B ⊆ A) :
    isReflexive R B :=
  fun x hx => h x (hB x hx)

theorem isIrreflexive_restrict {R A B : HFSet} (h : isIrreflexive R A) (hB : B ⊆ A) :
    isIrreflexive R B :=
  fun x hx => h x (hB x hx)

theorem isSymmetric_restrict {R A B : HFSet} (h : isSymmetric R A) (hB : B ⊆ A) :
    isSymmetric R B :=
  fun x hx y hy hxy => h x (hB x hx) y (hB y hy) hxy

theorem isAntisymmetric_restrict {R A B : HFSet} (h : isAntisymmetric R A) (hB : B ⊆ A) :
    isAntisymmetric R B :=
  fun x hx y hy hxy hyx => h x (hB x hx) y (hB y hy) hxy hyx

theorem isTransitive_restrict {R A B : HFSet} (h : isTransitive R A) (hB : B ⊆ A) :
    isTransitive R B :=
  fun x hx y hy z hz hxy hyz => h x (hB x hx) y (hB y hy) z (hB z hz) hxy hyz

theorem isTotal_restrict {R A B : HFSet} (h : isTotal R A) (hB : B ⊆ A) :
    isTotal R B :=
  fun x hx y hy => h x (hB x hx) y (hB y hy)

theorem isTrichotomous_restrict {R A B : HFSet} (h : isTrichotomous R A) (hB : B ⊆ A) :
    isTrichotomous R B :=
  fun x hx y hy => h x (hB x hx) y (hB y hy)

theorem isPreorder_restrict {R A B : HFSet} (h : isPreorder R A) (hB : B ⊆ A) :
    isPreorder R B :=
  ⟨isReflexive_restrict h.1 hB, isTransitive_restrict h.2 hB⟩

theorem isPartialOrder_restrict {R A B : HFSet} (h : isPartialOrder R A) (hB : B ⊆ A) :
    isPartialOrder R B :=
  ⟨isReflexive_restrict h.1 hB,
   isAntisymmetric_restrict h.2.1 hB,
   isTransitive_restrict h.2.2 hB⟩

theorem isTotalOrder_restrict {R A B : HFSet} (h : isTotalOrder R A) (hB : B ⊆ A) :
    isTotalOrder R B :=
  ⟨isPartialOrder_restrict h.1 hB, isTotal_restrict h.2 hB⟩

theorem isStrictOrder_restrict {R A B : HFSet} (h : isStrictOrder R A) (hB : B ⊆ A) :
    isStrictOrder R B :=
  ⟨isIrreflexive_restrict h.1 hB, isTransitive_restrict h.2 hB⟩

-- ─────────────────────────────────────────────────────────────────
-- Restricción de bien fundada
-- ─────────────────────────────────────────────────────────────────

theorem isWellFounded_restrict {R A B : HFSet}
    (hwf : isWellFounded R A) (hB : B ⊆ A) :
    isWellFounded R B := by
  intro S hS hne
  exact hwf S (subset_trans S B A hS hB) hne

theorem isStrictlyWellFounded_restrict {R A B : HFSet}
    (hwf : isStrictlyWellFounded R A) (hB : B ⊆ A) :
    isStrictlyWellFounded R B := by
  intro S hS hne
  exact hwf S (subset_trans S B A hS hB) hne

theorem isWellOrder_restrict {R A B : HFSet}
    (hwo : isWellOrder R A) (hB : B ⊆ A) :
    isWellOrder R B :=
  ⟨isTotalOrder_restrict hwo.1 hB, isWellFounded_restrict hwo.2 hB⟩

-- ─────────────────────────────────────────────────────────────────
-- El vacío es bien fundado (vacuamente)
-- ─────────────────────────────────────────────────────────────────

theorem isWellFounded_empty (R : HFSet) : isWellFounded R empty := by
  intro S hS hne
  exact absurd (subset_antisymm S empty hS (empty_subset S)) hne

theorem isStrictlyWellFounded_empty (R : HFSet) : isStrictlyWellFounded R empty := by
  intro S hS hne
  exact absurd (subset_antisymm S empty hS (empty_subset S)) hne

theorem isWellOrder_empty (R : HFSet) : isWellOrder R empty :=
  ⟨isTotalOrder_empty R, isWellFounded_empty R⟩

-- ─────────────────────────────────────────────────────────────────
-- Infimum/Supremum: unicidad en órdenes antisimétricos
-- ─────────────────────────────────────────────────────────────────

theorem infimum_unique {R A b c : HFSet}
    (hanti : isAntisymmetric R A)
    (hb_mem : b ∈ A) (hc_mem : c ∈ A)
    (hb : isInfimum R A b) (hc : isInfimum R A c) : b = c :=
  hanti b hb_mem c hc_mem (hc.2 b hb.1) (hb.2 c hc.1)

theorem supremum_unique {R A b c : HFSet}
    (hanti : isAntisymmetric R A)
    (hb_mem : b ∈ A) (hc_mem : c ∈ A)
    (hb : isSupremum R A b) (hc : isSupremum R A c) : b = c :=
  hanti b hb_mem c hc_mem (hb.2 c hc.1) (hc.2 b hb.1)

end HFSet
