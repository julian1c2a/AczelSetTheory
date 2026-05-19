/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/WellOrder.lean
-- Principios de inducción y descenso para relaciones bien fundadas.
--
-- Contenido:
--   wf_induction: inducción bien fundada desde isStrictlyWellFounded.
--   wo_induction: inducción por buen orden (total + bien fundado).
--   minimum_in_nonempty: todo subconjunto no vacío de un buen orden tiene mínimo.
--   wellOrder_minimum_unique: unicidad del mínimo en un buen orden.

import AczelSetTheory.Operations.Order
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Order

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- Inducción bien fundada (estricta)
-- ─────────────────────────────────────────────────────────────────

/-- Principio de inducción bien fundada: si R es estrictamente bien fundada en A y
    cada x ∈ A satisface P siempre que todos sus R-predecesores en A lo satisfagan,
    entonces todos los elementos de A satisfacen P. -/
theorem wf_induction {R A : HFSet} (hwf : isStrictlyWellFounded R A)
    {P : HFSet → Prop}
    (step : ∀ x ∈ A, (∀ y ∈ A, ⟪y, x⟫ ∈ R → P y) → P x) :
    ∀ x ∈ A, P x := by
  intro x hx
  apply Classical.byContradiction
  intro hnp
  -- Sea S = {z ∈ A | ¬P z}, no vacío porque x ∈ S.
  haveI : DecidablePred (fun z => ¬P z) := fun z => Classical.propDecidable _
  let S := sep A (fun z => ¬P z)
  have hS_sub : S ⊆ A := fun z hz => (mem_sep A _ z |>.mp hz).1
  have hS_ne : S ≠ empty := by
    intro heq
    have hx_in_S : x ∈ S := mem_sep A _ x |>.mpr ⟨hx, hnp⟩
    exact absurd (heq ▸ hx_in_S) (not_mem_empty x)
  obtain ⟨m, hm_in_S, hm_no_pred⟩ := hwf S hS_sub hS_ne
  have hm_in_A : m ∈ A := hS_sub m hm_in_S
  have hnp_m : ¬P m := (mem_sep A _ m |>.mp hm_in_S).2
  apply hnp_m
  apply step m hm_in_A
  intro y hy hym
  apply Classical.byContradiction
  intro hnp_y
  have hy_in_S : y ∈ S := mem_sep A _ y |>.mpr ⟨hy, hnp_y⟩
  exact absurd hym (hm_no_pred y hy_in_S)

-- ─────────────────────────────────────────────────────────────────
-- Inducción por buen orden
-- ─────────────────────────────────────────────────────────────────

/-- En un buen orden, todo subconjunto no vacío tiene un elemento mínimo.
    (Reformulación de `isWellFounded` en la forma de `isMinimum`.) -/
theorem minimum_in_nonempty {R A S : HFSet}
    (hwo : isWellOrder R A) (hS : S ⊆ A) (hne : S ≠ empty) :
    ∃ m, isMinimum R S m :=
  hwo.2 S hS hne

/-- El mínimo de un subconjunto en un buen orden es único. -/
theorem wellOrder_minimum_unique {R A S x y : HFSet}
    (hwo : isWellOrder R A) (hS : S ⊆ A)
    (hx : isMinimum R S x) (hy : isMinimum R S y) : x = y :=
  minimum_unique (isAntisymmetric_restrict hwo.1.1.2.1 hS) hx hy

/-- Principio de inducción por buen orden (versión no estricta):
    si R es un buen orden en A y cada x ∈ A satisface P siempre que
    todos los y ∈ A con ⟪y, x⟫ ∈ R y y ≠ x lo satisfagan, entonces
    todos los elementos de A satisfacen P. -/
theorem wo_induction {R A : HFSet} (hwo : isWellOrder R A)
    {P : HFSet → Prop}
    (step : ∀ x ∈ A, (∀ y ∈ A, ⟪y, x⟫ ∈ R → y ≠ x → P y) → P x) :
    ∀ x ∈ A, P x := by
  intro x hx
  apply Classical.byContradiction
  intro hnp
  haveI : DecidablePred (fun z => ¬P z) := fun z => Classical.propDecidable _
  let S := sep A (fun z => ¬P z)
  have hS_sub : S ⊆ A := fun z hz => (mem_sep A _ z |>.mp hz).1
  have hS_ne : S ≠ empty := by
    intro heq
    have hx_in_S : x ∈ S := mem_sep A _ x |>.mpr ⟨hx, hnp⟩
    exact absurd (heq ▸ hx_in_S) (not_mem_empty x)
  obtain ⟨m, hm_in_S, hm_min⟩ := hwo.2 S hS_sub hS_ne
  have hm_in_A : m ∈ A := hS_sub m hm_in_S
  have hnp_m : ¬P m := (mem_sep A _ m |>.mp hm_in_S).2
  apply hnp_m
  apply step m hm_in_A
  intro y hy hym hne
  apply Classical.byContradiction
  intro hnp_y
  have hy_in_S : y ∈ S := mem_sep A _ y |>.mpr ⟨hy, hnp_y⟩
  -- m es mínimo de S: ⟪m, y⟫ ∈ R para todo y ∈ S.
  -- Tenemos ⟪y, m⟫ ∈ R e ⟪m, y⟫ ∈ R con y ≠ m.
  -- Por antisimetría, y = m — contradicción con y ≠ m.
  have hmym : ⟪m, y⟫ ∈ R := hm_min y hy_in_S
  have hanti := isAntisymmetric_restrict hwo.1.1.2.1 hS_sub
  exact absurd (hanti m hm_in_S y hy_in_S hmym hym) hne.symm

-- ─────────────────────────────────────────────────────────────────
-- Descenso infinito es imposible en órdenes bien fundados
-- ─────────────────────────────────────────────────────────────────

/-- No existe una cadena descendente infinita en una relación estrictamente
    bien fundada: si f : ℕ₀ → HFSet satisface ⟪f (n+1), f n⟫ ∈ R y f n ∈ A
    para todo n, se llega a contradicción. -/
theorem no_infinite_descent {R A : HFSet} (hwf : isStrictlyWellFounded R A)
    {f : ℕ₀ → HFSet}
    (hf_mem : ∀ n, f n ∈ A) (hf_desc : ∀ n, ⟪f (σ n), f n⟫ ∈ R) : False :=
  wf_induction hwf (P := fun x => ∀ n, f n = x → False)
    (fun _x _hx ih n hn => ih (f (σ n)) (hf_mem (σ n)) (hn ▸ hf_desc n) (σ n) rfl)
    (f 𝟘) (hf_mem 𝟘) 𝟘 rfl

end HFSet
