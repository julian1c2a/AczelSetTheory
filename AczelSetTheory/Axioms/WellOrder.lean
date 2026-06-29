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
import AczelSetTheory.Axioms.Cardinal
import AczelSetTheory.Combinatorics.Counting

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

open Peano

private def vN_local : ℕ₀ → HFSet
  | .zero => HFSet.empty
  | .succ n => HFSet.insert (vN_local n) (vN_local n)

private theorem card_vN_local : ∀ n, card (vN_local n) = n
  | .zero => card_empty
  | .succ n => by
      change card (insert (vN_local n) (vN_local n)) = σ n
      rw [card_insert _ _ (not_mem_self (vN_local n)), card_vN_local n]

private theorem mem_vN_local : ∀ n x, x ∈ vN_local n → ∃ k, lt₀ k n ∧ x = vN_local k
  | .zero, x, hx => False.elim (not_mem_empty x hx)
  | .succ n, x, hx => by
      have hx' : x ∈ insert (vN_local n) (vN_local n) := hx
      rcases (mem_insert _ _ _).mp hx' with h_eq | hxn
      · exact ⟨n, lt_succ_self n, h_eq⟩
      · obtain ⟨k, hk, rfl⟩ := mem_vN_local n _ hxn
        exact ⟨k, lt_of_lt_of_le hk (Peano.Order.le_succ_self n), rfl⟩

private theorem vN_local_card_inj (n : ℕ₀) (x y : HFSet) (hx : x ∈ vN_local n) (hy : y ∈ vN_local n) :
    card x = card y → x = y := by
  intro hc
  obtain ⟨kx, _, rfl⟩ := mem_vN_local n x hx
  obtain ⟨ky, _, rfl⟩ := mem_vN_local n y hy
  have h1 := card_vN_local kx
  have h2 := card_vN_local ky
  rw [h1, h2] at hc
  rw [hc]

private def f_img_interval (f : ℕ₀ → HFSet) (i : ℕ₀) : ℕ₀ → HFSet
  | .zero => insert (f i) empty
  | .succ d => insert (f (add i (σ d))) (f_img_interval f i d)

private theorem f_i_mem_interval (f : ℕ₀ → HFSet) (i d : ℕ₀) : f i ∈ f_img_interval f i d := by
  induction d with
  | zero => exact (mem_insert _ _ _).mpr (Or.inl rfl)
  | succ d ih => exact (mem_insert _ _ _).mpr (Or.inr ih)

private theorem f_img_interval_subset {A : HFSet} (f : ℕ₀ → HFSet) (hf_mem : ∀ n, f n ∈ A) (i : ℕ₀) :
    ∀ d, f_img_interval f i d ⊆ A
  | .zero => by
      intro x hx
      change x ∈ insert (f i) empty at hx
      rcases (mem_insert _ _ _).mp hx with rfl | hxe
      · exact hf_mem i
      · exact False.elim (not_mem_empty x hxe)
  | .succ d => by
      intro x hx
      change x ∈ insert _ _ at hx
      rcases (mem_insert _ _ _).mp hx with rfl | hxe
      · exact hf_mem _
      · exact f_img_interval_subset f hf_mem i d x hxe

private theorem interval_has_pred {R : HFSet} (f : ℕ₀ → HFSet)
    (hf_desc : ∀ n, ⟪f (σ n), f n⟫ ∈ R) (i : ℕ₀) :
    ∀ d m, m ∈ f_img_interval f i d →
      (∃ y ∈ f_img_interval f i d, ⟪y, m⟫ ∈ R) ∨ m = f (add i d)
  | .zero => by
      intro m hm
      change m ∈ insert (f i) empty at hm
      rcases (mem_insert _ _ _).mp hm with rfl | hxe
      · exact Or.inr (by rw [add_zero])
      · exact False.elim (not_mem_empty _ hxe)
  | .succ d => by
      intro m hm
      change m ∈ insert (f (add i (σ d))) (f_img_interval f i d) at hm
      rcases (mem_insert _ _ _).mp hm with rfl | hxe
      · exact Or.inr rfl
      · rcases interval_has_pred f hf_desc i d m hxe with ⟨y, hy, hyR⟩ | rfl
        · exact Or.inl ⟨y, (mem_insert _ _ _).mpr (Or.inr hy), hyR⟩
        · exact Or.inl ⟨f (add i (σ d)), (mem_insert _ _ _).mpr (Or.inl rfl), hf_desc _⟩

private theorem f_succ_mem_interval (f : ℕ₀ → HFSet) (i d : ℕ₀) :
    f (σ i) ∈ f_img_interval f i (σ d) := by
  induction d with
  | zero => exact (mem_insert _ _ _).mpr (Or.inl rfl)
  | succ d ih =>
      exact (mem_insert _ _ _).mpr (Or.inr ih)

private theorem no_infinite_descent_cycle {R A : HFSet} (hwf : isStrictlyWellFounded R A)
    {f : ℕ₀ → HFSet} (hf_mem : ∀ n, f n ∈ A) (hf_desc : ∀ n, ⟪f (σ n), f n⟫ ∈ R)
    (i d : ℕ₀) (heq : f i = f (add i (σ d))) : False := by
  let S := f_img_interval f i (σ d)
  have hS_sub : S ⊆ A := f_img_interval_subset f hf_mem i (σ d)
  have hS_ne : S ≠ empty := fun h => not_mem_empty (f i) (h ▸ f_i_mem_interval f i (σ d))
  obtain ⟨m, hm_in_S, hm_min⟩ := hwf S hS_sub hS_ne
  rcases interval_has_pred f hf_desc i (σ d) m hm_in_S with ⟨y, hy, hyR⟩ | rfl
  · exact hm_min y hy hyR
  · have hy : f (σ i) ∈ S := f_succ_mem_interval f i d
    have hyR : ⟪f (σ i), f (add i (σ d))⟫ ∈ R := by
      rw [← heq]
      exact hf_desc i
    exact hm_min (f (σ i)) hy hyR

private theorem zero_add (a : ℕ₀) : add 𝟘 a = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
      change σ (add 𝟘 a) = σ a
      rw [ih]

private theorem succ_add (a b : ℕ₀) : add (σ a) b = σ (add a b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      change σ (add (σ a) b) = σ (σ (add a b))
      rw [ih]

private theorem eq_add_of_lt0 (a b : ℕ₀) : lt₀ a b → ∃ d, b = add a (σ d) := by
  induction a generalizing b with
  | zero =>
      cases b
      · intro h; exact False.elim h
      · case succ b' => intro _; exact ⟨b', by rw [zero_add]⟩
  | succ a ih =>
      cases b
      · intro h; exact False.elim h
      · case succ b' =>
          intro h
          obtain ⟨d, hd⟩ := ih b' h
          exact ⟨d, by rw [hd, succ_add]⟩

/-- No existe una cadena descendente infinita en una relación estrictamente
    bien fundada: si f : ℕ₀ → HFSet satisface ⟪f (n+1), f n⟫ ∈ R y f n ∈ A
    para todo n, se llega a contradicción. -/
theorem no_infinite_descent {R A : HFSet} (hwf : isStrictlyWellFounded R A)
    {f : ℕ₀ → HFSet}
    (hf_mem : ∀ n, f n ∈ A) (hf_desc : ∀ n, ⟪f (σ n), f n⟫ ∈ R) : False := by
  -- Usaremos vN_local (σ (card A)) como conjunto de índices.
  let Dom := vN_local (σ (card A))
  have hcard_dom : card Dom = σ (card A) := card_vN_local _
  have hlt : lt₀ (card A) (card Dom) := by
    rw [hcard_dom]
    exact lt_succ_self (card A)
  let F : HFSet → HFSet := fun x => f (card x)
  have hF_into : ∀ x ∈ Dom, F x ∈ A := fun x _ => hf_mem (card x)
  obtain ⟨x, y, hx, hy, hne, hF⟩ := exists_collision_of_card_lt hF_into hlt
  have hc_ne : card x ≠ card y := fun h => hne (vN_local_card_inj _ _ _ hx hy h)
  change f (card x) = f (card y) at hF
  rcases Peano.StrictOrder.trichotomy (card x) (card y) with hij_lt | heq | hji_lt
  · obtain ⟨d, hd⟩ := eq_add_of_lt0 (card x) (card y) hij_lt
    rw [hd] at hF
    exact no_infinite_descent_cycle hwf hf_mem hf_desc (card x) d hF
  · exact absurd heq hc_ne
  · obtain ⟨d, hd⟩ := eq_add_of_lt0 (card y) (card x) hji_lt
    rw [hd] at hF
    exact no_infinite_descent_cycle hwf hf_mem hf_desc (card y) d hF.symm

export AczelSetTheory.HFSet (
  wf_induction minimum_in_nonempty wellOrder_minimum_unique wo_induction no_infinite_descent
)

end HFSet
