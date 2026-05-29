/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/CosetCount.lean
-- Conteo de cosetes y Teorema de Lagrange.

import AczelSetTheory.Algebra.Subgroup
import AczelSetTheory.Axioms.OrdinalNat
import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.Powerset
import Peano.PeanoNat.Arith

open Peano
open Peano.Arith

namespace HFSet

-- ======================================================================
-- Auxiliares sobre sUnión
-- ======================================================================

private theorem sUnion_empty_eq : sUnion (empty : HFSet) = empty :=
  extensionality _ _ fun x => by
    simp only [mem_sUnion]
    exact ⟨fun ⟨Y, hY, _⟩ => absurd hY (not_mem_empty Y),
           fun h => absurd h (not_mem_empty x)⟩

/-- La unión generalizada distribuye sobre inserción:
    sUnion (insert C F) = union C (sUnion F). -/
theorem sUnion_insert (C F : HFSet) :
    sUnion (insert C F) = union C (sUnion F) :=
  extensionality _ _ fun x => by
    simp only [mem_sUnion, mem_union, mem_insert]
    constructor
    · rintro ⟨Y, hY, hxY⟩
      rcases hY with rfl | hYF
      · exact Or.inl hxY
      · exact Or.inr ⟨Y, hYF, hxY⟩
    · rintro (hxC | ⟨Y, hYF, hxY⟩)
      · exact ⟨C, Or.inl rfl, hxC⟩
      · exact ⟨Y, Or.inr hYF, hxY⟩

-- ======================================================================
-- Cardinalidad de una partición uniforme
-- ======================================================================

/-- Si F es una familia de conjuntos mutuamente disjuntos, cada uno con
    cardinalidad k, entonces card(⋃ F) = card(F) · k. -/
theorem card_sUnion_uniform_partition (F : HFSet) (k : ℕ₀)
    (hunif : ∀ C, C ∈ F → card C = k)
    (hdisj : ∀ C D, C ∈ F → D ∈ F → C ≠ D → inter C D = empty) :
    card (sUnion F) = mul (card F) k := by
  revert hunif hdisj
  apply eps_induction
      (fun F =>
        (∀ C, C ∈ F → card C = k) →
        (∀ C D, C ∈ F → D ∈ F → C ≠ D → inter C D = empty) →
        card (sUnion F) = mul (card F) k)
  · -- Base: F = ∅
    intro _ _
    rw [sUnion_empty_eq, card_empty, zero_mul]
  · -- Paso: F = insert C F'
    intro F' C IH hunif hdisj
    have hCinF : C ∈ insert C F' := mem_insert_self C F'
    by_cases hCF' : C ∈ F'
    · -- C ∈ F': insert C F' = F' por insert_mem_eq
      have heq : insert C F' = F' :=
        extensionality _ _ fun x => ⟨
          fun hx => (mem_insert x C F').mp hx |>.elim (· ▸ hCF') id,
          fun hx => (mem_insert x C F').mpr (Or.inr hx)⟩
      rw [heq]
      exact IH
        (fun D hD => hunif D ((mem_insert D C F').mpr (Or.inr hD)))
        (fun D E hD hE hDE => hdisj D E
          ((mem_insert D C F').mpr (Or.inr hD))
          ((mem_insert E C F').mpr (Or.inr hE)) hDE)
    · -- C ∉ F': paso principal
      -- Disjunción de C con sUnion F'
      have hdisj_C : inter C (sUnion F') = empty := by
        apply extensionality; intro x
        constructor
        · intro hx
          simp only [mem_inter, mem_sUnion] at hx
          obtain ⟨hxC, Y, hYF', hxY⟩ := hx
          have hCY : C ≠ Y := fun h => hCF' (h ▸ hYF')
          have hCYd : inter C Y = empty :=
            hdisj C Y hCinF ((mem_insert Y C F').mpr (Or.inr hYF')) hCY
          exact absurd ((mem_inter C Y x).mpr ⟨hxC, hxY⟩)
            (hCYd ▸ not_mem_empty x)
        · intro hx; exact absurd hx (not_mem_empty x)
      -- Hipótesis de inducción aplicada a F'
      have hcard_F' : card (sUnion F') = mul (card F') k :=
        IH
          (fun D hD => hunif D ((mem_insert D C F').mpr (Or.inr hD)))
          (fun D E hD hE hDE => hdisj D E
            ((mem_insert D C F').mpr (Or.inr hD))
            ((mem_insert E C F').mpr (Or.inr hE)) hDE)
      -- Combinar
      rw [sUnion_insert, card_union_disjoint _ _ hdisj_C,
          hunif C hCinF, hcard_F', card_insert C F' hCF', succ_mul]
      exact add_comm k _

/-- Si `F` es una familia pairwise disjunta de conjuntos, cada uno con
    cardinalidad divisible por `p`, entonces `p ∣ card(⋃ F)`. -/
theorem dvd_card_sUnion_of_all_dvd (p : ℕ₀) (F : HFSet)
    (hdisj : ∀ C D, C ∈ F → D ∈ F → C ≠ D → inter C D = empty)
    (hdvd : ∀ C, C ∈ F → p ∣ card C) :
    p ∣ card (sUnion F) := by
  revert hdisj hdvd
  apply eps_induction
      (fun F =>
        (∀ C D, C ∈ F → D ∈ F → C ≠ D → inter C D = empty) →
        (∀ C, C ∈ F → p ∣ card C) →
        p ∣ card (sUnion F))
  · -- Base: F = ∅
    intro _ _
    rw [sUnion_empty_eq, card_empty]
    exact divides_zero p
  · -- Paso: F = insert C F'
    intro F' C IH hdisj hdvd
    have hCinF : C ∈ insert C F' := mem_insert_self C F'
    by_cases hCF' : C ∈ F'
    · -- C ∈ F': insert C F' = F' por insert_mem_eq
      have heq : insert C F' = F' :=
        extensionality _ _ fun x => ⟨
          fun hx => (mem_insert x C F').mp hx |>.elim (· ▸ hCF') id,
          fun hx => (mem_insert x C F').mpr (Or.inr hx)⟩
      rw [heq]
      exact IH
        (fun D E hD hE hDE => hdisj D E
          ((mem_insert D C F').mpr (Or.inr hD))
          ((mem_insert E C F').mpr (Or.inr hE)) hDE)
        (fun D hD => hdvd D ((mem_insert D C F').mpr (Or.inr hD)))
    · -- C ∉ F': card(sUnion(insert C F')) = card C + card(sUnion F')
      have hdisj_C : inter C (sUnion F') = empty := by
        apply extensionality; intro x
        constructor
        · intro hx
          simp only [mem_inter, mem_sUnion] at hx
          obtain ⟨hxC, Y, hYF', hxY⟩ := hx
          have hCY : C ≠ Y := fun h => hCF' (h ▸ hYF')
          have hCYd : inter C Y = empty :=
            hdisj C Y hCinF ((mem_insert Y C F').mpr (Or.inr hYF')) hCY
          exact absurd ((mem_inter C Y x).mpr ⟨hxC, hxY⟩)
            (hCYd ▸ not_mem_empty x)
        · intro hx; exact absurd hx (not_mem_empty x)
      have hdvd_F' : p ∣ card (sUnion F') :=
        IH
          (fun D E hD hE hDE => hdisj D E
            ((mem_insert D C F').mpr (Or.inr hD))
            ((mem_insert E C F').mpr (Or.inr hE)) hDE)
          (fun D hD => hdvd D ((mem_insert D C F').mpr (Or.inr hD)))
      rw [sUnion_insert, card_union_disjoint _ _ hdisj_C]
      exact divides_add (hdvd C hCinF) hdvd_F'

end HFSet

-- ======================================================================
-- Equinumerosidad general de cosetes y Teorema de Lagrange
-- ======================================================================

namespace HFAlgebra

/-- Lema privado: la aplicación h ↦ h·a es una biyección de A en {h·a | h ∈ A},
    preservando la cardinalidad, para cualquier A ⊆ G y a ∈ G. -/
private theorem card_rightMul_eq_card (g : HFGroup) (a : HFSet) (ha : a ∈ g.G) :
    ∀ A : HFSet, (∀ {x : HFSet}, x ∈ A → x ∈ g.G) →
    HFSet.card (HFSet.sep g.G (fun x => ∃ h ∈ A, x = g.op h a)) =
    HFSet.card A := by
  apply HFSet.eps_induction
      (fun A => (∀ {x : HFSet}, x ∈ A → x ∈ g.G) →
       HFSet.card (HFSet.sep g.G (fun x => ∃ h ∈ A, x = g.op h a)) =
       HFSet.card A)
  · -- Base: A = ∅
    intro _
    have hempty : HFSet.sep g.G (fun x => ∃ h ∈ (HFSet.empty : HFSet), x = g.op h a) =
        HFSet.empty :=
      HFSet.extensionality _ _ fun x => by
        rw [HFSet.mem_sep]
        exact ⟨fun ⟨_, h, hh, _⟩ => absurd hh (HFSet.not_mem_empty h),
               fun hx => absurd hx (HFSet.not_mem_empty x)⟩
    rw [hempty, HFSet.card_empty]
  · -- Paso: A = insert b A'
    intro A' b IH hA
    have hbG : b ∈ g.G := hA (HFSet.mem_insert_self b A')
    have hA' : ∀ {x : HFSet}, x ∈ A' → x ∈ g.G :=
      fun {x} hx => hA ((HFSet.mem_insert x b A').mpr (Or.inr hx))
    by_cases hbA' : b ∈ A'
    · -- b ∈ A': insert b A' = A'
      have heq : HFSet.insert b A' = A' :=
        HFSet.extensionality _ _ fun x => ⟨
          fun hx => (HFSet.mem_insert x b A').mp hx |>.elim (· ▸ hbA') id,
          fun hx => (HFSet.mem_insert x b A').mpr (Or.inr hx)⟩
      rw [heq]
      exact IH hA'
    · -- b ∉ A': paso principal
      -- S' = {h·a | h ∈ insert b A'} = insert (b·a) S  donde  S = {h·a | h ∈ A'}
      have hS'_eq :
          HFSet.sep g.G (fun x => ∃ h ∈ HFSet.insert b A', x = g.op h a) =
          HFSet.insert (g.op b a)
            (HFSet.sep g.G (fun x => ∃ h ∈ A', x = g.op h a)) := by
        apply HFSet.extensionality; intro x
        rw [HFSet.mem_sep, HFSet.mem_insert, HFSet.mem_sep]
        constructor
        · rintro ⟨hxG, h, hh, hx⟩
          rcases (HFSet.mem_insert h b A').mp hh with rfl | hhA'
          · exact Or.inl hx
          · exact Or.inr ⟨hxG, h, hhA', hx⟩
        · rintro (rfl | ⟨hxG, h, hhA', hx⟩)
          · exact ⟨g.op_closed hbG ha, b,
                   (HFSet.mem_insert b b A').mpr (Or.inl rfl), rfl⟩
          · exact ⟨hxG, h, (HFSet.mem_insert h b A').mpr (Or.inr hhA'), hx⟩
      -- b·a ∉ S: si b·a = h·a con h ∈ A', entonces b = h ∈ A', contradicción
      have hba_not_S :
          g.op b a ∉ HFSet.sep g.G (fun x => ∃ h ∈ A', x = g.op h a) := by
        intro hmem
        rw [HFSet.mem_sep] at hmem
        obtain ⟨_, h, hhA', hba_eq⟩ := hmem
        have hbh : b = h := g.right_cancel ha hbG (hA' hhA') hba_eq
        exact hbA' (hbh ▸ hhA')
      -- Concluir: card S' = σ(card S) = σ(card A') = card(insert b A')
      rw [hS'_eq, HFSet.card_insert _ _ hba_not_S, IH hA',
          HFSet.card_insert b A' hbA']

namespace HFSubgroup

open HFSet

variable {grp : HFGroup}

-- ======================================================================
-- Equinumerosidad general: card(Ha) = card(H) para todo a ∈ G
-- ======================================================================

/-- El cosete derecho `Ha` tiene la misma cardinalidad que `H`
    para cualquier `a ∈ G`. -/
theorem card_rightCoset_eq_card_H (sub : HFSubgroup grp) {a : HFSet}
    (ha : a ∈ grp.G) :
    card (sub.rightCoset a) = card sub.H :=
  card_rightMul_eq_card grp a ha sub.H sub.H_sub

-- ======================================================================
-- Conjunto de cosetes derechos
-- ======================================================================

/-- Conjunto de todos los cosetes derechos de `H` en `G`. -/
def cosets (sub : HFSubgroup grp) : HFSet :=
  sep (powerset grp.G) (fun C => ∃ a ∈ grp.G, C = sub.rightCoset a)

theorem mem_cosets {sub : HFSubgroup grp} {C : HFSet} :
    C ∈ sub.cosets ↔ ∃ a ∈ grp.G, C = sub.rightCoset a := by
  unfold cosets
  rw [mem_sep]
  constructor
  · rintro ⟨_, a, haG, rfl⟩
    exact ⟨a, haG, rfl⟩
  · rintro ⟨a, haG, rfl⟩
    refine ⟨?_, a, haG, rfl⟩
    rw [mem_powerset]
    intro x hx
    obtain ⟨h, hh, rfl⟩ := (sub.mem_rightCoset haG).mp hx
    exact grp.op_closed (sub.H_sub hh) haG

/-- Índice del subgrupo H en G: número de cosetes derechos distintos. -/
def index (sub : HFSubgroup grp) : ℕ₀ := card sub.cosets

-- ======================================================================
-- Los cosetes cubren G y son pairwise disjuntos
-- ======================================================================

/-- Los cosetes derechos cubren `G`: `sUnion(cosets) = G`. -/
theorem cosets_cover (sub : HFSubgroup grp) :
    sUnion sub.cosets = grp.G := by
  apply extensionality; intro x
  constructor
  · intro hx
    rw [mem_sUnion] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    rw [mem_cosets] at hC
    obtain ⟨a, haG, rfl⟩ := hC
    obtain ⟨h, hh, rfl⟩ := (sub.mem_rightCoset haG).mp hxC
    exact grp.op_closed (sub.H_sub hh) haG
  · intro hxG
    rw [mem_sUnion]
    exact ⟨sub.rightCoset x, mem_cosets.mpr ⟨x, hxG, rfl⟩,
           sub.rightCoset_self_mem hxG⟩

/-- Cosetes derechos distintos son disjuntos. -/
theorem cosets_pairwise_disjoint (sub : HFSubgroup grp) {C D : HFSet}
    (hC : C ∈ sub.cosets) (hD : D ∈ sub.cosets) (hCD : C ≠ D) :
    HFSet.inter C D = HFSet.empty := by
  rw [mem_cosets] at hC hD
  obtain ⟨a, haG, rfl⟩ := hC
  obtain ⟨b, hbG, rfl⟩ := hD
  rcases sub.rightCoset_eq_or_disjoint haG hbG with heq | hdisj
  · exact absurd heq hCD
  · exact hdisj

/-- Todo `C ∈ cosets` tiene `card C = card H`. -/
theorem coset_card_eq (sub : HFSubgroup grp) {C : HFSet}
    (hC : C ∈ sub.cosets) :
    card C = card sub.H := by
  rw [mem_cosets] at hC
  obtain ⟨a, haG, rfl⟩ := hC
  exact sub.card_rightCoset_eq_card_H haG

-- ======================================================================
-- Teorema de Lagrange
-- ======================================================================

/-- (9) card(G) = card(cosets) · card(H). -/
theorem card_G_eq_card_H_mul_index (sub : HFSubgroup grp) :
    card grp.G = mul (card sub.cosets) (card sub.H) := by
  rw [← sub.cosets_cover]
  exact card_sUnion_uniform_partition sub.cosets (card sub.H)
    (fun C hC => sub.coset_card_eq hC)
    (fun C D hC hD hCD => sub.cosets_pairwise_disjoint hC hD hCD)

/-- (10) Teorema de Lagrange: `card(H) ∣ card(G)`. -/
theorem card_subgroup_dvd_card_group (sub : HFSubgroup grp) :
    card sub.H ∣ card grp.G :=
  ⟨card sub.cosets,
   sub.card_G_eq_card_H_mul_index.trans (mul_comm _ _)⟩

end HFSubgroup

end HFAlgebra

-- ======================================================================
-- Exports
-- ======================================================================
--
-- Público (HFSet):
--   HFSet.sUnion_insert               : sUnion (insert C F) = union C (sUnion F)
--   HFSet.card_sUnion_uniform_partition : partición uniforme → card(⋃F) = card(F) · k
--   HFSet.dvd_card_sUnion_of_all_dvd  : pairwise disjoint + p∣card C → p∣card(⋃F)
--
-- Público (HFAlgebra.HFSubgroup):
--   HFSubgroup.card_rightCoset_eq_card_H    : card(Ha) = card(H)  (a ∈ G general)
--   HFSubgroup.cosets                       : conjunto de cosetes derechos
--   HFSubgroup.mem_cosets                   : C ∈ cosets ↔ ∃ a ∈ G, C = Ha
--   HFSubgroup.index                        : card(cosets)
--   HFSubgroup.cosets_cover                 : sUnion(cosets) = G
--   HFSubgroup.cosets_pairwise_disjoint     : cosetes distintos son disjuntos
--   HFSubgroup.coset_card_eq                : ∀ C ∈ cosets, card C = card H
--   HFSubgroup.card_G_eq_card_H_mul_index   : card G = card(cosets) · card H  (9)
--   HFSubgroup.card_subgroup_dvd_card_group : card H ∣ card G  (Lagrange, 10)

-- ¿DEBERÍAMOS HACER UN EXPORT LEAN 4 PARA ESTO COMO LO HEMOS HECHO HABITUALEMNTE
-- EN OTROS PROYECTOS Y MÓDULOS? SERÍA DEL ESTILO `export HFAlgebra.HFSubgroup (...)` Y SOLO INCLUYENDO LOS RESULTADOS PÚBLICOS ANTERIORES.
