/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/SecondIsomorphism.lean
-- Segundo Teorema de Isomorfía: H/(H∩N) ≅ HN/N.
--
-- Diseño (paridad con Peano Combinatorics/GroupTheory/SecondIsomorphism.lean):
--   • subgroupHN sub₁ sub₂ hn : HN = { h·n | h ∈ sub₁.H, n ∈ sub₂.H } ⊆ G (subgrupo).
--   • H ≤ HN y N ≤ HN.
--   • N como subgrupo de HN.toHFGroup, normal.
--   • H ∩ N como subgrupo de H.toHFGroup, normal.
--   • secondIsoMap : G_{H/(H∩N)} → G_{HN/N}, C ↦ N · rep_{H∩N}(C).
--   • Bien-definida (porque H∩N ⊆ N), homomorfismo, biyectiva.

import AczelSetTheory.Algebra.FirstIsomorphism

namespace HFAlgebra

open HFSet

variable {grp : HFGroup}

namespace HFSubgroup

-- ─────────────────────────────────────────────────────────────────
-- §1. El producto HN como subgrupo de G
-- ─────────────────────────────────────────────────────────────────

/-- El producto `HN = { h·n | h ∈ H, n ∈ N }` como subgrupo de `G`
    (requiere `N ⊴ G` para la cerradura por producto e inverso). -/
def subgroupHN (sub₁ sub₂ : HFSubgroup grp) (hn : sub₂.isNormal) :
    HFSubgroup grp where
  H := HFSet.sep grp.G (fun x => ∃ h ∈ sub₁.H, ∃ n ∈ sub₂.H, x = grp.op h n)
  H_sub := fun hx => ((HFSet.mem_sep _ _ _).mp hx).1
  e_mem := by
    rw [HFSet.mem_sep]
    refine ⟨grp.e_mem, grp.e, sub₁.e_mem, grp.e, sub₂.e_mem, ?_⟩
    exact (grp.op_id_left grp.e_mem).symm
  op_closed := by
    intro a b ha hb
    rw [HFSet.mem_sep] at ha hb ⊢
    obtain ⟨haG, h₁, hh₁, n₁, hn₁, rfl⟩ := ha
    obtain ⟨hbG, h₂, hh₂, n₂, hn₂, rfl⟩ := hb
    have hh₁_G := sub₁.H_sub hh₁
    have hh₂_G := sub₁.H_sub hh₂
    have hn₁_G := sub₂.H_sub hn₁
    have hn₂_G := sub₂.H_sub hn₂
    have hh₂i_G := grp.inv_closed hh₂_G
    -- n₁' := h₂⁻¹ · n₁ · h₂ ∈ N por normalidad aplicada a g := h₂⁻¹
    have hconj : grp.op (grp.op (grp.inv h₂) n₁) (grp.inv (grp.inv h₂)) ∈ sub₂.H :=
      hn (grp.inv h₂) n₁ hh₂i_G hn₁
    have hn₁' : grp.op (grp.op (grp.inv h₂) n₁) h₂ ∈ sub₂.H := by
      rwa [grp.inv_inv hh₂_G] at hconj
    -- nuevo h = h₁·h₂, nuevo n = (h₂⁻¹·n₁·h₂)·n₂
    refine ⟨grp.op_closed haG hbG, grp.op h₁ h₂,
            sub₁.op_closed hh₁ hh₂,
            grp.op (grp.op (grp.op (grp.inv h₂) n₁) h₂) n₂,
            sub₂.op_closed hn₁' hn₂, ?_⟩
    -- a·b = (h₁·n₁)·(h₂·n₂) = (h₁·h₂)·(h₂⁻¹·n₁·h₂·n₂)
    have hX_G : grp.op (grp.op (grp.inv h₂) n₁) h₂ ∈ grp.G :=
      grp.op_closed (grp.op_closed hh₂i_G hn₁_G) hh₂_G
    show grp.op (grp.op h₁ n₁) (grp.op h₂ n₂) =
         grp.op (grp.op h₁ h₂) (grp.op (grp.op (grp.op (grp.inv h₂) n₁) h₂) n₂)
    calc grp.op (grp.op h₁ n₁) (grp.op h₂ n₂)
        = grp.op h₁ (grp.op n₁ (grp.op h₂ n₂)) :=
            grp.op_assoc hh₁_G hn₁_G (grp.op_closed hh₂_G hn₂_G)
      _ = grp.op h₁ (grp.op (grp.op n₁ h₂) n₂) := by
            rw [← grp.op_assoc hn₁_G hh₂_G hn₂_G]
      _ = grp.op h₁ (grp.op (grp.op (grp.op grp.e n₁) h₂) n₂) := by
            rw [grp.op_id_left hn₁_G]
      _ = grp.op h₁ (grp.op (grp.op (grp.op (grp.op h₂ (grp.inv h₂)) n₁) h₂) n₂) := by
            rw [grp.op_inv_right hh₂_G]
      _ = grp.op h₁ (grp.op (grp.op h₂ (grp.op (grp.inv h₂) n₁)) (grp.op h₂ n₂)) := by
            rw [grp.op_assoc hh₂_G hh₂i_G hn₁_G,
                grp.op_assoc (grp.op_closed hh₂_G (grp.op_closed hh₂i_G hn₁_G)) hh₂_G hn₂_G]
      _ = grp.op h₁ (grp.op h₂ (grp.op (grp.op (grp.inv h₂) n₁) (grp.op h₂ n₂))) := by
            rw [grp.op_assoc hh₂_G (grp.op_closed hh₂i_G hn₁_G)
                  (grp.op_closed hh₂_G hn₂_G)]
      _ = grp.op (grp.op h₁ h₂) (grp.op (grp.op (grp.inv h₂) n₁) (grp.op h₂ n₂)) :=
            (grp.op_assoc hh₁_G hh₂_G
              (grp.op_closed (grp.op_closed hh₂i_G hn₁_G) (grp.op_closed hh₂_G hn₂_G))).symm
      _ = grp.op (grp.op h₁ h₂) (grp.op (grp.op (grp.op (grp.inv h₂) n₁) h₂) n₂) := by
            rw [← grp.op_assoc (grp.op_closed hh₂i_G hn₁_G) hh₂_G hn₂_G]
  inv_closed := by
    intro a ha
    rw [HFSet.mem_sep] at ha ⊢
    obtain ⟨haG, h, hh, n, hn_mem, rfl⟩ := ha
    have hh_G := sub₁.H_sub hh
    have hn_G := sub₂.H_sub hn_mem
    have hhi_G := grp.inv_closed hh_G
    have hni_G := grp.inv_closed hn_G
    -- conjugado: h · n⁻¹ · h⁻¹ ∈ N
    have hni_in : grp.inv n ∈ sub₂.H := sub₂.inv_closed hn_mem
    have hconj : grp.op (grp.op h (grp.inv n)) (grp.inv h) ∈ sub₂.H :=
      hn h (grp.inv n) hh_G hni_in
    refine ⟨grp.inv_closed haG, grp.inv h, sub₁.inv_closed hh,
            grp.op (grp.op h (grp.inv n)) (grp.inv h), hconj, ?_⟩
    -- (h·n)⁻¹ = n⁻¹·h⁻¹ = h⁻¹·(h·n⁻¹·h⁻¹)
    show grp.inv (grp.op h n) = grp.op (grp.inv h) (grp.op (grp.op h (grp.inv n)) (grp.inv h))
    calc grp.inv (grp.op h n)
        = grp.op (grp.inv n) (grp.inv h) := grp.inv_op hh_G hn_G
      _ = grp.op (grp.op grp.e (grp.inv n)) (grp.inv h) := by
            rw [grp.op_id_left hni_G]
      _ = grp.op (grp.op (grp.op (grp.inv h) h) (grp.inv n)) (grp.inv h) := by
            rw [grp.op_inv_left hh_G]
      _ = grp.op (grp.op (grp.inv h) (grp.op h (grp.inv n))) (grp.inv h) := by
            rw [grp.op_assoc hhi_G hh_G hni_G]
      _ = grp.op (grp.inv h) (grp.op (grp.op h (grp.inv n)) (grp.inv h)) :=
            grp.op_assoc hhi_G (grp.op_closed hh_G hni_G) hhi_G

/-- Caracterización de pertenencia a HN. -/
theorem mem_subgroupHN_iff (sub₁ sub₂ : HFSubgroup grp) (hn : sub₂.isNormal) {x : HFSet} :
    x ∈ (sub₁.subgroupHN sub₂ hn).H ↔
      x ∈ grp.G ∧ ∃ h ∈ sub₁.H, ∃ n ∈ sub₂.H, x = grp.op h n := by
  show x ∈ HFSet.sep grp.G _ ↔ _
  rw [HFSet.mem_sep]

-- ─────────────────────────────────────────────────────────────────
-- §2. H ≤ HN y N ≤ HN
-- ─────────────────────────────────────────────────────────────────

theorem H_le_subgroupHN (sub₁ sub₂ : HFSubgroup grp) (hn : sub₂.isNormal)
    {h : HFSet} (hh : h ∈ sub₁.H) : h ∈ (sub₁.subgroupHN sub₂ hn).H := by
  rw [mem_subgroupHN_iff]
  refine ⟨sub₁.H_sub hh, h, hh, grp.e, sub₂.e_mem, ?_⟩
  exact (grp.op_id_right (sub₁.H_sub hh)).symm

theorem N_le_subgroupHN (sub₁ sub₂ : HFSubgroup grp) (hn : sub₂.isNormal)
    {n : HFSet} (hn' : n ∈ sub₂.H) : n ∈ (sub₁.subgroupHN sub₂ hn).H := by
  rw [mem_subgroupHN_iff]
  refine ⟨sub₂.H_sub hn', grp.e, sub₁.e_mem, n, hn', ?_⟩
  exact (grp.op_id_left (sub₂.H_sub hn')).symm

-- ─────────────────────────────────────────────────────────────────
-- §3. N como subgrupo normal de HN
-- ─────────────────────────────────────────────────────────────────

/-- `N` visto como subgrupo de `HN.toHFGroup`. -/
def N_in_subgroupHN (sub₁ sub₂ : HFSubgroup grp) (hn : sub₂.isNormal) :
    HFSubgroup (sub₁.subgroupHN sub₂ hn).toHFGroup where
  H          := sub₂.H
  H_sub      := fun hx => N_le_subgroupHN sub₁ sub₂ hn hx
  e_mem      := sub₂.e_mem
  op_closed  := sub₂.op_closed
  inv_closed := sub₂.inv_closed

theorem N_normal_in_subgroupHN (sub₁ sub₂ : HFSubgroup grp) (hn : sub₂.isNormal) :
    (N_in_subgroupHN sub₁ sub₂ hn).isNormal := by
  intro g n hg hn_mem
  -- g ∈ HN.toHFGroup.G = HN.H ⊆ grp.G; hn_mem : n ∈ N.H
  have hg_G : g ∈ grp.G := (sub₁.subgroupHN sub₂ hn).H_sub hg
  -- Operación y inversa de HN.toHFGroup son las de grp
  show grp.op (grp.op g n) (grp.inv g) ∈ sub₂.H
  exact hn g n hg_G hn_mem

-- ─────────────────────────────────────────────────────────────────
-- §4. H∩N como subgrupo normal de H
-- ─────────────────────────────────────────────────────────────────

/-- `H ∩ N` visto como subgrupo de `H.toHFGroup`. -/
def interHN_as_subgroup_H (sub₁ sub₂ : HFSubgroup grp) (_hn : sub₂.isNormal) :
    HFSubgroup sub₁.toHFGroup where
  H          := (sub₁.inter sub₂).H
  H_sub      := fun hx => by
    show _ ∈ sub₁.H
    have hx' : _ ∈ HFSet.inter sub₁.H sub₂.H := hx
    rw [HFSet.mem_inter] at hx'
    exact hx'.1
  e_mem      := (sub₁.inter sub₂).e_mem
  op_closed  := (sub₁.inter sub₂).op_closed
  inv_closed := (sub₁.inter sub₂).inv_closed

theorem interHN_as_subgroup_H_isNormal (sub₁ sub₂ : HFSubgroup grp) (hn : sub₂.isNormal) :
    (interHN_as_subgroup_H sub₁ sub₂ hn).isNormal := by
  intro g k hg hk
  have hg_H : g ∈ sub₁.H := hg
  have hg_G : g ∈ grp.G := sub₁.H_sub hg_H
  have hk_inter : k ∈ (sub₁.inter sub₂).H := hk
  have hk_inter' : k ∈ HFSet.inter sub₁.H sub₂.H := hk_inter
  rw [HFSet.mem_inter] at hk_inter'
  obtain ⟨hk_H, hk_N⟩ := hk_inter'
  show grp.op (grp.op g k) (grp.inv g) ∈ (sub₁.inter sub₂).H
  show grp.op (grp.op g k) (grp.inv g) ∈ HFSet.inter sub₁.H sub₂.H
  rw [HFSet.mem_inter]
  refine ⟨?_, ?_⟩
  · exact sub₁.op_closed (sub₁.op_closed hg_H hk_H) (sub₁.inv_closed hg_H)
  · exact hn g k hg_G hk_N

end HFSubgroup

-- ─────────────────────────────────────────────────────────────────
-- §5. El isomorfismo φ̄ : H/(H∩N) → HN/N
-- ─────────────────────────────────────────────────────────────────

namespace HFSubgroup

variable (sub₁ sub₂ : HFSubgroup grp) (hn : sub₂.isNormal)

/-- Función subyacente: C ↦ N · rep_{H∩N}(C) (visto como coseto en HN/N). -/
private noncomputable def secondIsoFun (C : HFSet) : HFSet :=
  (N_in_subgroupHN sub₁ sub₂ hn).rightCoset
    ((interHN_as_subgroup_H sub₁ sub₂ hn).cosetRep C)

/-- Bien-definición: φ̄((H∩N)·g) = N·g para g ∈ H. -/
theorem secondIsoFun_eq {g : HFSet} (hg : g ∈ sub₁.H) :
    secondIsoFun sub₁ sub₂ hn ((interHN_as_subgroup_H sub₁ sub₂ hn).rightCoset g) =
      (N_in_subgroupHN sub₁ sub₂ hn).rightCoset g := by
  unfold secondIsoFun
  let IK := interHN_as_subgroup_H sub₁ sub₂ hn
  let NK := N_in_subgroupHN sub₁ sub₂ hn
  -- g ∈ H.toHFGroup.G
  have hg_HG : g ∈ sub₁.toHFGroup.G := hg
  have hC_in : IK.rightCoset g ∈ IK.cosets := IK.cosetOf_mem_cosets hg_HG
  have hr_HG : IK.cosetRep (IK.rightCoset g) ∈ sub₁.toHFGroup.G :=
    IK.cosetRep_mem_G hC_in
  have hr_H : IK.cosetRep (IK.rightCoset g) ∈ sub₁.H := hr_HG
  have hreq : IK.rightCoset (IK.cosetRep (IK.rightCoset g)) = IK.rightCoset g :=
    IK.cosetRep_rightCoset_eq hC_in
  -- De rightCoset r = rightCoset g (en H/IK), saco r·g⁻¹⁻¹... actually g·(rep)⁻¹ ∈ IK ⊆ N
  have hcoseq : sub₁.toHFGroup.op g (sub₁.toHFGroup.inv (IK.cosetRep (IK.rightCoset g))) ∈ IK.H :=
    (IK.cosetEq_iff_rightCoset_eq hr_HG hg_HG).mpr hreq
  -- IK.H = (sub₁.inter sub₂).H ⊆ sub₂.H
  have hgr_in_inter : grp.op g (grp.inv (IK.cosetRep (IK.rightCoset g))) ∈
                      (sub₁.inter sub₂).H := hcoseq
  have hgr_in_inter' : grp.op g (grp.inv (IK.cosetRep (IK.rightCoset g))) ∈
                      HFSet.inter sub₁.H sub₂.H := hgr_in_inter
  rw [HFSet.mem_inter] at hgr_in_inter'
  have hgr_in_N : grp.op g (grp.inv (IK.cosetRep (IK.rightCoset g))) ∈ sub₂.H :=
    hgr_in_inter'.2
  -- Ahora pasar a NK: NK actúa sobre HN.toHFGroup. Necesitamos g, r ∈ HN.H y la igualdad de cosetes.
  have hg_HN : g ∈ (sub₁.subgroupHN sub₂ hn).H :=
    H_le_subgroupHN sub₁ sub₂ hn hg
  have hr_HN : IK.cosetRep (IK.rightCoset g) ∈ (sub₁.subgroupHN sub₂ hn).H :=
    H_le_subgroupHN sub₁ sub₂ hn hr_H
  -- NK.rightCoset r = NK.rightCoset g vía cosetEq_iff: g·r⁻¹ ∈ NK.H = sub₂.H
  exact (NK.cosetEq_iff_rightCoset_eq hr_HN hg_HN).mp hgr_in_N

/-- El homomorfismo del Segundo Teorema de Isomorfía:
    `φ̄ : H/(H∩N) → HN/N`. -/
noncomputable def secondIsoMap :
    HFGroupHom
      (quotientGroup sub₁.toHFGroup (interHN_as_subgroup_H sub₁ sub₂ hn)
        (interHN_as_subgroup_H_isNormal sub₁ sub₂ hn))
      (quotientGroup (sub₁.subgroupHN sub₂ hn).toHFGroup
        (N_in_subgroupHN sub₁ sub₂ hn) (N_normal_in_subgroupHN sub₁ sub₂ hn)) where
  f      := secondIsoFun sub₁ sub₂ hn
  f_mem  := by
    intro C hC
    let IK := interHN_as_subgroup_H sub₁ sub₂ hn
    let NK := N_in_subgroupHN sub₁ sub₂ hn
    have hr_H : IK.cosetRep C ∈ sub₁.H := IK.cosetRep_mem_G hC
    have hr_HN : IK.cosetRep C ∈ (sub₁.subgroupHN sub₂ hn).H :=
      H_le_subgroupHN sub₁ sub₂ hn hr_H
    show secondIsoFun sub₁ sub₂ hn C ∈ NK.cosets
    unfold secondIsoFun
    exact NK.cosetOf_mem_cosets hr_HN
  f_hom  := by
    intro C₁ C₂ hC₁ hC₂
    let IK := interHN_as_subgroup_H sub₁ sub₂ hn
    let NK := N_in_subgroupHN sub₁ sub₂ hn
    have hr₁_H : IK.cosetRep C₁ ∈ sub₁.H := IK.cosetRep_mem_G hC₁
    have hr₂_H : IK.cosetRep C₂ ∈ sub₁.H := IK.cosetRep_mem_G hC₂
    have hop_H : sub₁.toHFGroup.op (IK.cosetRep C₁) (IK.cosetRep C₂) ∈ sub₁.H :=
      sub₁.op_closed hr₁_H hr₂_H
    -- LHS: secondIsoFun (IK.quotientOp C₁ C₂)
    --    = secondIsoFun (IK.rightCoset (op (rep C₁) (rep C₂)))
    --    = NK.rightCoset (op (rep C₁) (rep C₂))   (por secondIsoFun_eq)
    -- RHS: NK.quotientOp (NK.rightCoset (rep C₁)) (NK.rightCoset (rep C₂))
    --    = NK.rightCoset (op (rep_NK (NK.rightCoset (rep C₁))) (rep_NK ...))
    show secondIsoFun sub₁ sub₂ hn (IK.quotientOp C₁ C₂) =
         NK.quotientOp (secondIsoFun sub₁ sub₂ hn C₁) (secondIsoFun sub₁ sub₂ hn C₂)
    -- IK.quotientOp C₁ C₂ = IK.rightCoset (op (rep C₁) (rep C₂))
    have hopeq : IK.quotientOp C₁ C₂ =
        IK.rightCoset (sub₁.toHFGroup.op (IK.cosetRep C₁) (IK.cosetRep C₂)) := rfl
    rw [hopeq, secondIsoFun_eq sub₁ sub₂ hn hop_H]
    -- RHS: definición de quotientOp en NK con representantes
    have hr₁_HN : IK.cosetRep C₁ ∈ (sub₁.subgroupHN sub₂ hn).H :=
      H_le_subgroupHN sub₁ sub₂ hn hr₁_H
    have hr₂_HN : IK.cosetRep C₂ ∈ (sub₁.subgroupHN sub₂ hn).H :=
      H_le_subgroupHN sub₁ sub₂ hn hr₂_H
    show NK.rightCoset (sub₁.toHFGroup.op (IK.cosetRep C₁) (IK.cosetRep C₂)) =
         NK.quotientOp (NK.rightCoset (IK.cosetRep C₁)) (NK.rightCoset (IK.cosetRep C₂))
    -- quotientOp_cosetOf: NK.quotientOp (NK.cosetOf a) (NK.cosetOf b) = NK.cosetOf (op a b)
    -- Tenemos rightCoset = cosetOf
    have heq := NK.quotientOp_cosetOf (N_normal_in_subgroupHN sub₁ sub₂ hn) hr₁_HN hr₂_HN
    show NK.rightCoset (sub₁.toHFGroup.op (IK.cosetRep C₁) (IK.cosetRep C₂)) =
         NK.quotientOp (NK.cosetOf (IK.cosetRep C₁)) (NK.cosetOf (IK.cosetRep C₂))
    rw [heq]
    rfl

theorem secondIsoMap_welldefined {h : HFSet} (hh : h ∈ sub₁.H) :
    (secondIsoMap sub₁ sub₂ hn).f
        ((interHN_as_subgroup_H sub₁ sub₂ hn).rightCoset h) =
      (N_in_subgroupHN sub₁ sub₂ hn).rightCoset h :=
  secondIsoFun_eq sub₁ sub₂ hn hh

/-- φ̄ es **inyectiva**. -/
theorem secondIsoMap_injective : (secondIsoMap sub₁ sub₂ hn).Injective := by
  intro C₁ C₂ hC₁ hC₂ heq
  let IK := interHN_as_subgroup_H sub₁ sub₂ hn
  let NK := N_in_subgroupHN sub₁ sub₂ hn
  have hr₁_H := IK.cosetRep_mem_G hC₁
  have hr₂_H := IK.cosetRep_mem_G hC₂
  have e₁ : IK.rightCoset (IK.cosetRep C₁) = C₁ := IK.cosetRep_rightCoset_eq hC₁
  have e₂ : IK.rightCoset (IK.cosetRep C₂) = C₂ := IK.cosetRep_rightCoset_eq hC₂
  rw [← e₁, ← e₂]
  apply (IK.cosetEq_iff_rightCoset_eq hr₁_H hr₂_H).mp
  -- Necesitamos: r₂·r₁⁻¹ ∈ IK.H = (sub₁∩sub₂).H
  show sub₁.toHFGroup.op (IK.cosetRep C₂) (sub₁.toHFGroup.inv (IK.cosetRep C₁)) ∈
       (sub₁.inter sub₂).H
  have hr₁_H_sub : IK.cosetRep C₁ ∈ sub₁.H := hr₁_H
  have hr₂_H_sub : IK.cosetRep C₂ ∈ sub₁.H := hr₂_H
  show grp.op (IK.cosetRep C₂) (grp.inv (IK.cosetRep C₁)) ∈ HFSet.inter sub₁.H sub₂.H
  rw [HFSet.mem_inter]
  refine ⟨sub₁.op_closed hr₂_H_sub (sub₁.inv_closed hr₁_H_sub), ?_⟩
  -- Para la pertenencia a sub₂.H, usamos heq:
  -- heq : secondIsoFun C₁ = secondIsoFun C₂
  --     : NK.rightCoset (rep C₁) = NK.rightCoset (rep C₂)
  have heq' : NK.rightCoset (IK.cosetRep C₁) = NK.rightCoset (IK.cosetRep C₂) := heq
  have hr₁_HN : IK.cosetRep C₁ ∈ (sub₁.subgroupHN sub₂ hn).H :=
    H_le_subgroupHN sub₁ sub₂ hn hr₁_H_sub
  have hr₂_HN : IK.cosetRep C₂ ∈ (sub₁.subgroupHN sub₂ hn).H :=
    H_le_subgroupHN sub₁ sub₂ hn hr₂_H_sub
  have hcoseq_NK : (sub₁.subgroupHN sub₂ hn).toHFGroup.op (IK.cosetRep C₂)
                    ((sub₁.subgroupHN sub₂ hn).toHFGroup.inv (IK.cosetRep C₁)) ∈ NK.H :=
    (NK.cosetEq_iff_rightCoset_eq hr₁_HN hr₂_HN).mpr heq'
  exact hcoseq_NK

/-- φ̄ es **sobreyectiva** sobre HN/N. -/
theorem secondIsoMap_surjective : (secondIsoMap sub₁ sub₂ hn).Surjective := by
  intro D hD
  let IK := interHN_as_subgroup_H sub₁ sub₂ hn
  let NK := N_in_subgroupHN sub₁ sub₂ hn
  -- D ∈ NK.cosets ⟹ ∃ x ∈ HN.H, D = NK.rightCoset x
  have hD' : D ∈ NK.cosets := hD
  obtain ⟨x, hx_HN, rfl⟩ := mem_cosets.mp hD'
  -- x ∈ HN.H ⟹ x = h·n con h ∈ sub₁.H, n ∈ sub₂.H
  have hx_in_H : x ∈ (sub₁.subgroupHN sub₂ hn).H := hx_HN
  rw [mem_subgroupHN_iff] at hx_in_H
  obtain ⟨_hx_G, h, hh, n, hn_mem, rfl⟩ := hx_in_H
  -- queremos preimagen IK.rightCoset h
  refine ⟨IK.rightCoset h, ?_, ?_⟩
  · exact IK.cosetOf_mem_cosets (show h ∈ sub₁.toHFGroup.G from hh)
  -- φ̄(IK.rightCoset h) = NK.rightCoset h, y debe ser = NK.rightCoset (h·n)
  -- Para eso: (h·n)·h⁻¹ ∈ N, y luego (en HN) cosetEq: (h·n)·h⁻¹ ∈ NK.H
  rw [secondIsoMap_welldefined sub₁ sub₂ hn hh]
  have hh_HN : h ∈ (sub₁.subgroupHN sub₂ hn).H := H_le_subgroupHN sub₁ sub₂ hn hh
  have hhn_HN : grp.op h n ∈ (sub₁.subgroupHN sub₂ hn).H := by
    rw [mem_subgroupHN_iff]
    exact ⟨grp.op_closed (sub₁.H_sub hh) (sub₂.H_sub hn_mem), h, hh, n, hn_mem, rfl⟩
  -- objetivo: NK.rightCoset h = NK.rightCoset (h·n)
  -- vía cosetEq: (h·n)·h⁻¹ ∈ NK.H = sub₂.H
  apply (NK.cosetEq_iff_rightCoset_eq hh_HN hhn_HN).mp
  show (sub₁.subgroupHN sub₂ hn).toHFGroup.op (grp.op h n)
        ((sub₁.subgroupHN sub₂ hn).toHFGroup.inv h) ∈ NK.H
  -- (h·n)·h⁻¹ = h·(n·h⁻¹) ; por normalidad: h·n·h⁻¹ ∈ N
  show grp.op (grp.op h n) (grp.inv h) ∈ sub₂.H
  exact hn h n (sub₁.H_sub hh) hn_mem

/-- **Segundo Teorema de Isomorfía**: `H/(H∩N) ≅ HN/N`. -/
theorem secondIsoMap_bijective : (secondIsoMap sub₁ sub₂ hn).Bijective :=
  ⟨secondIsoMap_injective sub₁ sub₂ hn, secondIsoMap_surjective sub₁ sub₂ hn⟩

end HFSubgroup

end HFAlgebra
