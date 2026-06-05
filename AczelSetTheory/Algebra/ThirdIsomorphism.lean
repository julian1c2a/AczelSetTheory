/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/ThirdIsomorphism.lean
-- Tercer Teorema de Isomorfía: (G/N)/(K/N) ≅ G/K.

import AczelSetTheory.Algebra.FirstIsomorphism

namespace HFAlgebra

open HFSet

variable {grp : HFGroup}

namespace HFSubgroup

-- ─────────────────────────────────────────────────────────────────
-- §1. K/N como subgrupo de G/N
-- ─────────────────────────────────────────────────────────────────

/-- `K/N = { N·k | k ∈ K }` como subgrupo de `G/N`. -/
abbrev KmodN_subgroup (sub_N sub_K : HFSubgroup grp)
    (hn_N : sub_N.isNormal)
    (_hNK : ∀ n ∈ sub_N.H, n ∈ sub_K.H) :
    HFSubgroup (quotientGroup grp sub_N hn_N) where
  H := HFSet.sep (quotientGroup grp sub_N hn_N).G
        (fun C => ∃ k ∈ sub_K.H, C = sub_N.rightCoset k)
  H_sub := fun hx => ((HFSet.mem_sep _ _ _).mp hx).1
  e_mem := by
    rw [HFSet.mem_sep]
    refine ⟨(quotientGroup grp sub_N hn_N).e_mem, grp.e, sub_K.e_mem, ?_⟩
    rfl
  op_closed := by
    intro a b ha hb
    rw [HFSet.mem_sep] at ha hb ⊢
    obtain ⟨haQ, k₁, hk₁, rfl⟩ := ha
    obtain ⟨hbQ, k₂, hk₂, rfl⟩ := hb
    have hk₁_G := sub_K.H_sub hk₁
    have hk₂_G := sub_K.H_sub hk₂
    refine ⟨(quotientGroup grp sub_N hn_N).op_closed haQ hbQ,
            grp.op k₁ k₂, sub_K.op_closed hk₁ hk₂, ?_⟩
    show (quotientGroup grp sub_N hn_N).op (sub_N.rightCoset k₁) (sub_N.rightCoset k₂)
       = sub_N.rightCoset (grp.op k₁ k₂)
    exact sub_N.quotientOp_cosetOf hn_N hk₁_G hk₂_G
  inv_closed := by
    intro a ha
    rw [HFSet.mem_sep] at ha ⊢
    obtain ⟨haQ, k, hk, rfl⟩ := ha
    have hk_G := sub_K.H_sub hk
    refine ⟨(quotientGroup grp sub_N hn_N).inv_closed haQ,
            grp.inv k, sub_K.inv_closed hk, ?_⟩
    show (quotientGroup grp sub_N hn_N).inv (sub_N.rightCoset k)
       = sub_N.rightCoset (grp.inv k)
    exact sub_N.quotientInv_cosetOf hn_N hk_G

theorem mem_KmodN_iff (sub_N sub_K : HFSubgroup grp)
    (hn_N : sub_N.isNormal) (hNK : ∀ n ∈ sub_N.H, n ∈ sub_K.H) {C : HFSet} :
    C ∈ (KmodN_subgroup sub_N sub_K hn_N hNK).H ↔
      C ∈ sub_N.cosets ∧ ∃ k ∈ sub_K.H, C = sub_N.rightCoset k := by
  show C ∈ HFSet.sep _ _ ↔ _
  rw [HFSet.mem_sep]

-- ─────────────────────────────────────────────────────────────────
-- §2. K/N es normal en G/N
-- ─────────────────────────────────────────────────────────────────

theorem KmodN_normal (sub_N sub_K : HFSubgroup grp)
    (hn_N : sub_N.isNormal) (hn_K : sub_K.isNormal)
    (hNK : ∀ n ∈ sub_N.H, n ∈ sub_K.H) :
    (KmodN_subgroup sub_N sub_K hn_N hNK).isNormal := by
  intro C D hC hD
  rw [mem_KmodN_iff] at hD
  obtain ⟨_hDQ, k, hk, rfl⟩ := hD
  have hk_G : k ∈ grp.G := sub_K.H_sub hk
  have hC' : C ∈ sub_N.cosets := hC
  obtain ⟨c, hc_G, rfl⟩ := mem_cosets.mp hC'
  -- Ahora C = sub_N.rightCoset c
  rw [mem_KmodN_iff]
  refine ⟨?_, grp.op (grp.op c k) (grp.inv c), hn_K _ k hc_G hk, ?_⟩
  · refine (quotientGroup grp sub_N hn_N).op_closed
      ((quotientGroup grp sub_N hn_N).op_closed ?_ ?_)
      ((quotientGroup grp sub_N hn_N).inv_closed ?_)
    · exact sub_N.cosetOf_mem_cosets hc_G
    · exact sub_N.cosetOf_mem_cosets hk_G
    · exact sub_N.cosetOf_mem_cosets hc_G
  show (quotientGroup grp sub_N hn_N).op
        ((quotientGroup grp sub_N hn_N).op (sub_N.rightCoset c) (sub_N.rightCoset k))
        ((quotientGroup grp sub_N hn_N).inv (sub_N.rightCoset c))
      = sub_N.rightCoset (grp.op (grp.op c k) (grp.inv c))
  show sub_N.quotientOp
        (sub_N.quotientOp (sub_N.cosetOf c) (sub_N.cosetOf k))
        (sub_N.quotientInv (sub_N.cosetOf c))
      = sub_N.cosetOf (grp.op (grp.op c k) (grp.inv c))
  rw [sub_N.quotientOp_cosetOf hn_N hc_G hk_G,
      sub_N.quotientInv_cosetOf hn_N hc_G,
      sub_N.quotientOp_cosetOf hn_N (grp.op_closed hc_G hk_G) (grp.inv_closed hc_G)]

end HFSubgroup

-- ─────────────────────────────────────────────────────────────────
-- §3. El homomorfismo φ : G/N → G/K
-- ─────────────────────────────────────────────────────────────────

namespace HFSubgroup

/-- Función subyacente del 3er TI: C ↦ K · rep_N(C). -/
private abbrev thirdIsoFun (sub_N sub_K : HFSubgroup grp) (C : HFSet) : HFSet :=
  sub_K.rightCoset (sub_N.cosetRep C)

theorem thirdIsoFun_eq (sub_N sub_K : HFSubgroup grp)
    (hNK : ∀ n ∈ sub_N.H, n ∈ sub_K.H) {g : HFSet} (hg : g ∈ grp.G) :
    thirdIsoFun sub_N sub_K (sub_N.rightCoset g) = sub_K.rightCoset g := by
  unfold thirdIsoFun
  have hC_in : sub_N.rightCoset g ∈ sub_N.cosets := sub_N.cosetOf_mem_cosets hg
  have hr_G : sub_N.cosetRep (sub_N.rightCoset g) ∈ grp.G := sub_N.cosetRep_mem_G hC_in
  have hreq : sub_N.rightCoset (sub_N.cosetRep (sub_N.rightCoset g)) = sub_N.rightCoset g :=
    sub_N.cosetRep_rightCoset_eq hC_in
  have hcoseq_N : sub_N.cosetEq (sub_N.cosetRep (sub_N.rightCoset g)) g :=
    (sub_N.cosetEq_iff_rightCoset_eq hr_G hg).mpr hreq
  have hcoseq_N' : grp.op g (grp.inv (sub_N.cosetRep (sub_N.rightCoset g))) ∈ sub_N.H := hcoseq_N
  have hcoseq_K : grp.op g (grp.inv (sub_N.cosetRep (sub_N.rightCoset g))) ∈ sub_K.H :=
    hNK _ hcoseq_N'
  exact (sub_K.cosetEq_iff_rightCoset_eq hr_G hg).mp hcoseq_K

abbrev thirdIsoMap (sub_N sub_K : HFSubgroup grp)
    (hn_N : sub_N.isNormal) (hn_K : sub_K.isNormal)
    (hNK : ∀ n ∈ sub_N.H, n ∈ sub_K.H) :
    HFGroupHom
      (quotientGroup grp sub_N hn_N)
      (quotientGroup grp sub_K hn_K) where
  f      := thirdIsoFun sub_N sub_K
  f_mem  := by
    intro C hC
    have hr_G : sub_N.cosetRep C ∈ grp.G := sub_N.cosetRep_mem_G hC
    show thirdIsoFun sub_N sub_K C ∈ sub_K.cosets
    unfold thirdIsoFun
    exact sub_K.cosetOf_mem_cosets hr_G
  f_hom  := by
    intro C₁ C₂ hC₁ hC₂
    -- Destructure C₁, C₂ as cosetes
    have hC₁' : C₁ ∈ sub_N.cosets := hC₁
    have hC₂' : C₂ ∈ sub_N.cosets := hC₂
    obtain ⟨c₁, hc₁_G, rfl⟩ := mem_cosets.mp hC₁'
    obtain ⟨c₂, hc₂_G, rfl⟩ := mem_cosets.mp hC₂'
    have hop_G : grp.op c₁ c₂ ∈ grp.G := grp.op_closed hc₁_G hc₂_G
    show thirdIsoFun sub_N sub_K
          ((quotientGroup grp sub_N hn_N).op (sub_N.rightCoset c₁) (sub_N.rightCoset c₂)) =
         (quotientGroup grp sub_K hn_K).op
           (thirdIsoFun sub_N sub_K (sub_N.rightCoset c₁))
           (thirdIsoFun sub_N sub_K (sub_N.rightCoset c₂))
    show thirdIsoFun sub_N sub_K
          (sub_N.quotientOp (sub_N.cosetOf c₁) (sub_N.cosetOf c₂)) =
         sub_K.quotientOp
           (thirdIsoFun sub_N sub_K (sub_N.rightCoset c₁))
           (thirdIsoFun sub_N sub_K (sub_N.rightCoset c₂))
    rw [sub_N.quotientOp_cosetOf hn_N hc₁_G hc₂_G]
    show thirdIsoFun sub_N sub_K (sub_N.rightCoset (grp.op c₁ c₂)) =
         sub_K.quotientOp
           (thirdIsoFun sub_N sub_K (sub_N.rightCoset c₁))
           (thirdIsoFun sub_N sub_K (sub_N.rightCoset c₂))
    rw [thirdIsoFun_eq sub_N sub_K hNK hop_G,
        thirdIsoFun_eq sub_N sub_K hNK hc₁_G,
        thirdIsoFun_eq sub_N sub_K hNK hc₂_G]
    show sub_K.rightCoset (grp.op c₁ c₂) =
         sub_K.quotientOp (sub_K.cosetOf c₁) (sub_K.cosetOf c₂)
    exact (sub_K.quotientOp_cosetOf hn_K hc₁_G hc₂_G).symm

theorem thirdIsoMap_welldefined (sub_N sub_K : HFSubgroup grp)
    (hn_N : sub_N.isNormal) (hn_K : sub_K.isNormal)
    (hNK : ∀ n ∈ sub_N.H, n ∈ sub_K.H) {g : HFSet} (hg : g ∈ grp.G) :
    (thirdIsoMap sub_N sub_K hn_N hn_K hNK).f (sub_N.rightCoset g) = sub_K.rightCoset g :=
  thirdIsoFun_eq sub_N sub_K hNK hg

-- ─────────────────────────────────────────────────────────────────
-- §4. φ es sobreyectivo
-- ─────────────────────────────────────────────────────────────────

theorem thirdIsoMap_surjective (sub_N sub_K : HFSubgroup grp)
    (hn_N : sub_N.isNormal) (hn_K : sub_K.isNormal)
    (hNK : ∀ n ∈ sub_N.H, n ∈ sub_K.H) :
    (thirdIsoMap sub_N sub_K hn_N hn_K hNK).Surjective := by
  intro D hD
  have hD' : D ∈ sub_K.cosets := hD
  obtain ⟨g, hg, rfl⟩ := mem_cosets.mp hD'
  refine ⟨sub_N.rightCoset g, sub_N.cosetOf_mem_cosets hg, ?_⟩
  exact thirdIsoMap_welldefined sub_N sub_K hn_N hn_K hNK hg

-- ─────────────────────────────────────────────────────────────────
-- §5. ker φ = K/N
-- ─────────────────────────────────────────────────────────────────

theorem thirdIsoMap_ker_eq (sub_N sub_K : HFSubgroup grp)
    (hn_N : sub_N.isNormal) (hn_K : sub_K.isNormal)
    (hNK : ∀ n ∈ sub_N.H, n ∈ sub_K.H) :
    (thirdIsoMap sub_N sub_K hn_N hn_K hNK).ker.H =
      (KmodN_subgroup sub_N sub_K hn_N hNK).H := by
  apply HFSet.extensionality
  intro C
  constructor
  · intro hC
    have hker := hC
    show C ∈ (KmodN_subgroup sub_N sub_K hn_N hNK).H
    rw [mem_KmodN_iff]
    have hC_in : C ∈ (quotientGroup grp sub_N hn_N).G :=
      ((HFSet.mem_sep _ _ _).mp hker).1
    have hf_eq : (thirdIsoMap sub_N sub_K hn_N hn_K hNK).f C =
                  (quotientGroup grp sub_K hn_K).e :=
      ((HFSet.mem_sep _ _ _).mp hker).2
    refine ⟨hC_in, ?_⟩
    have hr_G : sub_N.cosetRep C ∈ grp.G := sub_N.cosetRep_mem_G hC_in
    have hC_rep : sub_N.rightCoset (sub_N.cosetRep C) = C :=
      sub_N.cosetRep_rightCoset_eq hC_in
    have hf_eq' : sub_K.rightCoset (sub_N.cosetRep C) = sub_K.rightCoset grp.e := hf_eq
    have hcoseq_K : sub_K.cosetEq (sub_N.cosetRep C) grp.e :=
      (sub_K.cosetEq_iff_rightCoset_eq hr_G grp.e_mem).mpr hf_eq'
    have hcoseq_K' : grp.op grp.e (grp.inv (sub_N.cosetRep C)) ∈ sub_K.H := hcoseq_K
    have hrep_inv_K : grp.inv (sub_N.cosetRep C) ∈ sub_K.H := by
      rw [← grp.op_id_left (grp.inv_closed hr_G)]
      exact hcoseq_K'
    have hrep_K : sub_N.cosetRep C ∈ sub_K.H := by
      have := sub_K.inv_closed hrep_inv_K
      rwa [grp.inv_inv hr_G] at this
    exact ⟨sub_N.cosetRep C, hrep_K, hC_rep.symm⟩
  · intro hC
    rw [mem_KmodN_iff] at hC
    obtain ⟨hC_in, k, hk, rfl⟩ := hC
    have hk_G : k ∈ grp.G := sub_K.H_sub hk
    show sub_N.rightCoset k ∈ (thirdIsoMap sub_N sub_K hn_N hn_K hNK).ker.H
    show sub_N.rightCoset k ∈ HFSet.sep _ _
    rw [HFSet.mem_sep]
    refine ⟨hC_in, ?_⟩
    show (thirdIsoMap sub_N sub_K hn_N hn_K hNK).f (sub_N.rightCoset k) =
         (quotientGroup grp sub_K hn_K).e
    rw [thirdIsoMap_welldefined sub_N sub_K hn_N hn_K hNK hk_G]
    show sub_K.rightCoset k = sub_K.rightCoset grp.e
    apply (sub_K.cosetEq_iff_rightCoset_eq hk_G grp.e_mem).mp
    show grp.op grp.e (grp.inv k) ∈ sub_K.H
    rw [grp.op_id_left (grp.inv_closed hk_G)]
    exact sub_K.inv_closed hk

end HFSubgroup

end HFAlgebra
