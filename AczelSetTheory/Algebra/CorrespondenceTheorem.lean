/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/CorrespondenceTheorem.lean
-- Cuarto Teorema de Isomorfía (Teorema de Correspondencia):
-- biyección entre subgrupos de G que contienen a N ⊴ G y subgrupos de G/N.
--
-- Público:
--   HFSubgroup.preimageSubgroup        : ψ(Q) = π⁻¹(Q)
--   HFSubgroup.mem_preimageSubgroup_iff
--   HFSubgroup.N_le_preimageSubgroup   : N ⊆ ψ(Q)
--   HFSubgroup.imageSubgroup_preimage  : φ(ψ(Q)) = Q   (como HFSet)
--   HFSubgroup.preimageSubgroup_image  : ψ(φ(K)) = K   (como HFSet, cuando N ⊆ K)

import AczelSetTheory.Algebra.ThirdIsomorphism

namespace HFAlgebra

open HFSet

variable {grp : HFGroup}

namespace HFSubgroup

-- ─────────────────────────────────────────────────────────────────
-- §1. Preimagen: ψ(Q) = { g ∈ G | rightCoset g ∈ Q }
-- ─────────────────────────────────────────────────────────────────

/-- La preimagen de `Q ≤ G/N` bajo `π : G → G/N`, `g ↦ Ng`. -/
def preimageSubgroup (sub_N : HFSubgroup grp) (hn_N : sub_N.isNormal)
    (Q : HFSubgroup (quotientGroup grp sub_N hn_N)) : HFSubgroup grp where
  H := HFSet.sep grp.G (fun g => sub_N.rightCoset g ∈ Q.H)
  H_sub := fun hx => ((HFSet.mem_sep _ _ _).mp hx).1
  e_mem := by
    rw [HFSet.mem_sep]
    refine ⟨grp.e_mem, ?_⟩
    show sub_N.rightCoset grp.e ∈ Q.H
    have hid : sub_N.rightCoset grp.e = (quotientGroup grp sub_N hn_N).e := rfl
    rw [hid]; exact Q.e_mem
  op_closed := by
    intro a b ha hb
    rw [HFSet.mem_sep] at ha hb ⊢
    obtain ⟨ha_G, ha_Q⟩ := ha
    obtain ⟨hb_G, hb_Q⟩ := hb
    refine ⟨grp.op_closed ha_G hb_G, ?_⟩
    show sub_N.rightCoset (grp.op a b) ∈ Q.H
    have hop_eq : sub_N.rightCoset (grp.op a b)
                = (quotientGroup grp sub_N hn_N).op
                    (sub_N.rightCoset a) (sub_N.rightCoset b) :=
      (sub_N.quotientOp_cosetOf hn_N ha_G hb_G).symm
    rw [hop_eq]
    exact Q.op_closed ha_Q hb_Q
  inv_closed := by
    intro a ha
    rw [HFSet.mem_sep] at ha ⊢
    obtain ⟨ha_G, ha_Q⟩ := ha
    refine ⟨grp.inv_closed ha_G, ?_⟩
    show sub_N.rightCoset (grp.inv a) ∈ Q.H
    have hinv_eq : sub_N.rightCoset (grp.inv a)
                 = (quotientGroup grp sub_N hn_N).inv (sub_N.rightCoset a) :=
      (sub_N.quotientInv_cosetOf hn_N ha_G).symm
    rw [hinv_eq]
    exact Q.inv_closed ha_Q

theorem mem_preimageSubgroup_iff (sub_N : HFSubgroup grp) (hn_N : sub_N.isNormal)
    (Q : HFSubgroup (quotientGroup grp sub_N hn_N)) {g : HFSet} :
    g ∈ (preimageSubgroup sub_N hn_N Q).H ↔
      g ∈ grp.G ∧ sub_N.rightCoset g ∈ Q.H := by
  show g ∈ HFSet.sep _ _ ↔ _
  rw [HFSet.mem_sep]

-- ─────────────────────────────────────────────────────────────────
-- §2. N ⊆ ψ(Q) para todo Q ≤ G/N
-- ─────────────────────────────────────────────────────────────────

theorem N_le_preimageSubgroup (sub_N : HFSubgroup grp) (hn_N : sub_N.isNormal)
    (Q : HFSubgroup (quotientGroup grp sub_N hn_N)) :
    ∀ n ∈ sub_N.H, n ∈ (preimageSubgroup sub_N hn_N Q).H := by
  intro n hn
  rw [mem_preimageSubgroup_iff]
  have hn_G : n ∈ grp.G := sub_N.H_sub hn
  refine ⟨hn_G, ?_⟩
  -- rightCoset n = H (= rightCoset e = (quotientGroup).e) cuando n ∈ H
  have hcoset_e : sub_N.rightCoset n = sub_N.rightCoset grp.e := by
    apply (sub_N.cosetEq_iff_rightCoset_eq hn_G grp.e_mem).mp
    show grp.op grp.e (grp.inv n) ∈ sub_N.H
    rw [grp.op_id_left (grp.inv_closed hn_G)]
    exact sub_N.inv_closed hn
  rw [hcoset_e]
  show (quotientGroup grp sub_N hn_N).e ∈ Q.H
  exact Q.e_mem

-- ─────────────────────────────────────────────────────────────────
-- §3. φ(ψ(Q)) = Q   (igualdad como HFSet)
-- ─────────────────────────────────────────────────────────────────

theorem imageSubgroup_preimage (sub_N : HFSubgroup grp) (hn_N : sub_N.isNormal)
    (Q : HFSubgroup (quotientGroup grp sub_N hn_N)) :
    (KmodN_subgroup sub_N (preimageSubgroup sub_N hn_N Q) hn_N
        (N_le_preimageSubgroup sub_N hn_N Q)).H = Q.H := by
  apply HFSet.extensionality
  intro C
  constructor
  · intro hC
    rw [mem_KmodN_iff] at hC
    obtain ⟨_hC_in, g, hg_psi, rfl⟩ := hC
    rw [mem_preimageSubgroup_iff] at hg_psi
    exact hg_psi.2
  · intro hC
    rw [mem_KmodN_iff]
    have hC_in : C ∈ (quotientGroup grp sub_N hn_N).G := Q.H_sub hC
    refine ⟨hC_in, sub_N.cosetRep C, ?_, ?_⟩
    · rw [mem_preimageSubgroup_iff]
      refine ⟨sub_N.cosetRep_mem_G hC_in, ?_⟩
      rw [sub_N.cosetRep_rightCoset_eq hC_in]
      exact hC
    · exact (sub_N.cosetRep_rightCoset_eq hC_in).symm

-- ─────────────────────────────────────────────────────────────────
-- §4. ψ(φ(K)) = K   (igualdad como HFSet, cuando N ⊆ K)
-- ─────────────────────────────────────────────────────────────────

theorem preimageSubgroup_image (sub_N sub_K : HFSubgroup grp)
    (hn_N : sub_N.isNormal)
    (hNK : ∀ n ∈ sub_N.H, n ∈ sub_K.H) :
    (preimageSubgroup sub_N hn_N
        (KmodN_subgroup sub_N sub_K hn_N hNK)).H = sub_K.H := by
  apply HFSet.extensionality
  intro g
  constructor
  · intro hg
    rw [mem_preimageSubgroup_iff] at hg
    obtain ⟨hg_G, hg_phi⟩ := hg
    rw [mem_KmodN_iff] at hg_phi
    obtain ⟨_hg_in, k, hk_K, hcoseq⟩ := hg_phi
    -- hcoseq : sub_N.rightCoset g = sub_N.rightCoset k
    have hk_G : k ∈ grp.G := sub_K.H_sub hk_K
    -- De rightCoset g = rightCoset k, deducimos g · k⁻¹ ∈ N ⊆ K, luego g ∈ K
    have hcoset_eq : sub_N.cosetEq g k :=
      (sub_N.cosetEq_iff_rightCoset_eq hg_G hk_G).mpr hcoseq
    have hgk_N : grp.op k (grp.inv g) ∈ sub_N.H := hcoset_eq
    have hgk_K : grp.op k (grp.inv g) ∈ sub_K.H := hNK _ hgk_N
    -- g = (k · g⁻¹)⁻¹ · k = (k⁻¹·(k·g⁻¹)⁻¹)⁻¹... más directo:
    -- g = (k·g⁻¹)⁻¹·k·... mejor: k⁻¹·(k·g⁻¹) = g⁻¹, luego g = ((k·g⁻¹)⁻¹·k)
    -- Vía: (k·g⁻¹)⁻¹ = g·k⁻¹, así g = (k·g⁻¹)⁻¹·k = g·k⁻¹·k = g.
    have hgkinv_K : grp.inv (grp.op k (grp.inv g)) ∈ sub_K.H := sub_K.inv_closed hgk_K
    -- inv(k·g⁻¹) = g·k⁻¹
    have hinv_eq : grp.inv (grp.op k (grp.inv g)) = grp.op g (grp.inv k) := by
      rw [grp.inv_op hk_G (grp.inv_closed hg_G), grp.inv_inv hg_G]
    rw [hinv_eq] at hgkinv_K
    -- g·k⁻¹ ∈ K, k ∈ K ⇒ (g·k⁻¹)·k = g·(k⁻¹·k) = g·e = g ∈ K
    have hg_eq : grp.op (grp.op g (grp.inv k)) k = g := by
      rw [grp.op_assoc hg_G (grp.inv_closed hk_G) hk_G,
          grp.op_inv_left hk_G, grp.op_id_right hg_G]
    have := sub_K.op_closed hgkinv_K hk_K
    rwa [hg_eq] at this
  · intro hg
    rw [mem_preimageSubgroup_iff]
    have hg_G : g ∈ grp.G := sub_K.H_sub hg
    refine ⟨hg_G, ?_⟩
    rw [mem_KmodN_iff]
    refine ⟨sub_N.cosetOf_mem_cosets hg_G, g, hg, rfl⟩

end HFSubgroup

end HFAlgebra
