/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Zassenhaus.lean
-- Lema de la Mariposa de Zassenhaus.
--
-- Sean N ⊴ H y M ⊴ K subgrupos normales de G. Entonces:
--   (H∩K)/[(N∩K)(H∩M)] ≅ N(H∩K)/N(H∩M)
--
-- Público:
--   prodSubgroup                    : N·S como HFSubgroup cuando N ⊴ H y S ≤ H
--   mem_prodSubgroup_iff            : caracterización de membresía
--   N_le_prodSubgroup               : N ≤ N·S
--   S_le_prodSubgroup               : S ≤ N·S
--   inter_N_K_normal_in_inter_H_K   : N∩K ⊴ H∩K (cuando N ⊴ H)
--   inter_H_M_normal_in_inter_H_K   : H∩M ⊴ H∩K (cuando M ⊴ K)
--   prodNKHM                        : (N∩K)(H∩M) como subgrupo de G
--   prodNKHM_normal                 : (N∩K)(H∩M) ⊴ H∩K
--   prodN_HK                        : N(H∩K) subgrupo
--   prodN_HM                        : N(H∩M) subgrupo
--   prodN_HM_le_prodN_HK            : N(H∩M) ≤ N(H∩K)
--   prodN_HM_normal_in_prodN_HK     : N(H∩M) ⊴ N(H∩K)
--   zassenhaus_bijection            : isomorfismo de grupos cociente

import AczelSetTheory.Algebra.QuotientGroup
import AczelSetTheory.Algebra.FirstIsomorphism

namespace HFAlgebra

open HFSet

variable {grp : HFGroup}

-- ─────────────────────────────────────────────────────────────────
-- §1. Subgrupo producto N·S cuando N ⊴ H y S ≤ H
-- ─────────────────────────────────────────────────────────────────

/-- El producto `N·S = {n·s | n ∈ N, s ∈ S}` como subgrupo de `grp`,
    cuando N y S están contenidos en H, y N es normal en H. -/
def prodSubgroup (grp : HFGroup) (N S H : HFSubgroup grp)
    (_hNH : ∀ {x}, x ∈ N.H → x ∈ H.H)
    (hSH : ∀ {x}, x ∈ S.H → x ∈ H.H)
    (hNN : ∀ g n, g ∈ H.H → n ∈ N.H → grp.op (grp.op g n) (grp.inv g) ∈ N.H) :
    HFSubgroup grp where
  H := HFSet.sep grp.G (fun x => ∃ n ∈ N.H, ∃ s ∈ S.H, grp.op n s = x)
  H_sub := fun hx => by rw [HFSet.mem_sep] at hx; exact hx.1
  e_mem := by
    rw [HFSet.mem_sep]
    exact ⟨grp.e_mem, grp.e, N.e_mem, grp.e, S.e_mem,
           grp.op_id_left grp.e_mem⟩
  op_closed := by
    intro a b ha hb
    rw [HFSet.mem_sep] at ha hb ⊢
    obtain ⟨ha_G, n₁, hn₁, s₁, hs₁, ha_eq⟩ := ha
    obtain ⟨hb_G, n₂, hn₂, s₂, hs₂, hb_eq⟩ := hb
    -- a·b = (n₁·s₁)·(n₂·s₂) = (n₁·(s₁·n₂·s₁⁻¹))·(s₁·s₂)
    have hn₁_G := N.H_sub hn₁; have hn₂_G := N.H_sub hn₂
    have hs₁_G := S.H_sub hs₁; have hs₂_G := S.H_sub hs₂
    have hs₁_H := hSH hs₁
    have hs₁i_G := grp.inv_closed hs₁_G
    -- n₂' = s₁·n₂·s₁⁻¹ ∈ N
    have hn₂' : grp.op (grp.op s₁ n₂) (grp.inv s₁) ∈ N.H :=
      hNN s₁ n₂ hs₁_H hn₂
    have hn₂'_G := N.H_sub hn₂'
    -- n₁·n₂' ∈ N
    have hn₁n₂' := N.op_closed hn₁ hn₂'
    -- s₁·s₂ ∈ S
    have hs₁s₂ := S.op_closed hs₁ hs₂
    -- a·b = (n₁·n₂')·(s₁·s₂)
    have key : grp.op (grp.op n₁ s₁) (grp.op n₂ s₂) =
               grp.op (grp.op n₁ (grp.op (grp.op s₁ n₂) (grp.inv s₁)))
                      (grp.op s₁ s₂) := by
      calc grp.op (grp.op n₁ s₁) (grp.op n₂ s₂)
          = grp.op n₁ (grp.op s₁ (grp.op n₂ s₂)) :=
                grp.op_assoc hn₁_G hs₁_G (grp.op_closed hn₂_G hs₂_G)
        _ = grp.op n₁ (grp.op (grp.op s₁ n₂) s₂) := by
                rw [← grp.op_assoc hs₁_G hn₂_G hs₂_G]
        _ = grp.op n₁ (grp.op (grp.op (grp.op s₁ n₂) (grp.inv s₁)) (grp.op s₁ s₂)) := by
                congr 1; symm
                rw [grp.op_assoc (grp.op_closed hs₁_G hn₂_G) hs₁i_G
                      (grp.op_closed hs₁_G hs₂_G),
                    ← grp.op_assoc hs₁i_G hs₁_G hs₂_G,
                    grp.op_inv_left hs₁_G,
                    grp.op_id_left hs₂_G]
        _ = grp.op (grp.op n₁ (grp.op (grp.op s₁ n₂) (grp.inv s₁)))
                   (grp.op s₁ s₂) :=
                (grp.op_assoc hn₁_G (grp.op_closed (grp.op_closed hs₁_G hn₂_G) hs₁i_G)
                  (grp.op_closed hs₁_G hs₂_G)).symm
    rw [← ha_eq, ← hb_eq, key]
    exact ⟨grp.op_closed (N.H_sub hn₁n₂') (S.H_sub hs₁s₂),
           grp.op n₁ (grp.op (grp.op s₁ n₂) (grp.inv s₁)), hn₁n₂',
           grp.op s₁ s₂, hs₁s₂, rfl⟩
  inv_closed := by
    intro a ha
    rw [HFSet.mem_sep] at ha ⊢
    obtain ⟨ha_G, n, hn, s, hs, ha_eq⟩ := ha
    have hn_G := N.H_sub hn; have hs_G := S.H_sub hs
    have hs_H := hSH hs
    have hsi_G := grp.inv_closed hs_G
    have hni_mem := N.inv_closed hn
    have hsi_mem := S.inv_closed hs
    have hsi_H := H.inv_closed (hSH hs)
    -- s⁻¹·n⁻¹·s ∈ N (conjugado de n⁻¹ ∈ N por s⁻¹ ∈ H)
    have hconj : grp.op (grp.op (grp.inv s) (grp.inv n)) s ∈ N.H := by
      have h := hNN (grp.inv s) (grp.inv n) hsi_H hni_mem
      rwa [grp.inv_inv hs_G] at h
    -- inv(n·s) = s⁻¹·n⁻¹ = (s⁻¹·n⁻¹·s)·s⁻¹
    have ha_inv : grp.inv a = grp.op (grp.inv s) (grp.inv n) := by
      rw [← ha_eq]; exact grp.inv_op hn_G hs_G
    -- The inverse is (s⁻¹·n⁻¹·s)·s⁻¹ = s⁻¹·n⁻¹ = inv a
    have key : grp.op (grp.op (grp.op (grp.inv s) (grp.inv n)) s) (grp.inv s) = grp.inv a := by
      have step : grp.op (grp.op (grp.op (grp.inv s) (grp.inv n)) s) (grp.inv s) =
                  grp.op (grp.inv s) (grp.inv n) := by
        rw [grp.op_assoc (grp.op_closed hsi_G (grp.inv_closed hn_G)) hs_G hsi_G,
            grp.op_assoc hsi_G (grp.inv_closed hn_G) (grp.op_closed hs_G hsi_G),
            grp.op_inv_right hs_G, grp.op_id_right (grp.inv_closed hn_G)]
      exact step.trans ha_inv.symm
    exact ⟨key ▸ grp.op_closed (N.H_sub hconj) (S.H_sub hsi_mem),
           grp.op (grp.op (grp.inv s) (grp.inv n)) s, hconj,
           grp.inv s, hsi_mem, key⟩

/-- Caracterización de membresía en `N·S`. -/
theorem mem_prodSubgroup_iff (grp : HFGroup) (N S H : HFSubgroup grp)
    (hNH : ∀ {x}, x ∈ N.H → x ∈ H.H)
    (hSH : ∀ {x}, x ∈ S.H → x ∈ H.H)
    (hNN : ∀ g n, g ∈ H.H → n ∈ N.H → grp.op (grp.op g n) (grp.inv g) ∈ N.H)
    {x : HFSet} :
    x ∈ (prodSubgroup grp N S H hNH hSH hNN).H ↔
      x ∈ grp.G ∧ ∃ n ∈ N.H, ∃ s ∈ S.H, grp.op n s = x := by
  show x ∈ HFSet.sep grp.G _ ↔ _
  simp only [HFSet.mem_sep]

/-- `N ≤ N·S`. -/
theorem N_le_prodSubgroup (grp : HFGroup) (N S H : HFSubgroup grp)
    (hNH : ∀ {x}, x ∈ N.H → x ∈ H.H)
    (hSH : ∀ {x}, x ∈ S.H → x ∈ H.H)
    (hNN : ∀ g n, g ∈ H.H → n ∈ N.H → grp.op (grp.op g n) (grp.inv g) ∈ N.H)
    {n : HFSet} (hn : n ∈ N.H) :
    n ∈ (prodSubgroup grp N S H hNH hSH hNN).H := by
  rw [mem_prodSubgroup_iff]
  exact ⟨N.H_sub hn, n, hn, grp.e, S.e_mem, grp.op_id_right (N.H_sub hn)⟩

/-- `S ≤ N·S`. -/
theorem S_le_prodSubgroup (grp : HFGroup) (N S H : HFSubgroup grp)
    (hNH : ∀ {x}, x ∈ N.H → x ∈ H.H)
    (hSH : ∀ {x}, x ∈ S.H → x ∈ H.H)
    (hNN : ∀ g n, g ∈ H.H → n ∈ N.H → grp.op (grp.op g n) (grp.inv g) ∈ N.H)
    {s : HFSet} (hs : s ∈ S.H) :
    s ∈ (prodSubgroup grp N S H hNH hSH hNN).H := by
  rw [mem_prodSubgroup_iff]
  exact ⟨S.H_sub hs, grp.e, N.e_mem, s, hs, grp.op_id_left (S.H_sub hs)⟩

-- ─────────────────────────────────────────────────────────────────
-- §2. N∩K ⊴ H∩K (cuando N ⊴ H)
-- ─────────────────────────────────────────────────────────────────

/-- `N∩K` es normal en `H∩K`, dado N ⊴ H. -/
theorem inter_N_K_normal_in_inter_H_K {grp : HFGroup} (H K N : HFSubgroup grp)
    (_hNH : ∀ {x}, x ∈ N.H → x ∈ H.H)
    (hNN : ∀ g n, g ∈ H.H → n ∈ N.H → grp.op (grp.op g n) (grp.inv g) ∈ N.H) :
    ∀ g x, g ∈ (H.inter K).H → x ∈ (N.inter K).H →
      grp.op (grp.op g x) (grp.inv g) ∈ (N.inter K).H := by
  intro g x hg hx
  simp only [HFSubgroup.inter, HFSet.mem_inter] at hg hx ⊢
  have hg_H : g ∈ H.H := hg.1
  have hg_K : g ∈ K.H := hg.2
  have hx_N : x ∈ N.H := hx.1
  have hx_K : x ∈ K.H := hx.2
  have h_N : grp.op (grp.op g x) (grp.inv g) ∈ N.H := hNN g x hg_H hx_N
  have h_K : grp.op (grp.op g x) (grp.inv g) ∈ K.H :=
    K.op_closed (K.op_closed hg_K hx_K) (K.inv_closed hg_K)
  exact ⟨h_N, h_K⟩

/-- `H∩M` es normal en `H∩K`, dado M ⊴ K. -/
theorem inter_H_M_normal_in_inter_H_K {grp : HFGroup} (H K M : HFSubgroup grp)
    (hMM : ∀ g m, g ∈ K.H → m ∈ M.H → grp.op (grp.op g m) (grp.inv g) ∈ M.H) :
    ∀ g x, g ∈ (H.inter K).H → x ∈ (H.inter M).H →
      grp.op (grp.op g x) (grp.inv g) ∈ (H.inter M).H := by
  intro g x hg hx
  simp only [HFSubgroup.inter, HFSet.mem_inter] at hg hx ⊢
  have hg_H := hg.1; have hg_K := hg.2
  have hx_H := hx.1; have hx_M := hx.2
  have h_H : grp.op (grp.op g x) (grp.inv g) ∈ H.H :=
    H.op_closed (H.op_closed hg_H hx_H) (H.inv_closed hg_H)
  have h_M : grp.op (grp.op g x) (grp.inv g) ∈ M.H := hMM g x hg_K hx_M
  exact ⟨h_H, h_M⟩

-- ─────────────────────────────────────────────────────────────────
-- §3. Abreviaturas locales y (N∩K)(H∩M) ⊴ H∩K
-- ─────────────────────────────────────────────────────────────────

section Zassenhaus

variable {grp : HFGroup}
variable (H K N M : HFSubgroup grp)
variable (hNH : ∀ {x : HFSet}, x ∈ N.H → x ∈ H.H)
variable (hMK : ∀ {x : HFSet}, x ∈ M.H → x ∈ K.H)
variable (hMH : ∀ {x : HFSet}, x ∈ M.H → x ∈ H.H)
variable (hNN : ∀ g n, g ∈ H.H → n ∈ N.H → grp.op (grp.op g n) (grp.inv g) ∈ N.H)
variable (hMM : ∀ g m, g ∈ K.H → m ∈ M.H → grp.op (grp.op g m) (grp.inv g) ∈ M.H)

/-- El subgrupo `(N∩K)(H∩M)` dentro de `G`. -/
def prodNKHM : HFSubgroup grp :=
  prodSubgroup grp (N.inter K) (H.inter M) (H.inter K)
    (fun {x} ha =>
      (HFSet.mem_inter H.H K.H x).mpr
        ⟨hNH ((HFSet.mem_inter N.H K.H x).mp ha).1,
         ((HFSet.mem_inter N.H K.H x).mp ha).2⟩)
    (fun {x} ha =>
      (HFSet.mem_inter H.H K.H x).mpr
        ⟨((HFSet.mem_inter H.H M.H x).mp ha).1,
         hMK ((HFSet.mem_inter H.H M.H x).mp ha).2⟩)
    (fun g n hg hn =>
      let hg' := (HFSet.mem_inter H.H K.H g).mp hg
      let hn' := (HFSet.mem_inter N.H K.H n).mp hn
      (HFSet.mem_inter N.H K.H _).mpr
        ⟨hNN g n hg'.1 hn'.1,
         K.op_closed (K.op_closed hg'.2 hn'.2) (K.inv_closed hg'.2)⟩)

/-- `(N∩K)(H∩M)` es normal en `H∩K`. -/
theorem prodNKHM_normal
    (hMM : ∀ g m, g ∈ K.H → m ∈ M.H → grp.op (grp.op g m) (grp.inv g) ∈ M.H) :
    ∀ g x, g ∈ (H.inter K).H → x ∈ (prodNKHM H K N M hNH hMK hNN).H →
      grp.op (grp.op g x) (grp.inv g) ∈ (prodNKHM H K N M hNH hMK hNN).H := by
  intro g x hg hx
  have hx' : x ∈ (prodSubgroup grp (N.inter K) (H.inter M) (H.inter K) _ _ _).H := hx
  obtain ⟨_, a, ha_NK, b, hb_HM, hab⟩ :=
    (mem_prodSubgroup_iff grp (N.inter K) (H.inter M) (H.inter K)
      (fun ha => by show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; have ha_ := (HFSet.mem_inter N.H K.H _).mp ha; exact ⟨hNH ha_.1, ha_.2⟩)
      (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; exact ⟨ha.1, hMK ha.2⟩)
      _).mp hx'
  simp only [HFSubgroup.inter, HFSet.mem_inter] at hg
  have hg_H := hg.1; have hg_K := hg.2
  have hg_G := H.H_sub hg_H
  simp only [HFSubgroup.inter, HFSet.mem_inter] at ha_NK hb_HM
  have ha_N := ha_NK.1; have ha_K := ha_NK.2
  have hb_H := hb_HM.1; have hb_M := hb_HM.2
  have ha_G := N.H_sub ha_N; have hb_G := H.H_sub hb_H
  -- g·(a·b)·g⁻¹ = (g·a·g⁻¹)·(g·b·g⁻¹)
  have hconj_a : grp.op (grp.op g a) (grp.inv g) ∈ (N.inter K).H := by
    exact (HFSet.mem_inter N.H K.H _).mpr
      ⟨hNN g a hg_H ha_N, K.op_closed (K.op_closed hg_K ha_K) (K.inv_closed hg_K)⟩
  have hconj_b : grp.op (grp.op g b) (grp.inv g) ∈ (H.inter M).H := by
    exact (HFSet.mem_inter H.H M.H _).mpr
      ⟨H.op_closed (H.op_closed hg_H hb_H) (H.inv_closed hg_H), hMM g b hg_K hb_M⟩
  have hconj_split :
      grp.op (grp.op g x) (grp.inv g) =
      grp.op (grp.op (grp.op g a) (grp.inv g)) (grp.op (grp.op g b) (grp.inv g)) := by
    rw [← hab]
    have hgi := grp.inv_closed hg_G
    have hgag := grp.op_closed hg_G ha_G
    have hgbg := grp.op_closed (grp.op_closed hg_G hb_G) hgi
    symm
    calc grp.op (grp.op (grp.op g a) (grp.inv g)) (grp.op (grp.op g b) (grp.inv g))
        = grp.op (grp.op g a) (grp.op (grp.inv g) (grp.op (grp.op g b) (grp.inv g))) :=
              grp.op_assoc hgag hgi hgbg
      _ = grp.op (grp.op g a)
                 (grp.op (grp.op (grp.inv g) (grp.op g b)) (grp.inv g)) := by
              rw [← grp.op_assoc hgi (grp.op_closed hg_G hb_G) hgi]
      _ = grp.op (grp.op g a)
                 (grp.op (grp.op (grp.op (grp.inv g) g) b) (grp.inv g)) := by
              rw [← grp.op_assoc hgi hg_G hb_G]
      _ = grp.op (grp.op g a) (grp.op (grp.op grp.e b) (grp.inv g)) := by
              rw [grp.op_inv_left hg_G]
      _ = grp.op (grp.op g a) (grp.op b (grp.inv g)) := by
              rw [grp.op_id_left hb_G]
      _ = grp.op (grp.op (grp.op g a) b) (grp.inv g) :=
              (grp.op_assoc hgag hb_G hgi).symm
      _ = grp.op (grp.op g (grp.op a b)) (grp.inv g) := by
              rw [grp.op_assoc hg_G ha_G hb_G]
  show grp.op (grp.op g x) (grp.inv g) ∈ (prodSubgroup grp (N.inter K) (H.inter M) (H.inter K) _ _ _).H
  have hconj_a_N : grp.op (grp.op g a) (grp.inv g) ∈ N.H := by
    simp only [HFSubgroup.inter, HFSet.mem_inter] at hconj_a; exact hconj_a.1
  have hconj_b_H : grp.op (grp.op g b) (grp.inv g) ∈ H.H := by
    simp only [HFSubgroup.inter, HFSet.mem_inter] at hconj_b; exact hconj_b.1
  rw [hconj_split]
  exact (mem_prodSubgroup_iff grp (N.inter K) (H.inter M) (H.inter K)
    (fun ha => by show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; have ha_ := (HFSet.mem_inter N.H K.H _).mp ha; exact ⟨hNH ha_.1, ha_.2⟩)
    (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; exact ⟨ha.1, hMK ha.2⟩)
    _).mpr
    ⟨grp.op_closed (N.H_sub hconj_a_N) (H.H_sub hconj_b_H),
     grp.op (grp.op g a) (grp.inv g), hconj_a,
     grp.op (grp.op g b) (grp.inv g), hconj_b, rfl⟩

-- ─────────────────────────────────────────────────────────────────
-- §4. Subgrupos producto N(H∩K) y N(H∩M)
-- ─────────────────────────────────────────────────────────────────

/-- `N(H∩K)` como subgrupo de `grp`. -/
def prodN_HK : HFSubgroup grp :=
  prodSubgroup grp N (H.inter K) H hNH
    (fun ha => by
      change _ ∈ HFSet.inter H.H K.H at ha
      rw [HFSet.mem_inter] at ha; exact ha.1)
    hNN

/-- `N(H∩M)` como subgrupo de `grp`. -/
def prodN_HM : HFSubgroup grp :=
  prodSubgroup grp N (H.inter M) H hNH
    (fun ha => by
      change _ ∈ HFSet.inter H.H M.H at ha
      rw [HFSet.mem_inter] at ha; exact ha.1)
    hNN

/-- `N(H∩M) ≤ N(H∩K)` cuando H∩M ≤ H∩K. -/
theorem prodN_HM_le_prodN_HK {x : HFSet}
    (hMK : ∀ {x}, x ∈ M.H → x ∈ K.H)
    (hx : x ∈ (prodN_HM H N M hNH hNN).H) :
    x ∈ (prodN_HK H K N hNH hNN).H := by
  have hx' : x ∈ (prodSubgroup grp N (H.inter M) H _ _ _).H := hx
  obtain ⟨hx_G, n, hn, m, hm_HM, heq⟩ :=
    (mem_prodSubgroup_iff grp N (H.inter M) H hNH
      (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
      hNN).mp hx'
  have hm_HK : m ∈ (H.inter K).H := by
    change _ ∈ HFSet.inter H.H M.H at hm_HM
    rw [HFSet.mem_inter] at hm_HM
    change _ ∈ HFSet.inter H.H K.H
    rw [HFSet.mem_inter]; exact ⟨hm_HM.1, hMK hm_HM.2⟩
  show x ∈ (prodSubgroup grp N (H.inter K) H _ _ _).H
  exact (mem_prodSubgroup_iff grp N (H.inter K) H hNH
    (fun ha => by change _ ∈ HFSet.inter H.H K.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
    hNN).mpr ⟨hx_G, n, hn, m, hm_HK, heq⟩

-- ─────────────────────────────────────────────────────────────────
-- §5. N(H∩M) ⊴ N(H∩K)
-- ─────────────────────────────────────────────────────────────────

/-- N es normal en N(H∩K) (lema auxiliar). -/
private theorem N_normal_in_prodN_HK :
    ∀ g n, g ∈ (prodN_HK H K N hNH hNN).H → n ∈ N.H →
      grp.op (grp.op g n) (grp.inv g) ∈ N.H := by
  intro g n hg hn
  have hg' : g ∈ (prodSubgroup grp N (H.inter K) H _ _ _).H := hg
  obtain ⟨_, a, ha, b, hb, hg_eq⟩ :=
    (mem_prodSubgroup_iff grp N (H.inter K) H hNH
      (fun ha => by change _ ∈ HFSet.inter H.H K.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
      hNN).mp hg'
  have hg_H : g ∈ H.H := by
    rw [← hg_eq]
    exact H.op_closed (hNH ha) (by
      change _ ∈ HFSet.inter H.H K.H at hb
      rw [HFSet.mem_inter] at hb; exact hb.1)
  exact hNN g n hg_H hn

/-- `N(H∩M) ⊴ N(H∩K)`. -/
theorem prodN_HM_normal_in_prodN_HK
    (_hMK : ∀ {x}, x ∈ M.H → x ∈ K.H)
    (hMM : ∀ g m, g ∈ K.H → m ∈ M.H → grp.op (grp.op g m) (grp.inv g) ∈ M.H) :
    ∀ g y, g ∈ (prodN_HK H K N hNH hNN).H →
           y ∈ (prodN_HM H N M hNH hNN).H →
           grp.op (grp.op g y) (grp.inv g) ∈ (prodN_HM H N M hNH hNN).H := by
  intro g y hg hy
  have hg' : g ∈ (prodSubgroup grp N (H.inter K) H _ _ _).H := hg
  have hy' : y ∈ (prodSubgroup grp N (H.inter M) H _ _ _).H := hy
  obtain ⟨_, n_g, hn_g, k_g, hk_g, hg_eq⟩ :=
    (mem_prodSubgroup_iff grp N (H.inter K) H hNH
      (fun ha => by change _ ∈ HFSet.inter H.H K.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
      hNN).mp hg'
  obtain ⟨_, n_y, hn_y, m_y, hm_y, hy_eq⟩ :=
    (mem_prodSubgroup_iff grp N (H.inter M) H hNH
      (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
      hNN).mp hy'
  have hng_G := N.H_sub hn_g; have hng_H := hNH hn_g
  simp only [HFSubgroup.inter, HFSet.mem_inter] at hk_g hm_y
  have hkg_G := H.H_sub hk_g.1; have hkg_H := hk_g.1; have hkg_K := hk_g.2
  have hny_G := N.H_sub hn_y
  have hmy_H := hm_y.1; have hmy_M := hm_y.2; have hmy_G := H.H_sub hmy_H
  -- n_y' = k_g·n_y·k_g⁻¹ ∈ N
  have hny' : grp.op (grp.op k_g n_y) (grp.inv k_g) ∈ N.H := hNN k_g n_y hkg_H hn_y
  -- m_y' = k_g·m_y·k_g⁻¹ ∈ H∩M
  have hmy'_M : grp.op (grp.op k_g m_y) (grp.inv k_g) ∈ M.H := hMM k_g m_y hkg_K hmy_M
  have hmy'_H : grp.op (grp.op k_g m_y) (grp.inv k_g) ∈ H.H :=
    H.op_closed (H.op_closed hkg_H hmy_H) (H.inv_closed hkg_H)
  have hmy'_HM : grp.op (grp.op k_g m_y) (grp.inv k_g) ∈ (H.inter M).H := by
    change _ ∈ HFSet.inter H.H M.H; rw [HFSet.mem_inter]; exact ⟨hmy'_H, hmy'_M⟩
  let m_y' := grp.op (grp.op k_g m_y) (grp.inv k_g)
  have hmy'_G := H.H_sub hmy'_H
  -- α = m_y'·n_g⁻¹·m_y'⁻¹ ∈ N
  have hα : grp.op (grp.op m_y' (grp.inv n_g)) (grp.inv m_y') ∈ N.H :=
    hNN m_y' (grp.inv n_g) hmy'_H (N.inv_closed hn_g)
  -- n_pair = n_g · n_y' · α ∈ N
  have hn_pair : grp.op n_g (grp.op (grp.op (grp.op k_g n_y) (grp.inv k_g))
                                     (grp.op (grp.op m_y' (grp.inv n_g)) (grp.inv m_y')))
      ∈ N.H := N.op_closed hn_g (N.op_closed hny' hα)
  -- identidad algebraica: n_pair · m_y' = g·y·g⁻¹
  have hident : grp.op
      (grp.op n_g (grp.op (grp.op (grp.op k_g n_y) (grp.inv k_g))
                          (grp.op (grp.op m_y' (grp.inv n_g)) (grp.inv m_y'))))
      m_y' =
      grp.op (grp.op g y) (grp.inv g) := by
    have hinvkg_G := grp.inv_closed hkg_G
    have hinvng_G := grp.inv_closed hng_G
    have hinvmy'_G := grp.inv_closed hmy'_G
    have hny'_G := N.H_sub hny'
    -- (m_y'·n_g⁻¹·m_y'⁻¹)·m_y' = m_y'·n_g⁻¹
    have hcancel : grp.op (grp.op (grp.op m_y' (grp.inv n_g)) (grp.inv m_y')) m_y' =
                   grp.op m_y' (grp.inv n_g) := by
      rw [grp.op_assoc (grp.op_closed hmy'_G hinvng_G) hinvmy'_G hmy'_G,
          grp.op_inv_left hmy'_G,
          grp.op_id_right (grp.op_closed hmy'_G hinvng_G)]
    rw [grp.op_assoc hng_G
          (grp.op_closed (grp.op_closed (grp.op_closed hkg_G hny_G) hinvkg_G)
                         (grp.op_closed (grp.op_closed hmy'_G hinvng_G) hinvmy'_G))
          hmy'_G,
        grp.op_assoc (grp.op_closed (grp.op_closed hkg_G hny_G) hinvkg_G)
          (grp.op_closed (grp.op_closed hmy'_G hinvng_G) hinvmy'_G)
          hmy'_G,
        hcancel,
        ← grp.op_assoc (grp.op_closed (grp.op_closed hkg_G hny_G) hinvkg_G)
            hmy'_G hinvng_G,
        ← grp.op_assoc hng_G
            (grp.op_closed (grp.op_closed (grp.op_closed hkg_G hny_G) hinvkg_G) hmy'_G)
            hinvng_G]
    -- LHS: n_g·(k_g·n_y·k_g⁻¹·m_y')·n_g⁻¹, m_y' = k_g·m_y·k_g⁻¹
    -- Fold: (k_g·n_y·k_g⁻¹)·(k_g·m_y·k_g⁻¹) = k_g·(n_y·m_y)·k_g⁻¹
    have hfold : grp.op (grp.op (grp.op k_g n_y) (grp.inv k_g)) m_y' =
                 grp.op (grp.op k_g (grp.op n_y m_y)) (grp.inv k_g) := by
      show grp.op (grp.op (grp.op k_g n_y) (grp.inv k_g))
                  (grp.op (grp.op k_g m_y) (grp.inv k_g)) =
           grp.op (grp.op k_g (grp.op n_y m_y)) (grp.inv k_g)
      rw [grp.op_assoc (grp.op_closed hkg_G hny_G) hinvkg_G
            (grp.op_closed (grp.op_closed hkg_G hmy_G) hinvkg_G),
          grp.op_assoc hkg_G hmy_G hinvkg_G,
          ← grp.op_assoc hinvkg_G hkg_G (grp.op_closed hmy_G hinvkg_G),
          grp.op_inv_left hkg_G, grp.op_id_left (grp.op_closed hmy_G hinvkg_G),
          ← grp.op_assoc (grp.op_closed hkg_G hny_G) hmy_G hinvkg_G,
          grp.op_assoc hkg_G hny_G hmy_G]
    rw [hfold, ← hg_eq, ← hy_eq, grp.inv_op hng_G hkg_G,
        grp.op_assoc hng_G (grp.op_closed (grp.op_closed hkg_G (grp.op_closed hny_G hmy_G)) hinvkg_G)
          (grp.inv_closed hng_G),
        grp.op_assoc (grp.op_closed hkg_G (grp.op_closed hny_G hmy_G)) hinvkg_G (grp.inv_closed hng_G),
        grp.op_assoc hkg_G (grp.op_closed hny_G hmy_G) (grp.op_closed hinvkg_G (grp.inv_closed hng_G)),
        ← grp.op_assoc hng_G hkg_G
            (grp.op_closed (grp.op_closed hny_G hmy_G) (grp.op_closed hinvkg_G (grp.inv_closed hng_G))),
        ← grp.op_assoc (grp.op_closed hng_G hkg_G) (grp.op_closed hny_G hmy_G)
            (grp.op_closed hinvkg_G (grp.inv_closed hng_G))]
  show grp.op (grp.op g y) (grp.inv g) ∈ (prodSubgroup grp N (H.inter M) H _ _ _).H
  have hg_G : g ∈ grp.G := hg_eq ▸ grp.op_closed hng_G hkg_G
  have hy_G : y ∈ grp.G := hy_eq ▸ grp.op_closed hny_G hmy_G
  exact (mem_prodSubgroup_iff grp N (H.inter M) H hNH
    (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
    hNN).mpr
    ⟨grp.op_closed (grp.op_closed hg_G hy_G) (grp.inv_closed hg_G),
     grp.op n_g (grp.op (grp.op (grp.op k_g n_y) (grp.inv k_g))
                        (grp.op (grp.op m_y' (grp.inv n_g)) (grp.inv m_y'))),
     hn_pair, m_y', hmy'_HM, hident⟩

-- ─────────────────────────────────────────────────────────────────
-- §6. Lemas privados para la biyección
-- ─────────────────────────────────────────────────────────────────

/-- Todos los elementos de `(N∩K)(H∩M)` están en `H∩K`. -/
private theorem prodNKHM_le_HK {x : HFSet}
    (hx : x ∈ (prodNKHM H K N M hNH hMK hNN).H) :
    x ∈ (H.inter K).H := by
  have hx' : x ∈ (prodSubgroup grp (N.inter K) (H.inter M) (H.inter K) _ _ _).H := hx
  obtain ⟨_, a, ha_NK, b, hb_HM, heq⟩ :=
    (mem_prodSubgroup_iff grp (N.inter K) (H.inter M) (H.inter K)
      (fun ha => by show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; have ha_ := (HFSet.mem_inter N.H K.H _).mp ha; exact ⟨hNH ha_.1, ha_.2⟩)
      (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; exact ⟨ha.1, hMK ha.2⟩)
      _).mp hx'
  simp only [HFSubgroup.inter, HFSet.mem_inter] at ha_NK hb_HM
  have ha_N := ha_NK.1; have ha_K := ha_NK.2
  have hb_H := hb_HM.1; have hb_M := hb_HM.2
  rw [← heq]
  exact (HFSet.mem_inter H.H K.H _).mpr ⟨H.op_closed (hNH ha_N) hb_H, K.op_closed ha_K (hMK hb_M)⟩

/-- `(N∩K)(H∩M)` como `HFSubgroup` de `(H.inter K).toHFGroup`. -/
private def prodNKHM_in_HK : HFSubgroup (H.inter K).toHFGroup where
  H := (prodNKHM H K N M hNH hMK hNN).H
  H_sub := fun {_x} ha => prodNKHM_le_HK (H := H) (K := K) (N := N) (M := M)
                            (hNH := hNH) (hMK := hMK) (hNN := hNN) ha
  e_mem := (prodNKHM H K N M hNH hMK hNN).e_mem
  op_closed := fun ha hb => (prodNKHM H K N M hNH hMK hNN).op_closed ha hb
  inv_closed := fun ha => (prodNKHM H K N M hNH hMK hNN).inv_closed ha

/-- `N(H∩M)` como `HFSubgroup` de `(prodN_HK H K N).toHFGroup`. -/
private def prodN_HM_in_prodN_HK : HFSubgroup (prodN_HK H K N hNH hNN).toHFGroup where
  H := (prodN_HM H N M hNH hNN).H
  H_sub := fun {x} ha => @prodN_HM_le_prodN_HK grp H K N M hNH hNN x hMK ha
  e_mem := (prodN_HM H N M hNH hNN).e_mem
  op_closed := fun ha hb => (prodN_HM H N M hNH hNN).op_closed ha hb
  inv_closed := fun ha => (prodN_HM H N M hNH hNN).inv_closed ha

/-- `(N∩K)(H∩M) ≤ N(H∩M)`. -/
private theorem prodNKHM_sub_prodN_HM {x : HFSet}
    (hx : x ∈ (prodNKHM H K N M hNH hMK hNN).H) :
    x ∈ (prodN_HM H N M hNH hNN).H := by
  have hx' : x ∈ (prodSubgroup grp (N.inter K) (H.inter M) (H.inter K) _ _ _).H := hx
  obtain ⟨hx_G, a, ha_NK, b, hb_HM, heq⟩ :=
    (mem_prodSubgroup_iff grp (N.inter K) (H.inter M) (H.inter K)
      (fun ha => by show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; have ha_ := (HFSet.mem_inter N.H K.H _).mp ha; exact ⟨hNH ha_.1, ha_.2⟩)
      (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; exact ⟨ha.1, hMK ha.2⟩)
      _).mp hx'
  simp only [HFSubgroup.inter, HFSet.mem_inter] at ha_NK
  show x ∈ (prodSubgroup grp N (H.inter M) H _ _ _).H
  exact (mem_prodSubgroup_iff grp N (H.inter M) H hNH
    (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
    hNN).mpr ⟨hx_G, a, ha_NK.1, b, hb_HM, heq⟩

/-- Lema clave: `(H∩K) ∩ N(H∩M) ≤ (N∩K)(H∩M)`. -/
private theorem HK_inter_prodN_HM_le_prodNKHM {x : HFSet}
    (hx_HK : x ∈ (H.inter K).H)
    (hx_NHM : x ∈ (prodN_HM H N M hNH hNN).H) :
    x ∈ (prodNKHM H K N M hNH hMK hNN).H := by
  have hx_NHM' : x ∈ (prodSubgroup grp N (H.inter M) H _ _ _).H := hx_NHM
  obtain ⟨_, n, hn_N, m, hm_HM, heq⟩ :=
    (mem_prodSubgroup_iff grp N (H.inter M) H hNH
      (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
      hNN).mp hx_NHM'
  have hm_HM_sub : m ∈ (H.inter M).H := hm_HM
  simp only [HFSubgroup.inter, HFSet.mem_inter] at hx_HK hm_HM
  have hx_K := hx_HK.2
  have hm_M := hm_HM.2
  have hm_K := hMK hm_M
  have hn_G := N.H_sub hn_N
  have hm_G := M.H_sub hm_M
  have hx_G := H.H_sub hx_HK.1
  -- n = x·m⁻¹
  have hn_eq : n = grp.op x (grp.inv m) := by
    rw [← heq,
        grp.op_assoc hn_G hm_G (grp.inv_closed hm_G),
        grp.op_inv_right hm_G, grp.op_id_right hn_G]
  -- n ∈ K
  have hn_K : n ∈ K.H := hn_eq ▸ K.op_closed hx_K (K.inv_closed hm_K)
  -- n ∈ N∩K
  have hn_NK : n ∈ (N.inter K).H := by simp only [HFSubgroup.inter, HFSet.mem_inter]; exact ⟨hn_N, hn_K⟩
  have hm_HM_sub : m ∈ (H.inter M).H := by simp only [HFSubgroup.inter, HFSet.mem_inter]; exact hm_HM
  show x ∈ (prodSubgroup grp (N.inter K) (H.inter M) (H.inter K) _ _ _).H
  exact (mem_prodSubgroup_iff grp (N.inter K) (H.inter M) (H.inter K)
    (fun ha => by show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; have ha_ := (HFSet.mem_inter N.H K.H _).mp ha; exact ⟨hNH ha_.1, ha_.2⟩)
    (fun ha => by change _ ∈ HFSet.inter H.H M.H at ha; rw [HFSet.mem_inter] at ha; show _ ∈ (H.inter K).H; rw [show (H.inter K).H = HFSet.inter H.H K.H from rfl, HFSet.mem_inter]; exact ⟨ha.1, hMK ha.2⟩)
    _).mpr ⟨hx_G, n, hn_NK, m, hm_HM_sub, heq⟩

/-- `H∩K ≤ N(H∩K)`. -/
private theorem HK_le_prodN_HK {x : HFSet} (hx : x ∈ (H.inter K).H) :
    x ∈ (prodN_HK H K N hNH hNN).H :=
  S_le_prodSubgroup grp N (H.inter K) H hNH (fun ha => by
    simp only [HFSubgroup.inter, HFSet.mem_inter] at ha; exact ha.1) hNN hx

-- ─────────────────────────────────────────────────────────────────
-- §7. La biyección de Zassenhaus
-- ─────────────────────────────────────────────────────────────────

/-- Normalidad de `(N∩K)(H∩M)` en `(H.inter K).toHFGroup` (para el grupo cociente). -/
private theorem prodNKHM_in_HK_isNormal
    (hMM : ∀ g m, g ∈ K.H → m ∈ M.H → grp.op (grp.op g m) (grp.inv g) ∈ M.H) :
    (prodNKHM_in_HK H K N M hNH hMK hNN).isNormal := by
  intro g n hg hn
  exact @prodNKHM_normal grp H K N M hNH hMK hNN hMM g n hg hn

/-- Normalidad de `N(H∩M)` en `(prodN_HK H K N).toHFGroup`. -/
private theorem prodN_HM_in_prodN_HK_isNormal
    (hMM : ∀ g m, g ∈ K.H → m ∈ M.H → grp.op (grp.op g m) (grp.inv g) ∈ M.H) :
    (prodN_HM_in_prodN_HK H K N M hNH hMK hNN).isNormal := by
  intro g n hg hn
  exact @prodN_HM_normal_in_prodN_HK grp H K N M hNH hNN hMK hMM g n hg hn

/-- Bien-definición de la función de Zassenhaus:
    Para `k ∈ (H∩K).H`, `zassenhaus_fun(rightCoset k) = rightCoset k` en N(H∩K)/N(H∩M). -/
private theorem zassenhaus_fun_eq {k : HFSet} (hk : k ∈ (H.inter K).H) :
    let _hn₁ := @prodNKHM_in_HK_isNormal grp H K N M hNH hMK hNN hMM
    let _hn₂ := @prodN_HM_in_prodN_HK_isNormal grp H K N M hNH hMK hNN hMM
    let sub₁ := prodNKHM_in_HK H K N M hNH hMK hNN
    let sub₂ := prodN_HM_in_prodN_HK H K N M hNH hMK hNN
    let _hk_NHK := @HK_le_prodN_HK grp H K N hNH hNN k hk
    sub₂.rightCoset (sub₁.cosetRep (sub₁.rightCoset k)) =
    sub₂.rightCoset k := by
  intro _hn₁ _hn₂ sub₁ sub₂ hk_NHK
  -- r = cosetRep (rightCoset k); rightCoset r = rightCoset k
  have hC_mem : sub₁.rightCoset k ∈ sub₁.cosets :=
    sub₁.cosetOf_mem_cosets hk
  have hr_HK : sub₁.cosetRep (sub₁.rightCoset k) ∈ (H.inter K).H :=
    sub₁.cosetRep_mem_G hC_mem
  have hreq : sub₁.rightCoset (sub₁.cosetRep (sub₁.rightCoset k)) =
              sub₁.rightCoset k :=
    sub₁.cosetRep_rightCoset_eq hC_mem
  -- cosetEq r k: k · r⁻¹ ∈ prodNKHM
  have hcoseq : grp.op k (grp.inv (sub₁.cosetRep (sub₁.rightCoset k))) ∈
      (prodNKHM_in_HK H K N M hNH hMK hNN).H :=
    (sub₁.cosetEq_iff_rightCoset_eq hr_HK hk).mpr hreq
  -- k · r⁻¹ ∈ prodNKHM ⊆ prodN_HM
  have hcoseq_NHM : grp.op k (grp.inv (sub₁.cosetRep (sub₁.rightCoset k))) ∈
      (prodN_HM_in_prodN_HK H K N M hNH hMK hNN).H :=
    @prodNKHM_sub_prodN_HM grp H K N M hNH hMK hNN _ hcoseq
  -- sub₂.cosetEq r k: rightCoset r = rightCoset k in sub₂
  apply (sub₂.cosetEq_iff_rightCoset_eq (@HK_le_prodN_HK grp H K N hNH hNN _ hr_HK)
           hk_NHK).mp
  exact hcoseq_NHM

/-- El homomorfismo de Zassenhaus. -/
private def zassenhaus_hom :
    HFGroupHom
      (quotientGroup (H.inter K).toHFGroup
         (prodNKHM_in_HK H K N M hNH hMK hNN)
         (@prodNKHM_in_HK_isNormal grp H K N M hNH hMK hNN hMM))
      (quotientGroup (prodN_HK H K N hNH hNN).toHFGroup
         (prodN_HM_in_prodN_HK H K N M hNH hMK hNN)
         (@prodN_HM_in_prodN_HK_isNormal grp H K N M hNH hMK hNN hMM)) where
  f := fun C =>
    (prodN_HM_in_prodN_HK H K N M hNH hMK hNN).rightCoset
      ((prodNKHM_in_HK H K N M hNH hMK hNN).cosetRep C)
  f_mem := by
    intro C hC
    show (prodN_HM_in_prodN_HK H K N M hNH hMK hNN).rightCoset
           ((prodNKHM_in_HK H K N M hNH hMK hNN).cosetRep C) ∈
         (prodN_HM_in_prodN_HK H K N M hNH hMK hNN).cosets
    apply (prodN_HM_in_prodN_HK H K N M hNH hMK hNN).cosetOf_mem_cosets
    exact @HK_le_prodN_HK grp H K N hNH hNN _
            ((prodNKHM_in_HK H K N M hNH hMK hNN).cosetRep_mem_G hC)
  f_hom := by
    intro C₁ C₂ hC₁ hC₂
    let sub₁ := prodNKHM_in_HK H K N M hNH hMK hNN
    let sub₂ := prodN_HM_in_prodN_HK H K N M hNH hMK hNN
    have hr₁ := sub₁.cosetRep_mem_G hC₁
    have hr₂ := sub₁.cosetRep_mem_G hC₂
    have hr₁_HK : sub₁.cosetRep C₁ ∈ (H.inter K).H := hr₁
    have hr₂_HK : sub₁.cosetRep C₂ ∈ (H.inter K).H := hr₂
    have hop_HK : grp.op (sub₁.cosetRep C₁) (sub₁.cosetRep C₂) ∈ (H.inter K).H :=
      (H.inter K).op_closed hr₁_HK hr₂_HK
    have hop : sub₁.quotientOp C₁ C₂ =
        sub₁.rightCoset (grp.op (sub₁.cosetRep C₁) (sub₁.cosetRep C₂)) := rfl
    show sub₂.rightCoset (sub₁.cosetRep (sub₁.quotientOp C₁ C₂)) =
         sub₂.quotientOp (sub₂.rightCoset (sub₁.cosetRep C₁))
                         (sub₂.rightCoset (sub₁.cosetRep C₂))
    have hcoeq₁ : sub₂.rightCoset (sub₁.cosetRep C₁) = sub₂.cosetOf (sub₁.cosetRep C₁) := rfl
    have hcoeq₂ : sub₂.rightCoset (sub₁.cosetRep C₂) = sub₂.cosetOf (sub₁.cosetRep C₂) := rfl
    rw [hop, zassenhaus_fun_eq H K N M hNH hMK hNN hMM hop_HK,
        hcoeq₁, hcoeq₂,
        sub₂.quotientOp_cosetOf
          (@prodN_HM_in_prodN_HK_isNormal grp H K N M hNH hMK hNN hMM)
          (@HK_le_prodN_HK grp H K N hNH hNN _ hr₁_HK)
          (@HK_le_prodN_HK grp H K N hNH hNN _ hr₂_HK)]
    rfl

/-- El homomorfismo de Zassenhaus es inyectivo. -/
private theorem zassenhaus_hom_injective :
    (zassenhaus_hom H K N M hNH hMK hNN hMM).Injective := by
  intro C₁ C₂ hC₁ hC₂ heq
  let sub₁ := prodNKHM_in_HK H K N M hNH hMK hNN
  let sub₂ := prodN_HM_in_prodN_HK H K N M hNH hMK hNN
  have hr₁ := sub₁.cosetRep_mem_G hC₁
  have hr₂ := sub₁.cosetRep_mem_G hC₂
  have hr₁_HK : sub₁.cosetRep C₁ ∈ (H.inter K).H := hr₁
  have hr₂_HK : sub₁.cosetRep C₂ ∈ (H.inter K).H := hr₂
  have e₁ := sub₁.cosetRep_rightCoset_eq hC₁
  have e₂ := sub₁.cosetRep_rightCoset_eq hC₂
  rw [← e₁, ← e₂]
  -- heq : sub₂.rightCoset r₁ = sub₂.rightCoset r₂ ⟹ k·r₁⁻¹ ∈ sub₂ ⟹ ∈ prodNKHM
  have hcoseq_NHM : grp.op (sub₁.cosetRep C₂) (grp.inv (sub₁.cosetRep C₁)) ∈
      (prodN_HM_in_prodN_HK H K N M hNH hMK hNN).H :=
    (sub₂.cosetEq_iff_rightCoset_eq (@HK_le_prodN_HK grp H K N hNH hNN _ hr₁_HK)
      (@HK_le_prodN_HK grp H K N hNH hNN _ hr₂_HK)).mpr heq
  -- r₁, r₂ ∈ H∩K ⟹ r₂·r₁⁻¹ ∈ H∩K
  have hr₁_simp : sub₁.cosetRep C₁ ∈ H.H ∧ sub₁.cosetRep C₁ ∈ K.H := by
    have := hr₁_HK; simp only [HFSubgroup.inter, HFSet.mem_inter] at this; exact this
  have hr₂_simp : sub₁.cosetRep C₂ ∈ H.H ∧ sub₁.cosetRep C₂ ∈ K.H := by
    have := hr₂_HK; simp only [HFSubgroup.inter, HFSet.mem_inter] at this; exact this
  have hr₂_r₁_HK : grp.op (sub₁.cosetRep C₂) (grp.inv (sub₁.cosetRep C₁)) ∈
      (H.inter K).H := by
    simp only [HFSubgroup.inter, HFSet.mem_inter]
    exact ⟨H.op_closed hr₂_simp.1 (H.inv_closed hr₁_simp.1),
           K.op_closed hr₂_simp.2 (K.inv_closed hr₁_simp.2)⟩
  -- r₂·r₁⁻¹ ∈ H∩K ∩ N(H∩M) ⟹ ∈ prodNKHM
  have hrel_NKHM : grp.op (sub₁.cosetRep C₂) (grp.inv (sub₁.cosetRep C₁)) ∈
      (prodNKHM H K N M hNH hMK hNN).H :=
    HK_inter_prodN_HM_le_prodNKHM H K N M hNH hMK hNN
      hr₂_r₁_HK hcoseq_NHM
  apply (sub₁.cosetEq_iff_rightCoset_eq hr₁_HK hr₂_HK).mp
  exact hrel_NKHM

/-- El homomorfismo de Zassenhaus es sobreyectivo. -/
private theorem zassenhaus_hom_surjective :
    (zassenhaus_hom H K N M hNH hMK hNN hMM).Surjective := by
  intro D hD
  let sub₁ := prodNKHM_in_HK H K N M hNH hMK hNN
  let sub₂ := prodN_HM_in_prodN_HK H K N M hNH hMK hNN
  -- D = sub₂.rightCoset x para x ∈ prodN_HK
  obtain ⟨x, hx_NHK, hx_eq⟩ := sub₂.exists_rep_of_mem_cosets hD
  -- x ∈ prodN_HK: descomponer x = n·k, n ∈ N, k ∈ H∩K
  have hx_NHK' : x ∈ (prodSubgroup grp N (H.inter K) H hNH
      (fun ha => by change _ ∈ HFSet.inter H.H K.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
      hNN).H := hx_NHK
  obtain ⟨_, n, hn_N, k, hk_HK, heq_x⟩ :=
    (mem_prodSubgroup_iff grp N (H.inter K) H hNH
      (fun ha => by change _ ∈ HFSet.inter H.H K.H at ha; rw [HFSet.mem_inter] at ha; exact ha.1)
      hNN).mp hx_NHK'
  -- Preimagen: sub₁.rightCoset k
  refine ⟨sub₁.rightCoset k, sub₁.cosetOf_mem_cosets hk_HK, ?_⟩
  -- zassenhaus_hom.f(rightCoset k) = sub₂.rightCoset k
  show sub₂.rightCoset (sub₁.cosetRep (sub₁.rightCoset k)) = D
  rw [zassenhaus_fun_eq H K N M hNH hMK hNN hMM hk_HK]
  rw [hx_eq]
  -- sub₂.rightCoset k = sub₂.rightCoset x, vía cosetEq
  apply (sub₂.cosetEq_iff_rightCoset_eq (@HK_le_prodN_HK grp H K N hNH hNN _ hk_HK)
           hx_NHK).mp
  -- cosetEq k x := op x (inv k) ∈ sub₂.H. Como x = n·k, op x (inv k) = n ∈ N ⊆ sub₂.
  show grp.op x (grp.inv k) ∈ (prodN_HM_in_prodN_HK H K N M hNH hMK hNN).H
  have hk_H : k ∈ H.H := by simp only [HFSubgroup.inter, HFSet.mem_inter] at hk_HK; exact hk_HK.1
  have hk_G := H.H_sub hk_H
  have hn_G := N.H_sub hn_N
  have h_eq : grp.op x (grp.inv k) = n := by
    rw [← heq_x, grp.op_assoc hn_G hk_G (grp.inv_closed hk_G),
        grp.op_inv_right hk_G, grp.op_id_right hn_G]
  rw [h_eq]
  show n ∈ (prodN_HM H N M hNH hNN).H
  exact N_le_prodSubgroup grp N (H.inter M) H hNH
    (fun ha => by simp only [HFSubgroup.inter, HFSet.mem_inter] at ha; exact ha.1) hNN hn_N

-- ─────────────────────────────────────────────────────────────────
-- §8. Teorema principal
-- ─────────────────────────────────────────────────────────────────

/-- **Lema de la Mariposa de Zassenhaus**:
    El homomorfismo `(H∩K)/[(N∩K)(H∩M)] → N(H∩K)/N(H∩M)` es biyectivo. -/
theorem zassenhaus_bijection :
    (zassenhaus_hom H K N M hNH hMK hNN hMM).Bijective :=
  ⟨zassenhaus_hom_injective H K N M hNH hMK hNN hMM,
   zassenhaus_hom_surjective H K N M hNH hMK hNN hMM⟩

end Zassenhaus

end HFAlgebra
