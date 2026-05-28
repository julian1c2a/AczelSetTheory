/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Sylow.lean
-- Definiciones para los Teoremas de Sylow:
--   p-subgrupo, exponente de Sylow, p-subgrupo de Sylow.
--
-- Paridad con Peano/Combinatorics/GroupTheory/Sylow/Sylow.lean (§1).
--
-- Público:
--   HFAlgebra.pow_dvd_card           : ∃ m, p^k · m = card X
--   HFAlgebra.isPSubgroup            : ∃ k, card sub.H = p^k
--   HFAlgebra.isSylowExponent        : p^n ∣ card G  ∧  p^(n+1) ∤ card G
--   HFAlgebra.isSylowSubgroup        : ∃ n, isSylowExponent grp p n ∧ card sub.H = p^n
--   HFSubgroup.trivial               : subgrupo trivial {e}
--   HFSubgroup.trivial_card          : card trivial.H = 1
--   HFAlgebra.pow_dvd_card_of_le     : a ≤ b → p^b ∣ |G| → p^a ∣ |G|
--   HFAlgebra.sylow_card_eq          : todos los Sylow-p tienen el mismo cardinal
--   HFAlgebra.sylow_first_zero       : sylow_first caso n = 0 (subgrupo trivial)
--   HFAlgebra.gpow                   : g^n iterado
--   HFAlgebra.gpow_zero/succ/one/mem/add : reglas básicas de gpow
--
-- TODO (M6.4.B-F):
--   • gpow sobre HFGroup, order, cyclicSubgroup
--   • McKay: argumento combinatorio para Cauchy
--   • cauchy_minimal: ∃ subgrupo de orden p
--   • sylow_lift_from_cauchy: lift inductivo p^n → p^(n+1)
--   • sylow_first (caso inductivo)
--
-- Correspondencia con Peano:
--   Peano isPSubgroup G H p     ↔ HFAlgebra.isPSubgroup sub p
--   Peano isSylowExponent G p n ↔ HFAlgebra.isSylowExponent grp p n
--   Peano isSylowSubgroup G H p ↔ HFAlgebra.isSylowSubgroup sub p
--   Peano sylow_card_eq         ↔ HFAlgebra.sylow_card_eq

import AczelSetTheory.Algebra.Subgroup
import AczelSetTheory.Axioms.OrdinalNat
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.Arith
import Peano.Prelim.Classical

namespace HFAlgebra

open Peano Peano.Arith

/-- `p^k` divide la cardinalidad de `X`. -/
def pow_dvd_card (p k : ℕ₀) (X : HFSet) : Prop :=
  ∃ m : ℕ₀, mul (p ^ k) m = HFSet.card X

/-- Un `p`-subgrupo de `grp` es un subgrupo cuyo orden es una potencia de `p`. -/
def isPSubgroup {grp : HFGroup} (sub : HFSubgroup grp) (p : ℕ₀) : Prop :=
  ∃ k : ℕ₀, HFSet.card sub.H = p ^ k

/-- `p^n` es la mayor potencia de `p` que divide `card grp.G`. -/
def isSylowExponent (grp : HFGroup) (p n : ℕ₀) : Prop :=
  pow_dvd_card p n grp.G ∧ ¬ pow_dvd_card p (σ n) grp.G

/-- Un `p`-subgrupo de Sylow de `grp` es un `p`-subgrupo de orden `p^n` donde
    `p^n` es la mayor potencia de `p` que divide `card grp.G`. -/
def isSylowSubgroup {grp : HFGroup} (sub : HFSubgroup grp) (p : ℕ₀) : Prop :=
  ∃ n : ℕ₀, isSylowExponent grp p n ∧ HFSet.card sub.H = p ^ n

/-- Todo `p`-subgrupo de Sylow es, en particular, un `p`-subgrupo. -/
theorem isPSubgroup_of_isSylowSubgroup {grp : HFGroup} {sub : HFSubgroup grp}
    {p : ℕ₀} (h : isSylowSubgroup sub p) : isPSubgroup sub p := by
  obtain ⟨n, _, hcard⟩ := h
  exact ⟨n, hcard⟩

-- ─────────────────────────────────────────────────────────────────
-- §1. Subgrupo trivial {e} y caso base n = 0
-- ─────────────────────────────────────────────────────────────────

namespace HFSubgroup

variable {grp : HFGroup}

/-- Subgrupo trivial: `{e}`. -/
def trivial (grp : HFGroup) : HFSubgroup grp where
  H          := HFSet.singleton grp.e
  H_sub      := fun hx => by
    rw [HFSet.mem_singleton] at hx; rw [hx]; exact grp.e_mem
  e_mem      := (HFSet.mem_singleton grp.e grp.e).mpr rfl
  op_closed  := fun ha hb => by
    rw [HFSet.mem_singleton] at ha hb ⊢
    rw [ha, hb]; exact grp.op_id_left grp.e_mem
  inv_closed := fun ha => by
    rw [HFSet.mem_singleton] at ha ⊢
    rw [ha]; exact grp.inv_e

/-- El subgrupo trivial tiene cardinal 1. -/
theorem trivial_card (grp : HFGroup) : HFSet.card (trivial grp).H = (𝟙 : ℕ₀) := by
  show HFSet.card (HFSet.singleton grp.e) = (𝟙 : ℕ₀)
  have heq : HFSet.singleton grp.e = HFSet.insert grp.e HFSet.empty :=
    HFSet.extensionality _ _ fun z => by
      rw [HFSet.mem_singleton, HFSet.mem_insert]
      exact ⟨fun h => Or.inl h,
             fun h => h.elim id (absurd · (HFSet.not_mem_empty z))⟩
  rw [heq, HFSet.card_insert grp.e HFSet.empty (HFSet.not_mem_empty grp.e),
      HFSet.card_empty]
  rfl

end HFSubgroup

-- ─────────────────────────────────────────────────────────────────
-- §2. Lemas auxiliares de divisibilidad por potencias
-- ─────────────────────────────────────────────────────────────────

/-- Si `a ≤ b` y `p^b ∣ |X|`, entonces `p^a ∣ |X|`. -/
theorem pow_dvd_card_of_le {p a b : ℕ₀} {X : HFSet}
    (hab : le₀ a b) (hpb : pow_dvd_card p b X) :
    pow_dvd_card p a X := by
  obtain ⟨m, hm⟩ := hpb
  obtain ⟨c, hc⟩ := (le_iff_exists_add a b).mp hab
  -- hc : b = add a c, hm : mul (p^b) m = card X
  have h3 : mul (p ^ a) (p ^ c) = p ^ b :=
    (pow_add_eq_mul_pow p a c).symm.trans (congrArg (Peano.Pow.pow p) hc.symm)
  refine ⟨mul (p ^ c) m, ?_⟩
  rw [← mul_assoc, h3]; exact hm

-- ─────────────────────────────────────────────────────────────────
-- §3. Unicidad del cardinal de un Sylow-p
-- ─────────────────────────────────────────────────────────────────

/-- Si `H` y `K` son ambos Sylow-p de `grp`, tienen el mismo cardinal.
    Prueba: el exponente `n` con `p^n | |G| ∧ ¬ p^(n+1) | |G|` es único. -/
theorem sylow_card_eq {grp : HFGroup} {p : ℕ₀}
    {sub₁ sub₂ : HFSubgroup grp}
    (h₁ : isSylowSubgroup sub₁ p) (h₂ : isSylowSubgroup sub₂ p) :
    HFSet.card sub₁.H = HFSet.card sub₂.H := by
  obtain ⟨n₁, ⟨hdvd₁, hndvd₁⟩, hcard₁⟩ := h₁
  obtain ⟨n₂, ⟨hdvd₂, hndvd₂⟩, hcard₂⟩ := h₂
  have hn_eq : n₁ = n₂ := by
    rcases trichotomy n₁ n₂ with h | h | h
    · exact absurd
        (pow_dvd_card_of_le (lt_nm_then_le_nm n₁ n₂ h) hdvd₂)
        hndvd₁
    · exact h
    · exact absurd
        (pow_dvd_card_of_le (lt_nm_then_le_nm n₂ n₁ h) hdvd₁)
        hndvd₂
  exact hcard₁.trans ((congrArg (p ^ ·) hn_eq).trans hcard₂.symm)

-- ─────────────────────────────────────────────────────────────────
-- §3.5. gpow: potencia iterada en HFGroup
-- ─────────────────────────────────────────────────────────────────

/-- Potencia iterada en `HFGroup`: `gpow grp g 𝟘 = e`,
    `gpow grp g (σ n) = (gpow grp g n) · g`. -/
def gpow (grp : HFGroup) (g : HFSet) : ℕ₀ → HFSet
  | .zero   => grp.e
  | .succ n => grp.op (gpow grp g n) g

@[simp] theorem gpow_zero (grp : HFGroup) (g : HFSet) :
    gpow grp g (𝟘 : ℕ₀) = grp.e := rfl

@[simp] theorem gpow_succ (grp : HFGroup) (g : HFSet) (n : ℕ₀) :
    gpow grp g (σ n) = grp.op (gpow grp g n) g := rfl

theorem gpow_one (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    gpow grp g (𝟙 : ℕ₀) = g := by
  show grp.op grp.e g = g
  exact grp.op_id_left hg

theorem gpow_mem (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    ∀ n : ℕ₀, gpow grp g n ∈ grp.G
  | .zero   => grp.e_mem
  | .succ n => grp.op_closed (gpow_mem grp hg n) hg

theorem gpow_add (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    ∀ m n : ℕ₀, gpow grp g (add m n) = grp.op (gpow grp g m) (gpow grp g n)
  | m, .zero => by
      show gpow grp g (add m 𝟘) = grp.op (gpow grp g m) grp.e
      rw [add_zero]
      exact (grp.op_id_right (gpow_mem grp hg m)).symm
  | m, .succ n => by
      show gpow grp g (add m (σ n)) = grp.op (gpow grp g m) (grp.op (gpow grp g n) g)
      rw [add_succ]
      show grp.op (gpow grp g (add m n)) g
          = grp.op (gpow grp g m) (grp.op (gpow grp g n) g)
      rw [gpow_add grp hg m n,
          grp.op_assoc (gpow_mem grp hg m) (gpow_mem grp hg n) hg]

-- ─────────────────────────────────────────────────────────────────
-- §4. Sylow I: caso base n = 0 (subgrupo trivial)
-- ─────────────────────────────────────────────────────────────────

/-- **Sylow I**, caso `n = 0`: existe un subgrupo de orden `p^0 = 1` (el trivial).
    Caso inductivo `n+1` queda como TODO (M6.4.B-F). -/
theorem sylow_first_zero (grp : HFGroup) (p : ℕ₀) :
    ∃ sub : HFSubgroup grp, HFSet.card sub.H = p ^ (𝟘 : ℕ₀) := by
  refine ⟨HFSubgroup.trivial grp, ?_⟩
  rw [HFSubgroup.trivial_card]
  exact (Peano.Pow.pow_zero p).symm

-- ─────────────────────────────────────────────────────────────────
-- §5. gpowImg: imagen {g^0, g^1, …, g^m} como HFSet
-- ─────────────────────────────────────────────────────────────────

/-- Imagen de `{0, 1, …, m}` bajo `gpow grp g`:
    `gpowImg grp g 𝟘     = {g^0} = {e}`,
    `gpowImg grp g (σ m) = insert (g^(σ m)) (gpowImg grp g m)`. -/
def gpowImg (grp : HFGroup) (g : HFSet) : ℕ₀ → HFSet
  | .zero   => HFSet.singleton (gpow grp g (𝟘 : ℕ₀))
  | .succ m => HFSet.insert (gpow grp g (σ m)) (gpowImg grp g m)

theorem mem_gpowImg (grp : HFGroup) (g : HFSet) :
    ∀ (m : ℕ₀) (x : HFSet),
      x ∈ gpowImg grp g m ↔ ∃ i : ℕ₀, le₀ i m ∧ x = gpow grp g i
  | .zero, x => by
      show x ∈ HFSet.singleton (gpow grp g 𝟘) ↔ _
      rw [HFSet.mem_singleton]
      refine ⟨fun hx => ⟨𝟘, le_refl 𝟘, hx⟩, ?_⟩
      rintro ⟨i, hi, hx⟩
      have hi0 : i = 𝟘 := le_zero_eq_wp hi
      rw [hx, hi0]
  | .succ m, x => by
      show x ∈ HFSet.insert (gpow grp g (σ m)) (gpowImg grp g m) ↔ _
      rw [HFSet.mem_insert]
      constructor
      · rintro (hx | hx)
        · exact ⟨σ m, le_refl (σ m), hx⟩
        · obtain ⟨i, hi, hx⟩ := (mem_gpowImg grp g m x).mp hx
          exact ⟨i, le_n_m_then_le_n_sm_wp hi, hx⟩
      · rintro ⟨i, hi, hx⟩
        rcases (le_succ_iff_le_or_eq i m).mp hi with hi' | hi'
        · exact Or.inr ((mem_gpowImg grp g m x).mpr ⟨i, hi', hx⟩)
        · exact Or.inl (hx.trans (congrArg (gpow grp g) hi'))

theorem gpowImg_subset_G (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    ∀ m : ℕ₀, gpowImg grp g m ⊆ grp.G := fun m x hx => by
  obtain ⟨i, _, hxi⟩ := (mem_gpowImg grp g m x).mp hx
  rw [hxi]
  exact gpow_mem grp hg i

theorem gpowImg_card_le_succ (grp : HFGroup) (g : HFSet) :
    ∀ m : ℕ₀, le₀ (HFSet.card (gpowImg grp g m)) (σ m)
  | .zero => by
      show le₀ (HFSet.card (HFSet.singleton (gpow grp g (𝟘 : ℕ₀)))) (σ 𝟘)
      have heq : HFSet.singleton (gpow grp g (𝟘 : ℕ₀))
                  = HFSet.insert (gpow grp g (𝟘 : ℕ₀)) HFSet.empty :=
        HFSet.extensionality _ _ fun z => by
          rw [HFSet.mem_singleton, HFSet.mem_insert]
          exact ⟨Or.inl, fun h => h.elim id (absurd · (HFSet.not_mem_empty z))⟩
      rw [heq,
          HFSet.card_insert _ _ (HFSet.not_mem_empty _),
          HFSet.card_empty]
      exact le_refl (σ 𝟘)
  | .succ m => by
      show le₀ (HFSet.card (HFSet.insert (gpow grp g (σ m)) (gpowImg grp g m))) (σ (σ m))
      by_cases hin : gpow grp g (σ m) ∈ gpowImg grp g m
      · -- insert no cambia el conjunto, así card ≤ σ m ≤ σ σ m.
        have heq : HFSet.insert (gpow grp g (σ m)) (gpowImg grp g m)
                    = gpowImg grp g m := by
          apply HFSet.extensionality; intro z
          rw [HFSet.mem_insert]
          exact ⟨fun h => h.elim (· ▸ hin) id, Or.inr⟩
        rw [heq]
        exact le_trans _ _ _ (gpowImg_card_le_succ grp g m)
                              (lt_imp_le _ _ (lt_succ_self (σ m)))
      · rw [HFSet.card_insert _ _ hin]
        exact succ_le_succ_if (gpowImg_card_le_succ grp g m)

-- ─────────────────────────────────────────────────────────────────
-- §6. Pigeonhole sobre `gpowImg` y existencia del orden
-- ─────────────────────────────────────────────────────────────────

/-- Si `card (gpowImg grp g m) < σ m`, dos índices `i, j` con `j < i ≤ m`
    colisionan: `gpow grp g i = gpow grp g j`. -/
theorem exists_collision_of_card_lt (grp : HFGroup) (g : HFSet) :
    ∀ m : ℕ₀, lt₀ (HFSet.card (gpowImg grp g m)) (σ m) →
      ∃ i j : ℕ₀, le₀ i m ∧ lt₀ j i ∧ gpow grp g i = gpow grp g j
  | .zero, h => by
      -- card = 1 = σ 𝟘, contradicción con h : lt₀ 𝟙 𝟙.
      have hcard : HFSet.card (gpowImg grp g 𝟘) = (𝟙 : ℕ₀) := by
        show HFSet.card (HFSet.singleton (gpow grp g (𝟘 : ℕ₀))) = (𝟙 : ℕ₀)
        have heq : HFSet.singleton (gpow grp g (𝟘 : ℕ₀))
                    = HFSet.insert (gpow grp g (𝟘 : ℕ₀)) HFSet.empty :=
          HFSet.extensionality _ _ fun z => by
            rw [HFSet.mem_singleton, HFSet.mem_insert]
            exact ⟨Or.inl, fun h => h.elim id (absurd · (HFSet.not_mem_empty z))⟩
        rw [heq, HFSet.card_insert _ _ (HFSet.not_mem_empty _),
            HFSet.card_empty]; rfl
      rw [hcard] at h
      exact absurd h (lt_irrefl 𝟙)
  | .succ m, h => by
      by_cases hin : gpow grp g (σ m) ∈ gpowImg grp g m
      · -- gpow(σ m) ya está en gpowImg m: ∃ j ≤ m con gpow j = gpow(σ m).
        obtain ⟨j, hj, hxj⟩ := (mem_gpowImg grp g m _).mp hin
        refine ⟨σ m, j, le_refl (σ m), ?_, hxj⟩
        -- j < σ m porque j ≤ m < σ m
        exact (le_iff_lt_succ j m).mp hj
      · -- gpow(σ m) ∉ gpowImg m: card insert = σ(card m), aplicar IH.
        have h2 : HFSet.card (gpowImg grp g (σ m))
                    = σ (HFSet.card (gpowImg grp g m)) := by
          show HFSet.card (HFSet.insert (gpow grp g (σ m)) (gpowImg grp g m))
                = σ (HFSet.card (gpowImg grp g m))
          exact HFSet.card_insert _ _ hin
        rw [h2] at h
        have h' : lt₀ (HFSet.card (gpowImg grp g m)) (σ m) :=
          (lt_iff_lt_σ_σ _ _).mpr h
        obtain ⟨i, j, hi, hji, heq⟩ := exists_collision_of_card_lt grp g m h'
        exact ⟨i, j, le_n_m_then_le_n_sm_wp hi, hji, heq⟩

/-- `gpow grp g` se cancela: si `gpow i = gpow j` con `j < i`,
    entonces `gpow (Peano.Sub.sub i j) = e`. -/
theorem gpow_sub_eq_id (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    {i j : ℕ₀} (hji : lt₀ j i) (heq : gpow grp g i = gpow grp g j) :
    gpow grp g (Peano.Sub.sub i j) = grp.e := by
  have hle : le₀ j i := lt_imp_le _ _ hji
  have hadd : add (Peano.Sub.sub i j) j = i := sub_k_add_k i j hle
  have hgj : gpow grp g j ∈ grp.G := gpow_mem grp hg j
  have hgsub : gpow grp g (Peano.Sub.sub i j) ∈ grp.G := gpow_mem grp hg (Peano.Sub.sub i j)
  have hsplit : gpow grp g i
      = grp.op (gpow grp g (Peano.Sub.sub i j)) (gpow grp g j) :=
    (congrArg (gpow grp g) hadd.symm).trans
      (gpow_add grp hg (Peano.Sub.sub i j) j)
  have hcancel : gpow grp g j
      = grp.op (gpow grp g (Peano.Sub.sub i j)) (gpow grp g j) :=
    heq ▸ hsplit
  have hLHS : gpow grp g j = grp.op grp.e (gpow grp g j) :=
    (grp.op_id_left hgj).symm
  have hboth : grp.op grp.e (gpow grp g j)
                = grp.op (gpow grp g (Peano.Sub.sub i j)) (gpow grp g j) :=
    hLHS ▸ hcancel
  exact (grp.right_cancel hgj grp.e_mem hgsub hboth).symm

/-- **Existencia del orden**: para todo `g ∈ G`, existe `n > 0` con `g^n = e`
    y `n ≤ card G`. -/
theorem orderExists (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    ∃ n : ℕ₀, lt₀ 𝟘 n ∧ gpow grp g n = grp.e ∧ le₀ n (HFSet.card grp.G) := by
  let N : ℕ₀ := HFSet.card grp.G
  have hsubG : gpowImg grp g N ⊆ grp.G := gpowImg_subset_G grp hg N
  have hcardle : le₀ (HFSet.card (gpowImg grp g N)) N :=
    HFSet.card_le_of_subset hsubG
  have hlt : lt₀ (HFSet.card (gpowImg grp g N)) (σ N) :=
    (le_iff_lt_succ _ _).mp hcardle
  obtain ⟨i, j, hiN, hji, heqij⟩ :=
    exists_collision_of_card_lt grp g N hlt
  refine ⟨Peano.Sub.sub i j, ?_, gpow_sub_eq_id grp hg hji heqij, ?_⟩
  · rcases trichotomy (Peano.Sub.sub i j) 𝟘 with h | h | h
    · exact (nlt_n_0 (Peano.Sub.sub i j) h).elim
    · have hadd : add (Peano.Sub.sub i j) j = i :=
        sub_k_add_k i j (lt_imp_le _ _ hji)
      have h0 : add 𝟘 j = i := h ▸ hadd
      have hji_eq : j = i := (zero_add j).symm.trans h0
      exact (lt_irrefl j (hji_eq ▸ hji)).elim
    · exact h
  · -- sub i j ≤ i ≤ N
    exact le_trans _ i _ (sub_le_self i j) hiN

-- ─────────────────────────────────────────────────────────────────
-- §7. Order vía WOP
-- ─────────────────────────────────────────────────────────────────

/-- Especificación del orden vía WOP. -/
private theorem order_wop (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    ExistsUnique (fun n : ℕ₀ =>
      (lt₀ 𝟘 n ∧ gpow grp g n = grp.e) ∧
      ∀ m : ℕ₀, (lt₀ 𝟘 m ∧ gpow grp g m = grp.e) → le₀ n m) :=
  Peano.WellFounded.well_ordering_principle
    (fun n => lt₀ 𝟘 n ∧ gpow grp g n = grp.e)
    (let ⟨n, hn1, hn2, _⟩ := orderExists grp hg; ⟨n, hn1, hn2⟩)

/-- El orden de `g` en `grp`: el mínimo `n > 0` con `g^n = e`. -/
noncomputable def order (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) : ℕ₀ :=
  Peano.choose_unique (order_wop grp hg)

private theorem order_spec (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    (lt₀ 𝟘 (order grp hg) ∧ gpow grp g (order grp hg) = grp.e) ∧
    ∀ m : ℕ₀, (lt₀ 𝟘 m ∧ gpow grp g m = grp.e) → le₀ (order grp hg) m :=
  Peano.choose_spec_unique (order_wop grp hg)

theorem order_pos (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    lt₀ 𝟘 (order grp hg) := (order_spec grp hg).1.1

theorem gpow_order_eq_id (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    gpow grp g (order grp hg) = grp.e := (order_spec grp hg).1.2

theorem order_minimal (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    {m : ℕ₀} (hm_pos : lt₀ 𝟘 m) (hm_eq : gpow grp g m = grp.e) :
    le₀ (order grp hg) m := (order_spec grp hg).2 m ⟨hm_pos, hm_eq⟩

theorem order_ne_zero (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    order grp hg ≠ 𝟘 :=
  (ne_of_lt 𝟘 _ (order_pos grp hg)).symm

theorem order_le_card (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    le₀ (order grp hg) (HFSet.card grp.G) := by
  obtain ⟨n, hn_pos, hn_eq, hn_le⟩ := orderExists grp hg
  exact le_trans _ n _ (order_minimal grp hg hn_pos hn_eq) hn_le

/-- `g^(k · ord) = e`. -/
theorem gpow_mul_order_eq_id (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    ∀ k : ℕ₀, gpow grp g (mul k (order grp hg)) = grp.e
  | .zero => by
      show gpow grp g (mul 𝟘 (order grp hg)) = grp.e
      rw [zero_mul]; rfl
  | .succ k => by
      show gpow grp g (mul (σ k) (order grp hg)) = grp.e
      rw [succ_mul, gpow_add grp hg, gpow_mul_order_eq_id grp hg k,
          gpow_order_eq_id grp hg, grp.op_id_left grp.e_mem]

/-- `g^n = g^(n mod ord)`. -/
theorem gpow_mod_order (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) (n : ℕ₀) :
    gpow grp g n = gpow grp g (mod n (order grp hg)) := by
  have hord_ne := order_ne_zero grp hg
  have hdec : n = add (mul (div n (order grp hg)) (order grp hg))
                       (mod n (order grp hg)) :=
    divMod_spec n (order grp hg) hord_ne
  have hkey : gpow grp g (add (mul (div n (order grp hg)) (order grp hg))
                                (mod n (order grp hg)))
              = gpow grp g (mod n (order grp hg)) := by
    rw [gpow_add grp hg, gpow_mul_order_eq_id grp hg,
        grp.op_id_left (gpow_mem grp hg _)]
  exact (congrArg (gpow grp g) hdec).trans hkey

-- ─────────────────────────────────────────────────────────────────
-- §8. Subgrupo cíclico ⟨g⟩
-- ─────────────────────────────────────────────────────────────────

/-- Inverso de `gpow g n`: si `g^n · h = e`, entonces `h = (g^n)⁻¹`. Aquí calculamos
    directamente que `(g^n)⁻¹ = g^(ord - (n mod ord))` (mod ord) — lo encapsulamos
    en `gpow_inv_eq_gpow_sub` abajo. -/
theorem gpow_op_gpow_sub_order (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    (n : ℕ₀) (hn : le₀ n (order grp hg)) :
    grp.op (gpow grp g n) (gpow grp g (Peano.Sub.sub (order grp hg) n)) = grp.e := by
  have hsum : add n (Peano.Sub.sub (order grp hg) n) = order grp hg := by
    have := sub_k_add_k (order grp hg) n hn
    rw [add_comm] at this
    exact this
  have h := gpow_add grp hg n (Peano.Sub.sub (order grp hg) n)
  rw [hsum] at h
  exact h.symm.trans (gpow_order_eq_id grp hg)

/-- Soporte del subgrupo cíclico: `{g^0, g^1, …, g^(ord)}` (con duplicidad en `g^0 = g^ord = e`). -/
noncomputable def cyclicCarrier (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) : HFSet :=
  gpowImg grp g (order grp hg)

theorem mem_cyclicCarrier (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) (x : HFSet) :
    x ∈ cyclicCarrier grp hg ↔ ∃ i : ℕ₀, le₀ i (order grp hg) ∧ x = gpow grp g i :=
  mem_gpowImg grp g (order grp hg) x

theorem cyclicCarrier_subset_G (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    cyclicCarrier grp hg ⊆ grp.G :=
  gpowImg_subset_G grp hg (order grp hg)

theorem cyclicCarrier_e_mem (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    grp.e ∈ cyclicCarrier grp hg :=
  (mem_cyclicCarrier grp hg grp.e).mpr
    ⟨𝟘, zero_le _, by show grp.e = gpow grp g 𝟘; rfl⟩

theorem cyclicCarrier_op_closed (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    {a b : HFSet} (ha : a ∈ cyclicCarrier grp hg) (hb : b ∈ cyclicCarrier grp hg) :
    grp.op a b ∈ cyclicCarrier grp hg := by
  obtain ⟨i, _hi, hai⟩ := (mem_cyclicCarrier grp hg a).mp ha
  obtain ⟨j, _hj, hbj⟩ := (mem_cyclicCarrier grp hg b).mp hb
  have hord_ne := order_ne_zero grp hg
  refine (mem_cyclicCarrier grp hg _).mpr
    ⟨mod (add i j) (order grp hg), ?_, ?_⟩
  · exact lt_imp_le _ _ (mod_lt _ (order grp hg) hord_ne)
  · -- a · b = gpow i · gpow j = gpow (i+j) = gpow ((i+j) mod ord)
    rw [hai, hbj, ← gpow_add grp hg, gpow_mod_order grp hg (add i j)]

theorem cyclicCarrier_inv_closed (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    {a : HFSet} (ha : a ∈ cyclicCarrier grp hg) :
    grp.inv a ∈ cyclicCarrier grp hg := by
  obtain ⟨i, _hi, hai⟩ := (mem_cyclicCarrier grp hg a).mp ha
  have hord_ne := order_ne_zero grp hg
  -- Sea i' = i mod ord ≤ ord-1, y j = ord - i'. Entonces gpow i' · gpow j = e,
  -- así inv (gpow i') = gpow j.
  let i' := mod i (order grp hg)
  have hi'_lt : lt₀ i' (order grp hg) := mod_lt _ _ hord_ne
  have hi'_le : le₀ i' (order grp hg) := lt_imp_le _ _ hi'_lt
  have hgpow_eq : a = gpow grp g i' := hai.trans (gpow_mod_order grp hg i)
  have hgi'_mem : gpow grp g i' ∈ grp.G := gpow_mem grp hg i'
  have hgj_mem : gpow grp g (Peano.Sub.sub (order grp hg) i') ∈ grp.G :=
    gpow_mem grp hg _
  have hrel := gpow_op_gpow_sub_order grp hg i' hi'_le
  -- inv (gpow i') = gpow (ord - i')  (de la relación · = e por unicidad del inverso)
  have hinv_eq : grp.inv (gpow grp g i') = gpow grp g (Peano.Sub.sub (order grp hg) i') := by
    have h1 : grp.op (gpow grp g i') (grp.inv (gpow grp g i')) = grp.e :=
      grp.op_inv_right hgi'_mem
    have h2 : grp.op (gpow grp g i') (gpow grp g (Peano.Sub.sub (order grp hg) i')) = grp.e := hrel
    exact grp.left_cancel hgi'_mem (grp.inv_closed hgi'_mem) hgj_mem
            (h1.trans h2.symm)
  refine (mem_cyclicCarrier grp hg _).mpr
    ⟨Peano.Sub.sub (order grp hg) i', ?_, ?_⟩
  · exact sub_le_self _ _
  · rw [hgpow_eq, hinv_eq]

/-- Subgrupo cíclico `⟨g⟩` generado por un elemento `g`. -/
noncomputable def cyclicSubgroup (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    HFSubgroup grp where
  H          := cyclicCarrier grp hg
  H_sub      := fun hx => cyclicCarrier_subset_G grp hg _ hx
  e_mem      := cyclicCarrier_e_mem grp hg
  op_closed  := cyclicCarrier_op_closed grp hg
  inv_closed := cyclicCarrier_inv_closed grp hg

end HFAlgebra
