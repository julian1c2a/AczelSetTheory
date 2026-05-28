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
import AczelSetTheory.Axioms.Function
import AczelSetTheory.Axioms.CartProd
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.CardImage
import AczelSetTheory.Operations.NPow
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

-- ─────────────────────────────────────────────────────────────────
-- §9. McKay carrier: p-tuplas con producto = e
-- ─────────────────────────────────────────────────────────────────

/-- Producto secuencial de las componentes de una `p`-tupla `t ∈ nPow grp.G p`,
    definido por recursión sobre la longitud y proyecciones `fst`/`snd`.
    Para `p = σ n`: `tupleProd (σ n) ⟪s, a⟫ = (tupleProd n s) · a`. -/
def tupleProd (grp : HFGroup) : ℕ₀ → HFSet → HFSet
  | .zero,   _ => grp.e
  | .succ n, t => grp.op (tupleProd grp n (HFSet.fst t)) (HFSet.snd t)

@[simp] theorem tupleProd_zero (grp : HFGroup) (t : HFSet) :
    tupleProd grp 𝟘 t = grp.e := rfl

@[simp] theorem tupleProd_succ (grp : HFGroup) (n : ℕ₀) (t : HFSet) :
    tupleProd grp (σ n) t
      = grp.op (tupleProd grp n (HFSet.fst t)) (HFSet.snd t) := rfl

/-- Sobre un par `⟪s, a⟫` el producto se reduce limpiamente. -/
theorem tupleProd_pair (grp : HFGroup) (n : ℕ₀) (s a : HFSet) :
    tupleProd grp (σ n) ⟪s, a⟫ = grp.op (tupleProd grp n s) a := by
  show grp.op (tupleProd grp n (HFSet.fst ⟪s, a⟫)) (HFSet.snd ⟪s, a⟫)
        = grp.op (tupleProd grp n s) a
  rw [HFSet.fst_orderedPair_eq', HFSet.snd_orderedPair_eq']

/-- Primera proyección de un elemento de `nPow A (σ n)` cae en `nPow A n`. -/
theorem fst_mem_nPow (A : HFSet) (n : ℕ₀) {t : HFSet}
    (ht : t ∈ HFSet.nPow A (σ n)) : HFSet.fst t ∈ HFSet.nPow A n := by
  rw [HFSet.nPow_succ] at ht
  obtain ⟨a, b, ha, _hb, heq⟩ := (HFSet.mem_cartProd t (HFSet.nPow A n) A).mp ht
  rw [heq, HFSet.fst_orderedPair_eq']
  exact ha

/-- Segunda proyección de un elemento de `nPow A (σ n)` cae en `A`. -/
theorem snd_mem_of_mem_nPow (A : HFSet) (n : ℕ₀) {t : HFSet}
    (ht : t ∈ HFSet.nPow A (σ n)) : HFSet.snd t ∈ A := by
  rw [HFSet.nPow_succ] at ht
  obtain ⟨a, b, _ha, hb, heq⟩ := (HFSet.mem_cartProd t (HFSet.nPow A n) A).mp ht
  rw [heq, HFSet.snd_orderedPair_eq']
  exact hb

/-- El producto de las componentes de una `p`-tupla de `G` vive en `G`. -/
theorem tupleProd_mem (grp : HFGroup) :
    ∀ (n : ℕ₀) {t : HFSet}, t ∈ HFSet.nPow grp.G n →
      tupleProd grp n t ∈ grp.G
  | .zero,   _, _  => grp.e_mem
  | .succ n, _, ht =>
      grp.op_closed
        (tupleProd_mem grp n (fst_mem_nPow grp.G n ht))
        (snd_mem_of_mem_nPow grp.G n ht)

/-- Tupla constante `(e, e, …, e)` de longitud `n`. -/
def eTuple (grp : HFGroup) : ℕ₀ → HFSet
  | .zero   => HFSet.empty
  | .succ n => ⟪eTuple grp n, grp.e⟫

theorem eTuple_mem_nPow (grp : HFGroup) :
    ∀ n : ℕ₀, eTuple grp n ∈ HFSet.nPow grp.G n
  | .zero   => by
      show HFSet.empty ∈ HFSet.singleton HFSet.empty
      exact (HFSet.mem_singleton _ _).mpr rfl
  | .succ n => by
      show ⟪eTuple grp n, grp.e⟫ ∈ HFSet.nPow grp.G n ×ₕ grp.G
      exact (HFSet.mem_cartProd _ _ _).mpr
        ⟨eTuple grp n, grp.e, eTuple_mem_nPow grp n, grp.e_mem, rfl⟩

theorem tupleProd_eTuple (grp : HFGroup) :
    ∀ n : ℕ₀, tupleProd grp n (eTuple grp n) = grp.e
  | .zero   => rfl
  | .succ n => by
      show tupleProd grp (σ n) ⟪eTuple grp n, grp.e⟫ = grp.e
      rw [tupleProd_pair, tupleProd_eTuple grp n, grp.op_id_left grp.e_mem]

/-- Decidibilidad del predicado McKay (necesaria para `sep`). -/
instance instDecidableTupleProdEq (grp : HFGroup) (p : ℕ₀) :
    DecidablePred (fun t : HFSet => tupleProd grp p t = grp.e) :=
  fun _ => inferInstance

/-- **Carrier de McKay**: `{t ∈ nPow G p | producto t = e}`. -/
def mckayCarrier (grp : HFGroup) (p : ℕ₀) : HFSet :=
  HFSet.sep (HFSet.nPow grp.G p) (fun t => tupleProd grp p t = grp.e)

theorem mem_mckayCarrier (grp : HFGroup) (p : ℕ₀) (t : HFSet) :
    t ∈ mckayCarrier grp p
      ↔ t ∈ HFSet.nPow grp.G p ∧ tupleProd grp p t = grp.e :=
  HFSet.mem_sep _ _ _

theorem mckayCarrier_subset_nPow (grp : HFGroup) (p : ℕ₀) :
    mckayCarrier grp p ⊆ HFSet.nPow grp.G p := fun _ hx =>
  ((mem_mckayCarrier grp p _).mp hx).1

/-- La tupla constante `(e, …, e)` pertenece al carrier de McKay. -/
theorem eTuple_mem_mckayCarrier (grp : HFGroup) (p : ℕ₀) :
    eTuple grp p ∈ mckayCarrier grp p :=
  (mem_mckayCarrier grp p _).mpr ⟨eTuple_mem_nPow grp p, tupleProd_eTuple grp p⟩

-- ==================================================================
-- §10. McKay shift (D.2)
-- ==================================================================

/-- Lema auxiliar: en un grupo, `a·b = e → b·a = e`. -/
theorem swap_op_eq_e (grp : HFGroup) {a b : HFSet}
    (ha : a ∈ grp.G) (hb : b ∈ grp.G) (h : grp.op a b = grp.e) :
    grp.op b a = grp.e := by
  have : a = grp.inv b := grp.unique_inv hb ha h
  rw [this, grp.op_inv_right hb]

/-- Cabeza (primera componente) de una `(σ n)`-tupla. -/
def getHead : ℕ₀ → HFSet → HFSet
  | .zero,   t => HFSet.snd t
  | .succ n, t => getHead n (HFSet.fst t)

/-- Cola (componentes 2..σn) de una `(σ n)`-tupla, como una `n`-tupla. -/
def dropHead : ℕ₀ → HFSet → HFSet
  | .zero,   _ => HFSet.empty
  | .succ n, t => ⟪dropHead n (HFSet.fst t), HFSet.snd t⟫

theorem getHead_mem (G : HFSet) :
    ∀ (n : ℕ₀) {t : HFSet}, t ∈ HFSet.nPow G (σ n) → getHead n t ∈ G
  | .zero,   t, ht   => snd_mem_of_mem_nPow G 𝟘 ht
  | .succ n, t, ht   => by
      show getHead n (HFSet.fst t) ∈ G
      exact getHead_mem G n (fst_mem_nPow G (σ n) ht)

theorem dropHead_mem (G : HFSet) :
    ∀ (n : ℕ₀) {t : HFSet}, t ∈ HFSet.nPow G (σ n) → dropHead n t ∈ HFSet.nPow G n
  | .zero,   _, _    => by
      show HFSet.empty ∈ HFSet.singleton HFSet.empty
      exact (HFSet.mem_singleton _ _).mpr rfl
  | .succ n, t, ht   => by
      show ⟪dropHead n (HFSet.fst t), HFSet.snd t⟫ ∈ HFSet.nPow G n ×ₕ G
      exact (HFSet.mem_cartProd _ _ _).mpr
        ⟨dropHead n (HFSet.fst t), HFSet.snd t,
         dropHead_mem G n (fst_mem_nPow G (σ n) ht),
         snd_mem_of_mem_nPow G (σ n) ht,
         rfl⟩

/-- Descomposición del producto: `tupleProd (σ n) t = (getHead n t) · (tupleProd n (dropHead n t))`. -/
theorem tupleProd_split (grp : HFGroup) :
    ∀ (n : ℕ₀) {t : HFSet}, t ∈ HFSet.nPow grp.G (σ n) →
      tupleProd grp (σ n) t
        = grp.op (getHead n t) (tupleProd grp n (dropHead n t))
  | .zero,   t, ht => by
      show grp.op (tupleProd grp 𝟘 (HFSet.fst t)) (HFSet.snd t)
            = grp.op (HFSet.snd t) (tupleProd grp 𝟘 HFSet.empty)
      have hsnd : HFSet.snd t ∈ grp.G := snd_mem_of_mem_nPow grp.G 𝟘 ht
      rw [show tupleProd grp 𝟘 (HFSet.fst t) = grp.e from rfl,
          show tupleProd grp 𝟘 HFSet.empty = grp.e from rfl,
          grp.op_id_left hsnd, grp.op_id_right hsnd]
  | .succ n, t, ht => by
      -- t : nPow G (σ (σ n)) = nPow G (σ n) ×ₕ G
      -- LHS = (tupleProd (σ n) (fst t)) · (snd t)
      -- IH on fst t : tupleProd (σ n) (fst t) = (getHead n (fst t)) · (tupleProd n (dropHead n (fst t)))
      -- RHS = getHead (σ n) t · tupleProd (σ n) (dropHead (σ n) t)
      --     = getHead n (fst t) · ((tupleProd n (dropHead n (fst t))) · (snd t))
      have hfst : HFSet.fst t ∈ HFSet.nPow grp.G (σ n) := fst_mem_nPow grp.G (σ n) ht
      have hsnd : HFSet.snd t ∈ grp.G := snd_mem_of_mem_nPow grp.G (σ n) ht
      have hhead : getHead n (HFSet.fst t) ∈ grp.G := getHead_mem grp.G n hfst
      have hdrop : dropHead n (HFSet.fst t) ∈ HFSet.nPow grp.G n :=
        dropHead_mem grp.G n hfst
      have htail : tupleProd grp n (dropHead n (HFSet.fst t)) ∈ grp.G :=
        tupleProd_mem grp n hdrop
      have ih := tupleProd_split grp n hfst
      show grp.op (tupleProd grp (σ n) (HFSet.fst t)) (HFSet.snd t)
            = grp.op (getHead n (HFSet.fst t))
                     (tupleProd grp (σ n) ⟪dropHead n (HFSet.fst t), HFSet.snd t⟫)
      rw [tupleProd_pair, ih, grp.op_assoc hhead htail hsnd]

/-- **McKay shift**: rota cíclicamente las componentes de una `p`-tupla. -/
def mckayShift (_grp : HFGroup) : ℕ₀ → HFSet → HFSet
  | .zero,   t => t
  | .succ n, t => ⟪dropHead n t, getHead n t⟫

theorem mckayShift_mem_nPow (grp : HFGroup) :
    ∀ (p : ℕ₀) {t : HFSet}, t ∈ HFSet.nPow grp.G p →
      mckayShift grp p t ∈ HFSet.nPow grp.G p
  | .zero,   _, ht => ht
  | .succ n, t, ht => by
      show ⟪dropHead n t, getHead n t⟫ ∈ HFSet.nPow grp.G n ×ₕ grp.G
      exact (HFSet.mem_cartProd _ _ _).mpr
        ⟨dropHead n t, getHead n t,
         dropHead_mem grp.G n ht, getHead_mem grp.G n ht, rfl⟩

/-- El shift de McKay preserva el predicado "producto = e". -/
theorem mckayShift_prod_e (grp : HFGroup) :
    ∀ (p : ℕ₀) {t : HFSet}, t ∈ HFSet.nPow grp.G p →
      tupleProd grp p t = grp.e →
      tupleProd grp p (mckayShift grp p t) = grp.e
  | .zero,   _, _,  hprod => hprod
  | .succ n, t, ht, hprod => by
      -- mckayShift (σ n) t = ⟪dropHead n t, getHead n t⟫
      -- tupleProd (σ n) ⟪dropHead n t, getHead n t⟫
      --   = (tupleProd n (dropHead n t)) · (getHead n t)
      -- Por tupleProd_split: tupleProd (σ n) t = (getHead n t) · (tupleProd n (dropHead n t)) = e
      -- Por swap: (tupleProd n (dropHead n t)) · (getHead n t) = e.
      have hhead : getHead n t ∈ grp.G := getHead_mem grp.G n ht
      have hdrop : dropHead n t ∈ HFSet.nPow grp.G n := dropHead_mem grp.G n ht
      have htail : tupleProd grp n (dropHead n t) ∈ grp.G := tupleProd_mem grp n hdrop
      have hsplit : grp.op (getHead n t) (tupleProd grp n (dropHead n t)) = grp.e := by
        rw [← tupleProd_split grp n ht]; exact hprod
      have hswap : grp.op (tupleProd grp n (dropHead n t)) (getHead n t) = grp.e :=
        swap_op_eq_e grp hhead htail hsplit
      show tupleProd grp (σ n) ⟪dropHead n t, getHead n t⟫ = grp.e
      rw [tupleProd_pair]
      exact hswap

/-- El shift de McKay preserva el carrier de McKay. -/
theorem mckayShift_mem_mckayCarrier (grp : HFGroup) (p : ℕ₀) {t : HFSet}
    (ht : t ∈ mckayCarrier grp p) :
    mckayShift grp p t ∈ mckayCarrier grp p := by
  obtain ⟨htN, hprod⟩ := (mem_mckayCarrier grp p t).mp ht
  exact (mem_mckayCarrier grp p _).mpr
    ⟨mckayShift_mem_nPow grp p htN, mckayShift_prod_e grp p htN hprod⟩

-- ==================================================================
-- §11. Cardinalidad del carrier de McKay (D.3)
-- ==================================================================

/-- "Levanta" un `n`-tupla a un `(σ n)`-tupla en el carrier de McKay,
    añadiendo como última componente el inverso del producto. -/
def mckayLift (grp : HFGroup) (n : ℕ₀) (s : HFSet) : HFSet :=
  ⟪s, grp.inv (tupleProd grp n s)⟫

theorem mckayLift_mem (grp : HFGroup) (n : ℕ₀) {s : HFSet}
    (hs : s ∈ HFSet.nPow grp.G n) :
    mckayLift grp n s ∈ mckayCarrier grp (σ n) := by
  have hprod : tupleProd grp n s ∈ grp.G := tupleProd_mem grp n hs
  have hinv : grp.inv (tupleProd grp n s) ∈ grp.G := grp.inv_closed hprod
  refine (mem_mckayCarrier grp (σ n) _).mpr ⟨?_, ?_⟩
  · -- Pertenencia a nPow G (σ n)
    show ⟪s, grp.inv (tupleProd grp n s)⟫ ∈ HFSet.nPow grp.G n ×ₕ grp.G
    exact (HFSet.mem_cartProd _ _ _).mpr ⟨s, _, hs, hinv, rfl⟩
  · -- Producto = e
    show tupleProd grp (σ n) ⟪s, grp.inv (tupleProd grp n s)⟫ = grp.e
    rw [tupleProd_pair]; exact grp.op_inv_right hprod

theorem mckayLift_injective (grp : HFGroup) (n : ℕ₀) :
    ∀ s₁ s₂, s₁ ∈ HFSet.nPow grp.G n → s₂ ∈ HFSet.nPow grp.G n →
      mckayLift grp n s₁ = mckayLift grp n s₂ → s₁ = s₂ := by
  intro s₁ s₂ _ _ h
  have h' : (⟪s₁, grp.inv (tupleProd grp n s₁)⟫ : HFSet)
              = ⟪s₂, grp.inv (tupleProd grp n s₂)⟫ := h
  have hfst := congrArg HFSet.fst h'
  rwa [HFSet.fst_orderedPair_eq', HFSet.fst_orderedPair_eq'] at hfst

theorem mckayLift_surjective (grp : HFGroup) (n : ℕ₀) :
    ∀ t, t ∈ mckayCarrier grp (σ n) →
      ∃ s ∈ HFSet.nPow grp.G n, t = mckayLift grp n s := by
  intro t ht
  obtain ⟨htN, hprod⟩ := (mem_mckayCarrier grp (σ n) t).mp ht
  rw [HFSet.nPow_succ] at htN
  obtain ⟨s, last, hs, hlast, heq⟩ := (HFSet.mem_cartProd _ _ _).mp htN
  refine ⟨s, hs, ?_⟩
  have hprod' : tupleProd grp (σ n) ⟪s, last⟫ = grp.e := heq ▸ hprod
  rw [tupleProd_pair] at hprod'
  have hprodG : tupleProd grp n s ∈ grp.G := tupleProd_mem grp n hs
  -- (prod s) · last = e, swap to last · (prod s) = e, then unique_inv
  have hswap : grp.op last (tupleProd grp n s) = grp.e :=
    swap_op_eq_e grp hprodG hlast hprod'
  have hlast_eq : last = grp.inv (tupleProd grp n s) :=
    grp.unique_inv hprodG hlast hswap
  show t = ⟪s, grp.inv (tupleProd grp n s)⟫
  rw [heq, hlast_eq]

/-- Cardinalidad del carrier de McKay: `|X_{σ n}| = |G|^n`. -/
theorem card_mckayCarrier_succ (grp : HFGroup) (n : ℕ₀) :
    HFSet.card (mckayCarrier grp (σ n)) = (HFSet.card grp.G) ^ n := by
  have hbij : HFSet.card (HFSet.nPow grp.G n) = HFSet.card (mckayCarrier grp (σ n)) :=
    HFSet.card_eq_of_classBij
      (fun s hs => mckayLift_mem grp n hs)
      (mckayLift_injective grp n)
      (fun y hy => mckayLift_surjective grp n y hy)
  rw [← hbij, HFSet.card_nPow]

/-- Si `p ∣ |G|` y `n ≠ 0`, entonces `p ∣ |G|^n`. -/
theorem dvd_card_pow_of_dvd_card (grp : HFGroup) (p : ℕ₀)
    (hp : p ∣ HFSet.card grp.G) {n : ℕ₀} (hn : n ≠ 𝟘) :
    p ∣ (HFSet.card grp.G) ^ n := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m =>
      show p ∣ Peano.Mul.mul ((HFSet.card grp.G) ^ m) (HFSet.card grp.G)
      exact Peano.Arith.divides_mul_left hp

/-- **D.3**: Si `p ∣ |G|`, entonces `p ∣ |mckayCarrier (σ n)|` para todo `n ≠ 0`. -/
theorem dvd_card_mckayCarrier_succ (grp : HFGroup) (p : ℕ₀)
    (hp : p ∣ HFSet.card grp.G) {n : ℕ₀} (hn : n ≠ 𝟘) :
    p ∣ HFSet.card (mckayCarrier grp (σ n)) := by
  rw [card_mckayCarrier_succ]
  exact dvd_card_pow_of_dvd_card grp p hp hn

-- ==================================================================
-- §12. Iteración de McKay shift y puntos fijos (D.4.A)
-- ==================================================================

/-- Iteración `k`-ésima del shift de McKay. -/
def shiftIter (grp : HFGroup) (p : ℕ₀) : ℕ₀ → HFSet → HFSet
  | .zero,   t => t
  | .succ k, t => mckayShift grp p (shiftIter grp p k t)

@[simp] theorem shiftIter_zero (grp : HFGroup) (p : ℕ₀) (t : HFSet) :
    shiftIter grp p 𝟘 t = t := rfl

@[simp] theorem shiftIter_succ (grp : HFGroup) (p k : ℕ₀) (t : HFSet) :
    shiftIter grp p (σ k) t = mckayShift grp p (shiftIter grp p k t) := rfl

/-- La iteración preserva la pertenencia a `nPow G p`. -/
theorem shiftIter_mem_nPow (grp : HFGroup) (p : ℕ₀) :
    ∀ (k : ℕ₀) {t : HFSet}, t ∈ HFSet.nPow grp.G p →
      shiftIter grp p k t ∈ HFSet.nPow grp.G p
  | .zero,   _, ht => ht
  | .succ k, _, ht =>
      mckayShift_mem_nPow grp p (shiftIter_mem_nPow grp p k ht)

/-- La iteración preserva el carrier de McKay. -/
theorem shiftIter_mem_mckayCarrier (grp : HFGroup) (p : ℕ₀) :
    ∀ (k : ℕ₀) {t : HFSet}, t ∈ mckayCarrier grp p →
      shiftIter grp p k t ∈ mckayCarrier grp p
  | .zero,   _, ht => ht
  | .succ k, _, ht =>
      mckayShift_mem_mckayCarrier grp p (shiftIter_mem_mckayCarrier grp p k ht)

/-- Conjunto de puntos fijos del shift de McKay en el carrier. -/
def mckayFixedPoints (grp : HFGroup) (p : ℕ₀) : HFSet :=
  HFSet.sep (mckayCarrier grp p) (fun t => mckayShift grp p t = t)

theorem mem_mckayFixedPoints (grp : HFGroup) (p : ℕ₀) (t : HFSet) :
    t ∈ mckayFixedPoints grp p
      ↔ t ∈ mckayCarrier grp p ∧ mckayShift grp p t = t :=
  HFSet.mem_sep _ _ _

theorem mckayFixedPoints_subset (grp : HFGroup) (p : ℕ₀) :
    mckayFixedPoints grp p ⊆ mckayCarrier grp p :=
  fun _ hx => ((mem_mckayFixedPoints grp p _).mp hx).1

/-- Lema técnico: `getHead n (eTuple (σ n)) = e`. -/
theorem eTuple_getHead (grp : HFGroup) :
    ∀ n : ℕ₀, getHead n (eTuple grp (σ n)) = grp.e
  | .zero   => by
      show HFSet.snd (eTuple grp (σ 𝟘)) = grp.e
      show HFSet.snd ⟪eTuple grp 𝟘, grp.e⟫ = grp.e
      rw [HFSet.snd_orderedPair_eq']
  | .succ n => by
      show getHead n (HFSet.fst (eTuple grp (σ (σ n)))) = grp.e
      show getHead n (HFSet.fst ⟪eTuple grp (σ n), grp.e⟫) = grp.e
      rw [HFSet.fst_orderedPair_eq']
      exact eTuple_getHead grp n

/-- Lema técnico: `dropHead n (eTuple (σ n)) = eTuple n`. -/
theorem eTuple_dropHead (grp : HFGroup) :
    ∀ n : ℕ₀, dropHead n (eTuple grp (σ n)) = eTuple grp n
  | .zero   => rfl
  | .succ n => by
      show ⟪dropHead n (HFSet.fst (eTuple grp (σ (σ n)))),
            HFSet.snd (eTuple grp (σ (σ n)))⟫ = eTuple grp (σ n)
      show ⟪dropHead n (HFSet.fst ⟪eTuple grp (σ n), grp.e⟫),
            HFSet.snd ⟪eTuple grp (σ n), grp.e⟫⟫ = ⟪eTuple grp n, grp.e⟫
      rw [HFSet.fst_orderedPair_eq', HFSet.snd_orderedPair_eq',
          eTuple_dropHead grp n]

/-- La tupla constante `(e, …, e)` es fija bajo el shift. -/
theorem mckayShift_eTuple (grp : HFGroup) :
    ∀ p : ℕ₀, mckayShift grp p (eTuple grp p) = eTuple grp p
  | .zero   => rfl
  | .succ n => by
      show ⟪dropHead n (eTuple grp (σ n)), getHead n (eTuple grp (σ n))⟫
            = eTuple grp (σ n)
      rw [eTuple_getHead grp n, eTuple_dropHead grp n]
      rfl

/-- La tupla constante está en el conjunto de puntos fijos. -/
theorem eTuple_mem_mckayFixedPoints (grp : HFGroup) (p : ℕ₀) :
    eTuple grp p ∈ mckayFixedPoints grp p :=
  (mem_mckayFixedPoints grp p _).mpr
    ⟨eTuple_mem_mckayCarrier grp p, mckayShift_eTuple grp p⟩

-- ==================================================================
-- §13. shiftIter es homomorfismo de monoides (D.4.B parte 1)
-- ==================================================================

/-- `shiftIter` respeta la suma: `shiftIter (i+j) t = shiftIter i (shiftIter j t)`. -/
theorem shiftIter_add (grp : HFGroup) (p : ℕ₀) :
    ∀ (i j : ℕ₀) (t : HFSet),
      shiftIter grp p (Peano.Add.add i j) t
        = shiftIter grp p i (shiftIter grp p j t)
  | .zero,   j, t => by
      show shiftIter grp p (Peano.Add.add 𝟘 j) t = shiftIter grp p j t
      rw [Peano.Add.zero_add]
  | .succ i, j, t => by
      show shiftIter grp p (Peano.Add.add (σ i) j) t
            = mckayShift grp p (shiftIter grp p i (shiftIter grp p j t))
      rw [Peano.Add.succ_add]
      show mckayShift grp p (shiftIter grp p (Peano.Add.add i j) t) = _
      rw [shiftIter_add grp p i j t]

-- ==================================================================
-- §14. Extensionalidad de tuplas y reglas de componentes (D.4.B parte 2)
-- ==================================================================

/-- Extensionalidad: las `(σ n)`-tuplas se determinan por sus σ n primeras
    componentes `getHead j` (`j ≤ n`). -/
theorem nPow_ext (G : HFSet) :
    ∀ (n : ℕ₀) (t₁ t₂ : HFSet),
      t₁ ∈ HFSet.nPow G (σ n) → t₂ ∈ HFSet.nPow G (σ n) →
      (∀ j : ℕ₀, le₀ j n → getHead j t₁ = getHead j t₂) → t₁ = t₂
  | .zero, t₁, t₂, h₁, h₂, h => by
      rw [HFSet.nPow_succ, HFSet.nPow_zero] at h₁ h₂
      obtain ⟨a₁, b₁, ha₁, _, heq₁⟩ := (HFSet.mem_cartProd _ _ _).mp h₁
      obtain ⟨a₂, b₂, ha₂, _, heq₂⟩ := (HFSet.mem_cartProd _ _ _).mp h₂
      have ea₁ : a₁ = HFSet.empty := (HFSet.mem_singleton _ _).mp ha₁
      have ea₂ : a₂ = HFSet.empty := (HFSet.mem_singleton _ _).mp ha₂
      have hb : b₁ = b₂ := by
        have e1 : getHead 𝟘 t₁ = b₁ := by
          show HFSet.snd t₁ = b₁
          rw [heq₁]; exact HFSet.snd_orderedPair_eq' _ _
        have e2 : getHead 𝟘 t₂ = b₂ := by
          show HFSet.snd t₂ = b₂
          rw [heq₂]; exact HFSet.snd_orderedPair_eq' _ _
        rw [← e1, ← e2]; exact h 𝟘 (le_refl 𝟘)
      rw [heq₁, heq₂, ea₁, ea₂, hb]
  | .succ m, t₁, t₂, h₁, h₂, h => by
      rw [HFSet.nPow_succ] at h₁ h₂
      obtain ⟨a₁, b₁, ha₁, _, heq₁⟩ := (HFSet.mem_cartProd _ _ _).mp h₁
      obtain ⟨a₂, b₂, ha₂, _, heq₂⟩ := (HFSet.mem_cartProd _ _ _).mp h₂
      have hb : b₁ = b₂ := by
        have e1 : getHead 𝟘 t₁ = b₁ := by
          show HFSet.snd t₁ = b₁
          rw [heq₁]; exact HFSet.snd_orderedPair_eq' _ _
        have e2 : getHead 𝟘 t₂ = b₂ := by
          show HFSet.snd t₂ = b₂
          rw [heq₂]; exact HFSet.snd_orderedPair_eq' _ _
        rw [← e1, ← e2]; exact h 𝟘 (Peano.Order.zero_le _)
      have ha : a₁ = a₂ := by
        apply nPow_ext G m a₁ a₂ ha₁ ha₂
        intro j hjm
        have e1 : getHead (σ j) t₁ = getHead j a₁ := by
          show getHead j (HFSet.fst t₁) = getHead j a₁
          rw [heq₁, HFSet.fst_orderedPair_eq']
        have e2 : getHead (σ j) t₂ = getHead j a₂ := by
          show getHead j (HFSet.fst t₂) = getHead j a₂
          rw [heq₂, HFSet.fst_orderedPair_eq']
        rw [← e1, ← e2]
        exact h (σ j) ((Peano.Order.succ_le_succ_iff _ _).mpr hjm)
      rw [heq₁, heq₂, ha, hb]

/-- Lema auxiliar: `getHead j (dropHead (σ n) t) = getHead j t` cuando `j ≤ n`. -/
theorem getHead_dropHead :
    ∀ (n j : ℕ₀) (t : HFSet), le₀ j n →
      getHead j (dropHead (σ n) t) = getHead j t
  | .zero,   .zero,   t, _ => by
      show HFSet.snd (dropHead (σ 𝟘) t) = HFSet.snd t
      show HFSet.snd ⟪dropHead 𝟘 (HFSet.fst t), HFSet.snd t⟫ = HFSet.snd t
      rw [HFSet.snd_orderedPair_eq']
  | .zero,   .succ _, _, h => by
      exact (Peano.Order.not_succ_le_zero _ h).elim
  | .succ m, .zero,   t, _ => by
      show HFSet.snd (dropHead (σ (σ m)) t) = HFSet.snd t
      show HFSet.snd ⟪dropHead (σ m) (HFSet.fst t), HFSet.snd t⟫ = HFSet.snd t
      rw [HFSet.snd_orderedPair_eq']
  | .succ m, .succ j', t, h => by
      have hjm : le₀ j' m := Peano.Order.succ_le_succ_then h
      show getHead j' (HFSet.fst (dropHead (σ (σ m)) t)) = getHead j' (HFSet.fst t)
      show getHead j' (HFSet.fst ⟪dropHead (σ m) (HFSet.fst t), HFSet.snd t⟫)
            = getHead j' (HFSet.fst t)
      rw [HFSet.fst_orderedPair_eq']
      exact getHead_dropHead m j' (HFSet.fst t) hjm

/-- Regla de componente 0 del shift: `getHead 0 (shift t) = getHead n t`. -/
theorem mckayShift_getHead_zero (grp : HFGroup) (n : ℕ₀) (t : HFSet) :
    getHead 𝟘 (mckayShift grp (σ n) t) = getHead n t := by
  show HFSet.snd (mckayShift grp (σ n) t) = getHead n t
  show HFSet.snd ⟪dropHead n t, getHead n t⟫ = getHead n t
  rw [HFSet.snd_orderedPair_eq']

/-- Regla de componente `σ j` del shift: para `σ j ≤ n`,
    `getHead (σ j) (shift t) = getHead j t`. -/
theorem mckayShift_getHead_succ (grp : HFGroup) :
    ∀ (n j : ℕ₀) (t : HFSet), le₀ (σ j) n →
      getHead (σ j) (mckayShift grp (σ n) t) = getHead j t
  | .zero,   j, _, h => by
      exact (Peano.Order.not_succ_le_zero _ h).elim
  | .succ m, j, t, h => by
      have hjm : le₀ j m := Peano.Order.succ_le_succ_then h
      show getHead j (HFSet.fst (mckayShift grp (σ (σ m)) t)) = getHead j t
      show getHead j (HFSet.fst ⟪dropHead (σ m) t, getHead (σ m) t⟫) = getHead j t
      rw [HFSet.fst_orderedPair_eq']
      exact getHead_dropHead m j t hjm

-- §15. Función predIndex/predIter y periodicidad (D.4.B parte 2, paso 3)

/-- Índice cíclico decreciente sobre `{0,...,n}`: `0 ↦ n`, `σ j ↦ j`. -/
def predIndex (n : ℕ₀) : ℕ₀ → ℕ₀
  | .zero   => n
  | .succ j => j

/-- Iteración `k` veces de `predIndex n`. -/
def predIter (n : ℕ₀) : ℕ₀ → ℕ₀ → ℕ₀
  | .zero,   j => j
  | .succ k, j => predIter n k (predIndex n j)

theorem predIter_zero (n j : ℕ₀) : predIter n 𝟘 j = j := rfl

theorem predIter_succ (n k j : ℕ₀) :
    predIter n (σ k) j = predIter n k (predIndex n j) := rfl

/-- Variante "trasera": `predIter (σ k) = predIndex ∘ predIter k`. -/
theorem predIter_succ_right (n : ℕ₀) :
    ∀ k j, predIter n (σ k) j = predIndex n (predIter n k j)
  | .zero,    j => rfl
  | .succ k', j => by
      show predIter n (σ (σ k')) j = predIndex n (predIter n (σ k') j)
      rw [predIter_succ n (σ k') j, predIter_succ_right n k' (predIndex n j)]
      rfl

theorem predIter_add (n a : ℕ₀) :
    ∀ b j, predIter n (Peano.Add.add a b) j = predIter n b (predIter n a j)
  | .zero,   _ => rfl
  | .succ b', j => by
      show predIter n (Peano.Add.add a (σ b')) j
            = predIter n (σ b') (predIter n a j)
      have hadd : Peano.Add.add a (σ b') = σ (Peano.Add.add a b') := rfl
      rw [hadd, predIter_succ_right n (Peano.Add.add a b') j,
          predIter_add n a b' j, predIter_succ_right n b' (predIter n a j)]

theorem predIter_self_zero (n : ℕ₀) :
    ∀ j, predIter n j j = 𝟘
  | .zero    => rfl
  | .succ j' => by
      show predIter n (σ j') (σ j') = 𝟘
      rw [predIter_succ n j' (σ j')]
      show predIter n j' j' = 𝟘
      exact predIter_self_zero n j'

theorem predIter_succ_self (n j : ℕ₀) :
    predIter n (σ j) j = n := by
  rw [predIter_succ_right n j j, predIter_self_zero n j]
  rfl

theorem predIter_le_eq_sub (n : ℕ₀) :
    ∀ k j, le₀ k j → predIter n k j = Peano.Sub.sub j k
  | .zero,    j, _ => by
      show j = Peano.Sub.sub j 𝟘
      rw [Peano.Sub.sub_zero]
  | .succ _,  .zero, h =>
      (Peano.Order.not_succ_le_zero _ h).elim
  | .succ k', .succ j', h => by
      have hk : le₀ k' j' := Peano.Order.succ_le_succ_then h
      show predIter n k' (predIndex n (σ j')) = Peano.Sub.sub (σ j') (σ k')
      show predIter n k' j' = Peano.Sub.sub (σ j') (σ k')
      rw [predIter_le_eq_sub n k' j' hk, Peano.Sub.sub_succ_succ_eq]

/-- `sub n (sub n j) = j` para `j ≤ n`, vía `sub_k_add_k` + `add_k_sub_k`. -/
theorem sub_sub_self (n j : ℕ₀) (h : le₀ j n) :
    Peano.Sub.sub n (Peano.Sub.sub n j) = j := by
  have h1 : Peano.Add.add (Peano.Sub.sub n j) j = n := Peano.Sub.sub_k_add_k n j h
  have h2 : Peano.Sub.sub (Peano.Add.add (Peano.Sub.sub n j) j) (Peano.Sub.sub n j) = j :=
    Peano.Sub.add_k_sub_k j (Peano.Sub.sub n j)
  rw [h1] at h2
  exact h2

/-- Periodicidad: `predIter n (σ n) j = j` para `j ≤ n`. -/
theorem predIter_period (n : ℕ₀) :
    ∀ j, le₀ j n → predIter n (σ n) j = j := by
  intro j hjn
  have hsum : Peano.Add.add j (Peano.Sub.sub n j) = n := by
    have := Peano.Sub.sub_k_add_k n j hjn
    -- this : add (sub n j) j = n
    have hcomm : Peano.Add.add j (Peano.Sub.sub n j)
               = Peano.Add.add (Peano.Sub.sub n j) j := Peano.Add.add_comm _ _
    rw [hcomm]; exact this
  have heq : σ n = Peano.Add.add (σ j) (Peano.Sub.sub n j) := by
    rw [Peano.Add.succ_add]
    show σ n = σ (Peano.Add.add j (Peano.Sub.sub n j))
    rw [hsum]
  have hle : le₀ (Peano.Sub.sub n j) n := Peano.Sub.sub_le_self n j
  rw [heq, predIter_add n (σ j) (Peano.Sub.sub n j) j,
      predIter_succ_self n j,
      predIter_le_eq_sub n (Peano.Sub.sub n j) n hle,
      sub_sub_self n j hjn]

-- §16. Ensamblaje: shiftIter_getHead + shiftIter_period (D.4.B parte 2, paso 4)

/-- Componente `j`-ésima de iterar el shift: equivale a aplicar `predIter` al índice. -/
theorem shiftIter_getHead (grp : HFGroup) (n : ℕ₀) :
    ∀ (k : ℕ₀) (j : ℕ₀), le₀ j n → ∀ (t : HFSet),
      getHead j (shiftIter grp (σ n) k t) = getHead (predIter n k j) t
  | .zero,    _,       _,  _ => rfl
  | .succ k', .zero,   _,  t => by
      show getHead 𝟘 (mckayShift grp (σ n) (shiftIter grp (σ n) k' t))
            = getHead (predIter n (σ k') 𝟘) t
      rw [mckayShift_getHead_zero grp n]
      have ih := shiftIter_getHead grp n k' n (Peano.Order.le_refl n) t
      rw [ih]
      rfl
  | .succ k', .succ j', h, t => by
      have hj : le₀ j' n := Peano.Order.le_succ_then_le h
      show getHead (σ j') (mckayShift grp (σ n) (shiftIter grp (σ n) k' t))
            = getHead (predIter n (σ k') (σ j')) t
      rw [mckayShift_getHead_succ grp n j' _ h]
      have ih := shiftIter_getHead grp n k' j' hj t
      rw [ih]
      rfl

/-- **Periodicidad del shift** (D.4.B parte 2 completo):
    para `t ∈ nPow grp.G (σ n)`, iterar el shift `σ n` veces devuelve `t`. -/
theorem shiftIter_period (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    shiftIter grp (σ n) (σ n) t = t := by
  apply nPow_ext grp.G n (shiftIter grp (σ n) (σ n) t) t
    (shiftIter_mem_nPow grp (σ n) (σ n) ht) ht
  intro j hjn
  rw [shiftIter_getHead grp n (σ n) j hjn t, predIter_period n j hjn]

-- §17. D.4.C parte 1: órbitas (enumeración y cota de cardinal)

/-- Enumeración auxiliar: `orbitEnum grp p m t = {shiftIter k t | k ≤ m}`. -/
def orbitEnum (grp : HFGroup) (p : ℕ₀) : ℕ₀ → HFSet → HFSet
  | .zero,   t => HFSet.singleton (shiftIter grp p 𝟘 t)
  | .succ m, t => HFSet.insert (shiftIter grp p (σ m) t) (orbitEnum grp p m t)

theorem mem_orbitEnum (grp : HFGroup) (p : ℕ₀) :
    ∀ (m : ℕ₀) (t x : HFSet),
      x ∈ orbitEnum grp p m t ↔ ∃ k : ℕ₀, le₀ k m ∧ x = shiftIter grp p k t
  | .zero, t, x => by
      show x ∈ HFSet.singleton (shiftIter grp p 𝟘 t) ↔ _
      rw [HFSet.mem_singleton]
      refine ⟨fun hx => ⟨𝟘, le_refl 𝟘, hx⟩, ?_⟩
      rintro ⟨k, hk, hx⟩
      have hk0 : k = 𝟘 := le_zero_eq_wp hk
      rw [hx, hk0]
  | .succ m, t, x => by
      show x ∈ HFSet.insert (shiftIter grp p (σ m) t) (orbitEnum grp p m t) ↔ _
      rw [HFSet.mem_insert]
      constructor
      · rintro (hx | hx)
        · exact ⟨σ m, le_refl (σ m), hx⟩
        · obtain ⟨k, hk, hx⟩ := (mem_orbitEnum grp p m t x).mp hx
          exact ⟨k, le_n_m_then_le_n_sm_wp hk, hx⟩
      · rintro ⟨k, hk, hx⟩
        rcases (le_succ_iff_le_or_eq k m).mp hk with hk' | hk'
        · exact Or.inr ((mem_orbitEnum grp p m t x).mpr ⟨k, hk', hx⟩)
        · exact Or.inl (hx.trans (congrArg (fun i => shiftIter grp p i t) hk'))

theorem orbitEnum_card_le_succ (grp : HFGroup) (p : ℕ₀) :
    ∀ (m : ℕ₀) (t : HFSet), le₀ (HFSet.card (orbitEnum grp p m t)) (σ m)
  | .zero, t => by
      show le₀ (HFSet.card (HFSet.singleton (shiftIter grp p 𝟘 t))) (σ 𝟘)
      have heq : HFSet.singleton (shiftIter grp p 𝟘 t)
                  = HFSet.insert (shiftIter grp p 𝟘 t) HFSet.empty :=
        HFSet.extensionality _ _ fun z => by
          rw [HFSet.mem_singleton, HFSet.mem_insert]
          exact ⟨Or.inl, fun h => h.elim id (absurd · (HFSet.not_mem_empty z))⟩
      rw [heq, HFSet.card_insert _ _ (HFSet.not_mem_empty _), HFSet.card_empty]
      exact le_refl (σ 𝟘)
  | .succ m, t => by
      show le₀ (HFSet.card
        (HFSet.insert (shiftIter grp p (σ m) t) (orbitEnum grp p m t))) (σ (σ m))
      by_cases hin : shiftIter grp p (σ m) t ∈ orbitEnum grp p m t
      · have heq : HFSet.insert (shiftIter grp p (σ m) t) (orbitEnum grp p m t)
                    = orbitEnum grp p m t := by
          apply HFSet.extensionality; intro z
          rw [HFSet.mem_insert]
          exact ⟨fun h => h.elim (· ▸ hin) id, Or.inr⟩
        rw [heq]
        exact le_trans _ _ _ (orbitEnum_card_le_succ grp p m t)
                              (lt_imp_le _ _ (lt_succ_self (σ m)))
      · rw [HFSet.card_insert _ _ hin]
        exact succ_le_succ_if (orbitEnum_card_le_succ grp p m t)

/-- Órbita de `t` bajo la acción del shift de período `σ n`. -/
def orbitOf (grp : HFGroup) (n : ℕ₀) (t : HFSet) : HFSet :=
  orbitEnum grp (σ n) n t

theorem mem_orbitOf (grp : HFGroup) (n : ℕ₀) (t x : HFSet) :
    x ∈ orbitOf grp n t ↔ ∃ k : ℕ₀, le₀ k n ∧ x = shiftIter grp (σ n) k t :=
  mem_orbitEnum grp (σ n) n t x

/-- `card (orbitOf grp n t) ≤ σ n`. -/
theorem card_orbitOf_le (grp : HFGroup) (n : ℕ₀) (t : HFSet) :
    le₀ (HFSet.card (orbitOf grp n t)) (σ n) :=
  orbitEnum_card_le_succ grp (σ n) n t

/-- La órbita es cerrada bajo el shift: si `t' ∈ orbitOf grp n t`, entonces
    `mckayShift grp (σ n) t' ∈ orbitOf grp n t`. -/
theorem mckayShift_mem_orbitOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    ∀ {t' : HFSet}, t' ∈ orbitOf grp n t →
      mckayShift grp (σ n) t' ∈ orbitOf grp n t := by
  intro t' h
  obtain ⟨k, hk, hk_eq⟩ := (mem_orbitOf grp n t t').mp h
  have hshift : mckayShift grp (σ n) t' = shiftIter grp (σ n) (σ k) t := by
    rw [hk_eq]; rfl
  rcases hk with hk_lt | hk_eq2
  · have hsk : le₀ (σ k) n :=
      (le_iff_lt_succ (σ k) n).mpr ((lt_iff_lt_σ_σ k n).mp hk_lt)
    exact (mem_orbitOf grp n t _).mpr ⟨σ k, hsk, hshift⟩
  · refine (mem_orbitOf grp n t _).mpr ⟨𝟘, Peano.Order.zero_le n, ?_⟩
    show mckayShift grp (σ n) t' = t
    rw [hshift, hk_eq2]
    exact shiftIter_period grp n t ht

-- §18. D.4.C parte 2: simetría e igualdad de órbitas que se intersectan

/-- Cualquier iteración del shift cae en la órbita. -/
theorem shiftIter_mem_orbitOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    ∀ k : ℕ₀, shiftIter grp (σ n) k t ∈ orbitOf grp n t
  | .zero =>
      (mem_orbitOf grp n t _).mpr ⟨𝟘, Peano.Order.zero_le n, rfl⟩
  | .succ k' => by
      show mckayShift grp (σ n) (shiftIter grp (σ n) k' t) ∈ orbitOf grp n t
      exact mckayShift_mem_orbitOf grp n t ht
        (shiftIter_mem_orbitOf grp n t ht k')

/-- Índice inverso para el shift: si `s = shiftIter k t` con `k ≤ n`, entonces
    `t = shiftIter (invIdx n k) s`. -/
def invIdx (n : ℕ₀) : ℕ₀ → ℕ₀
  | .zero    => 𝟘
  | .succ k' => Peano.Sub.sub n k'

theorem invIdx_le (n : ℕ₀) :
    ∀ k, le₀ k n → le₀ (invIdx n k) n
  | .zero,    _ => Peano.Order.zero_le n
  | .succ _,  _ => Peano.Sub.sub_le_self n _

theorem shiftIter_invIdx (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    ∀ k, le₀ k n →
      shiftIter grp (σ n) (invIdx n k) (shiftIter grp (σ n) k t) = t
  | .zero,    _ => rfl
  | .succ k', h => by
      have hk' : le₀ k' n := Peano.Order.le_succ_then_le h
      show shiftIter grp (σ n) (Peano.Sub.sub n k') (shiftIter grp (σ n) (σ k') t) = t
      rw [← shiftIter_add]
      have hadd : Peano.Add.add (Peano.Sub.sub n k') (σ k') = σ n := by
        show Peano.Add.add (Peano.Sub.sub n k') (σ k') = σ n
        rw [Peano.Add.add_succ]
        show σ (Peano.Add.add (Peano.Sub.sub n k') k') = σ n
        rw [Peano.Sub.sub_k_add_k n k' hk']
      rw [hadd]
      exact shiftIter_period grp n t ht

/-- Si `s ∈ orbitOf grp n t`, entonces `orbitOf grp n s ⊆ orbitOf grp n t`. -/
theorem orbitOf_subset (grp : HFGroup) (n : ℕ₀) (t s : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hs : s ∈ orbitOf grp n t) :
    orbitOf grp n s ⊆ orbitOf grp n t := by
  intro x hx
  obtain ⟨k, _, hsk⟩ := (mem_orbitOf grp n t s).mp hs
  obtain ⟨j, _, hxj⟩ := (mem_orbitOf grp n s x).mp hx
  have hxeq : x = shiftIter grp (σ n) (Peano.Add.add j k) t := by
    rw [hxj, hsk, ← shiftIter_add]
  rw [hxeq]
  exact shiftIter_mem_orbitOf grp n t ht (Peano.Add.add j k)

/-- Si `s ∈ orbitOf grp n t`, entonces las órbitas coinciden. -/
theorem orbitOf_eq_of_mem (grp : HFGroup) (n : ℕ₀) (t s : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hs : s ∈ orbitOf grp n t) :
    orbitOf grp n s = orbitOf grp n t := by
  have hsN : s ∈ HFSet.nPow grp.G (σ n) := by
    obtain ⟨k, _, hsk⟩ := (mem_orbitOf grp n t s).mp hs
    rw [hsk]
    exact shiftIter_mem_nPow grp (σ n) k ht
  have ht_s : t ∈ orbitOf grp n s := by
    obtain ⟨k, hk, hsk⟩ := (mem_orbitOf grp n t s).mp hs
    refine (mem_orbitOf grp n s t).mpr ⟨invIdx n k, invIdx_le n k hk, ?_⟩
    rw [hsk]
    exact (shiftIter_invIdx grp n t ht k hk).symm
  apply HFSet.subset_antisymm
  · exact orbitOf_subset grp n t s ht hs
  · exact orbitOf_subset grp n s t hsN ht_s

/-- Dos órbitas o son iguales o son disjuntas. -/
theorem orbitOf_eq_or_disjoint (grp : HFGroup) (n : ℕ₀) (t s : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hs : s ∈ HFSet.nPow grp.G (σ n)) :
    orbitOf grp n t = orbitOf grp n s ∨
    (∀ x, ¬ (x ∈ orbitOf grp n t ∧ x ∈ orbitOf grp n s)) := by
  by_cases hdisj : ∀ x, ¬ (x ∈ orbitOf grp n t ∧ x ∈ orbitOf grp n s)
  · exact Or.inr hdisj
  · refine Or.inl ?_
    -- Extracción clásica del testigo.
    have hex : ∃ x, x ∈ orbitOf grp n t ∧ x ∈ orbitOf grp n s :=
      Classical.byContradiction (fun hne =>
        hdisj (fun x hx => hne ⟨x, hx⟩))
    obtain ⟨x, hxt, hxs⟩ := hex
    have h1 : orbitOf grp n x = orbitOf grp n t :=
      orbitOf_eq_of_mem grp n t x ht hxt
    have h2 : orbitOf grp n x = orbitOf grp n s :=
      orbitOf_eq_of_mem grp n s x hs hxs
    rw [← h1, h2]

end HFAlgebra
