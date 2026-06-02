/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Sylow.lean
-- p-subgrupos, exponente de Sylow, infraestructura de McKay (D.4) y
-- prueba de Cauchy vía McKay: si p primo, p ∣ |G|, existe subgrupo de orden p.
--
-- Paridad con Peano/Combinatorics/GroupTheory/Sylow/Sylow.lean.
--
-- Público (definiciones e infraestructura):
--   isPSubgroup / isSylowExponent / isSylowSubgroup
--   trivial / trivial_card
--   pow_dvd_card_of_le / sylow_card_eq / sylow_first_zero
--   gpow / gpow_zero / gpow_succ / gpow_one / gpow_mem / gpow_add
--   order / order_pos / order_ne_zero / gpow_order_eq_id / order_minimal
--   order_le_card / gpow_mul_order_eq_id / gpow_mod_order
--   cyclicCarrier / cyclicSubgroup
--   mckayCarrier / mckayShift / mckayFixedPoints / shiftIter / orbitOf / periodOf
--
-- Público (D.3 – D.4.D, argumento de McKay):
--   dvd_card_mckayCarrier_succ          : σ n primo, p ∣ |G| → p ∣ |carrier|   (D.3)
--   card_orbitOf_eq_periodOf            : card(orbitOf t) = periodOf t           (§22)
--   card_orbitOf_one_or_succ            : card ∈ {1, σ n} en caso primo          (§23)
--   periodOf_eq_one_iff_fixed           : period = 1 ↔ t fijo por shift          (§24)
--   card_orbitOf_eq_one_iff_fixed       : card = 1 ↔ t fijo por shift            (§24)
--   card_orbitOf_eq_succ_of_not_fixed   : ¬fijo → card(orbit) = σ n             (§25)
--   succ_n_dvd_card_of_shift_closed_no_fixed : σ n ∣ card S, S ⊆ carrier        (§26)
--   succ_n_dvd_card_mckayFixedPoints    : σ n ∣ card(fixedPoints)  (D.4.D/McKay) (§27)
--
-- Público (§28–§32: punto fijo canónico, teorema de Cauchy):
--   eTuple_mem_mckayFixedPoints         : eTuple grp p ∈ mckayFixedPoints grp p  (§28)
--   order_dvd_of_gpow_eq_id             : g^m = e → order g ∣ m                 (§30)
--   order_eq_prime_of_pow               : g^p = e, primo p, g ≠ e → order g = p  (§30)
--   cyclicCarrier_card_eq_order         : card(⟨g⟩) = order g                   (§31)
--   cauchy_minimal                      : primo p, p ∣ |G| → ∃ sub, card sub = p (§32)
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
import AczelSetTheory.Axioms.Choice
import AczelSetTheory.Operations.NPow
import AczelSetTheory.Algebra.Action
import AczelSetTheory.Algebra.CorrespondenceTheorem
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes
import Peano.Prelim.Classical
import Peano.PeanoNat.WellFounded

namespace HFAlgebra

open Peano Peano.Arith Peano.Primes

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
abbrev order (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) : ℕ₀ :=
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
abbrev cyclicCarrier (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) : HFSet :=
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
abbrev cyclicSubgroup (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
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

-- ==================================================================
-- §19. D.4.C parte 3: período mínimo de una tupla bajo el shift
-- ==================================================================

/-- Especificación del período mínimo vía WOP: existe único `k > 0` con
    `shiftIter k t = t` y minimal entre tales. Existencia: `shiftIter_period`. -/
private theorem periodOf_wop (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    ExistsUnique (fun k : ℕ₀ =>
      (lt₀ 𝟘 k ∧ shiftIter grp (σ n) k t = t) ∧
      ∀ m : ℕ₀, (lt₀ 𝟘 m ∧ shiftIter grp (σ n) m t = t) → le₀ k m) :=
  Peano.WellFounded.well_ordering_principle
    (fun k => lt₀ 𝟘 k ∧ shiftIter grp (σ n) k t = t)
    ⟨σ n, zero_lt_succ n, shiftIter_period grp n t ht⟩

/-- Período mínimo de `t` bajo el shift: mínimo `k > 0` con `shiftIter k t = t`. -/
abbrev periodOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) : ℕ₀ :=
  Peano.choose_unique (periodOf_wop grp n t ht)

private theorem periodOf_spec (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    (lt₀ 𝟘 (periodOf grp n t ht) ∧
     shiftIter grp (σ n) (periodOf grp n t ht) t = t) ∧
    ∀ m : ℕ₀, (lt₀ 𝟘 m ∧ shiftIter grp (σ n) m t = t) →
      le₀ (periodOf grp n t ht) m :=
  Peano.choose_spec_unique (periodOf_wop grp n t ht)

theorem periodOf_pos (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    lt₀ 𝟘 (periodOf grp n t ht) := (periodOf_spec grp n t ht).1.1

theorem periodOf_ne_zero (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    periodOf grp n t ht ≠ 𝟘 :=
  (ne_of_lt 𝟘 _ (periodOf_pos grp n t ht)).symm

theorem shiftIter_periodOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    shiftIter grp (σ n) (periodOf grp n t ht) t = t := (periodOf_spec grp n t ht).1.2

theorem periodOf_minimal (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n))
    {m : ℕ₀} (hm_pos : lt₀ 𝟘 m) (hm_eq : shiftIter grp (σ n) m t = t) :
    le₀ (periodOf grp n t ht) m :=
  (periodOf_spec grp n t ht).2 m ⟨hm_pos, hm_eq⟩

theorem periodOf_le_succ_n (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    le₀ (periodOf grp n t ht) (σ n) :=
  periodOf_minimal grp n t ht (zero_lt_succ n) (shiftIter_period grp n t ht)

-- ==================================================================
-- §20. D.4.C parte 3: período divide a σ n (vía divMod)
-- ==================================================================

/-- Iteración por múltiplos del período: `shiftIter (q · period) t = t`. -/
private theorem shiftIter_mul_periodOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    ∀ q : ℕ₀, shiftIter grp (σ n) (mul q (periodOf grp n t ht)) t = t
  | .zero    => by
      show shiftIter grp (σ n) (mul 𝟘 (periodOf grp n t ht)) t = t
      rw [zero_mul]; rfl
  | .succ q' => by
      show shiftIter grp (σ n) (mul (σ q') (periodOf grp n t ht)) t = t
      rw [succ_mul]
      rw [shiftIter_add, shiftIter_periodOf grp n t ht]
      exact shiftIter_mul_periodOf grp n t ht q'

/-- **`periodOf` divide a `σ n`** (vía división euclídea y minimalidad). -/
theorem periodOf_dvd_succ_n (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    Divides (periodOf grp n t ht) (σ n) := by
  have hp_ne : periodOf grp n t ht ≠ 𝟘 := periodOf_ne_zero grp n t ht
  let p := periodOf grp n t ht
  have hspec : σ n = add (mul (div (σ n) p) p) (mod (σ n) p) := by
    have := divMod_spec (σ n) p hp_ne
    show σ n = add (mul (divMod (σ n) p).1 p) (divMod (σ n) p).2
    exact this
  have hr_lt : lt₀ (mod (σ n) p) p := mod_lt (σ n) p hp_ne
  have h1 : shiftIter grp (σ n) (σ n) t = t := shiftIter_period grp n t ht
  -- Reordenamos: σ n = (mod) + (div * p), aplicamos shiftIter_add y shiftIter_mul_periodOf.
  have hspec' : σ n = add (mod (σ n) p) (mul (div (σ n) p) p) := by
    have hc : add (mul (div (σ n) p) p) (mod (σ n) p)
            = add (mod (σ n) p) (mul (div (σ n) p) p) :=
      add_comm _ _
    exact hspec.trans hc
  have hsubst : shiftIter grp (σ n) (σ n) t
               = shiftIter grp (σ n)
                  (add (mod (σ n) p) (mul (div (σ n) p) p)) t :=
    congrArg (fun k => shiftIter grp (σ n) k t) hspec'
  have hsplit : shiftIter grp (σ n)
                  (add (mod (σ n) p) (mul (div (σ n) p) p)) t
               = shiftIter grp (σ n) (mod (σ n) p)
                  (shiftIter grp (σ n) (mul (div (σ n) p) p) t) :=
    shiftIter_add grp (σ n) (mod (σ n) p) (mul (div (σ n) p) p) t
  have hmul : shiftIter grp (σ n) (mul (div (σ n) p) p) t = t :=
    shiftIter_mul_periodOf grp n t ht (div (σ n) p)
  rw [hmul] at hsplit
  have h2 : shiftIter grp (σ n) (mod (σ n) p) t = t :=
    (hsubst.trans hsplit).symm.trans h1
  -- Si mod > 0, contradice minimalidad.
  have hr_zero : mod (σ n) p = 𝟘 := by
    rcases trichotomy (mod (σ n) p) 𝟘 with hlt | heq | hgt
    · exact (nlt_n_0 _ hlt).elim
    · exact heq
    · have hle : le₀ p (mod (σ n) p) := periodOf_minimal grp n t ht hgt h2
      exact (le_not_lt hle hr_lt).elim
  -- Así σ n = mul p (div (σ n) p).
  refine ⟨div (σ n) p, ?_⟩
  show σ n = mul p (div (σ n) p)
  have e1 : add (mul (div (σ n) p) p) (mod (σ n) p)
          = add (mul (div (σ n) p) p) 𝟘 :=
    congrArg (add _) hr_zero
  have e2 : add (mul (div (σ n) p) p) 𝟘 = mul (div (σ n) p) p := add_zero _
  have e3 : mul (div (σ n) p) p = mul p (div (σ n) p) := mul_comm _ _
  exact hspec.trans (e1.trans (e2.trans e3))

-- ==================================================================
-- §21. D.4.C parte 3: cancelación e inyectividad bajo el período
-- ==================================================================

/-- **Cancelación**: si `shiftIter i t = shiftIter j t` con `i ≤ j ≤ n`,
    entonces `shiftIter (j - i) t = t`. Vía `shiftIter_invIdx`. -/
private theorem shiftIter_cancel (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    ∀ i j : ℕ₀, le₀ i j → le₀ j n →
      shiftIter grp (σ n) i t = shiftIter grp (σ n) j t →
      shiftIter grp (σ n) (Peano.Sub.sub j i) t = t
  | .zero, j, _, _, heq => by
      rw [Peano.Sub.sub_zero]
      exact heq.symm
  | .succ i', j, hij, hjn, heq => by
      have hi'n : le₀ i' n :=
        Peano.Order.le_succ_then_le (le_trans _ _ _ hij hjn)
      have hin : le₀ (σ i') n := le_trans _ _ _ hij hjn
      -- shiftIter (sub n i') (shiftIter (σ i') t) = t
      have hkey : shiftIter grp (σ n) (Peano.Sub.sub n i')
                    (shiftIter grp (σ n) (σ i') t) = t := by
        have := shiftIter_invIdx grp n t ht (σ i') hin
        show shiftIter grp (σ n) (invIdx n (σ i'))
                (shiftIter grp (σ n) (σ i') t) = t
        exact this
      -- Aplicar shiftIter (sub n i') al lado derecho de heq.
      have h := congrArg (shiftIter grp (σ n) (Peano.Sub.sub n i')) heq.symm
      rw [hkey] at h
      -- h : shiftIter (sub n i') (shiftIter j t) = t
      -- LHS = shiftIter (add (sub n i') j) t  (vía shiftIter_add inverso)
      have hLHS : shiftIter grp (σ n) (Peano.Sub.sub n i')
                    (shiftIter grp (σ n) j t)
                = shiftIter grp (σ n) (add (Peano.Sub.sub n i') j) t :=
        (shiftIter_add grp (σ n) (Peano.Sub.sub n i') j t).symm
      rw [hLHS] at h
      -- h : shiftIter (sub n i' + j) t = t
      -- Reescribir (sub n i' + j) = (σ n) + (sub j (σ i')).
      have hsig : add (Peano.Sub.sub n i') (σ i') = σ n := by
        rw [Peano.Add.add_succ]
        show σ (add (Peano.Sub.sub n i') i') = σ n
        rw [Peano.Sub.sub_k_add_k n i' hi'n]
      have hj_eq : j = add (Peano.Sub.sub j (σ i')) (σ i') :=
        (sub_k_add_k j (σ i') hij).symm
      have hrec : add (Peano.Sub.sub n i') j
                = add (σ n) (Peano.Sub.sub j (σ i')) := by
        calc add (Peano.Sub.sub n i') j
            = add (Peano.Sub.sub n i') (add (Peano.Sub.sub j (σ i')) (σ i')) := by
                rw [← hj_eq]
          _ = add (add (Peano.Sub.sub n i') (Peano.Sub.sub j (σ i'))) (σ i') := by
                rw [← add_assoc]
          _ = add (add (Peano.Sub.sub j (σ i')) (Peano.Sub.sub n i')) (σ i') := by
                rw [add_comm (Peano.Sub.sub n i') (Peano.Sub.sub j (σ i'))]
          _ = add (Peano.Sub.sub j (σ i')) (add (Peano.Sub.sub n i') (σ i')) := by
                rw [add_assoc]
          _ = add (Peano.Sub.sub j (σ i')) (σ n) := by rw [hsig]
          _ = add (σ n) (Peano.Sub.sub j (σ i')) := add_comm _ _
      rw [hrec] at h
      -- h : shiftIter (σ n + (j - σ i')) t = t
      -- Reescribir vía shiftIter_add: = shiftIter (σ n) (shiftIter (j - σ i') t).
      rw [shiftIter_add] at h
      -- h : shiftIter (σ n) (shiftIter (j - σ i') t) = t
      -- Aplicar shiftIter_period a (shiftIter (j - σ i') t), que sigue en nPow.
      have hmem : shiftIter grp (σ n) (Peano.Sub.sub j (σ i')) t ∈ HFSet.nPow grp.G (σ n) :=
        shiftIter_mem_nPow grp (σ n) (Peano.Sub.sub j (σ i')) ht
      rw [shiftIter_period grp n _ hmem] at h
      exact h

/-- **`shiftIter k t = t ↔ period ∣ k`**. -/
theorem shiftIter_eq_id_iff_periodOf_dvd (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (k : ℕ₀) :
    shiftIter grp (σ n) k t = t ↔ Divides (periodOf grp n t ht) k := by
  let p := periodOf grp n t ht
  have hp_ne : p ≠ 𝟘 := periodOf_ne_zero grp n t ht
  refine ⟨?_, ?_⟩
  · intro hk
    -- divMod: k = (div k p) * p + (mod k p), mod < p
    have hspec : k = add (mul (div k p) p) (mod k p) := by
      have := divMod_spec k p hp_ne
      show k = add (mul (divMod k p).1 p) (divMod k p).2
      exact this
    have hr_lt : lt₀ (mod k p) p := mod_lt k p hp_ne
    have hspec' : k = add (mod k p) (mul (div k p) p) := by
      have hc : add (mul (div k p) p) (mod k p)
              = add (mod k p) (mul (div k p) p) := add_comm _ _
      exact hspec.trans hc
    have hsubst : shiftIter grp (σ n) k t
                = shiftIter grp (σ n)
                    (add (mod k p) (mul (div k p) p)) t :=
      congrArg (fun m => shiftIter grp (σ n) m t) hspec'
    have hsplit : shiftIter grp (σ n)
                    (add (mod k p) (mul (div k p) p)) t
                = shiftIter grp (σ n) (mod k p)
                    (shiftIter grp (σ n) (mul (div k p) p) t) :=
      shiftIter_add grp (σ n) (mod k p) (mul (div k p) p) t
    have hmul : shiftIter grp (σ n) (mul (div k p) p) t = t :=
      shiftIter_mul_periodOf grp n t ht (div k p)
    rw [hmul] at hsplit
    have h2 : shiftIter grp (σ n) (mod k p) t = t :=
      (hsubst.trans hsplit).symm.trans hk
    have hr_zero : mod k p = 𝟘 := by
      rcases trichotomy (mod k p) 𝟘 with hlt | heq | hgt
      · exact (nlt_n_0 _ hlt).elim
      · exact heq
      · exact (le_not_lt (periodOf_minimal grp n t ht hgt h2) hr_lt).elim
    refine ⟨div k p, ?_⟩
    show k = mul p (div k p)
    have e1 : add (mul (div k p) p) (mod k p)
            = add (mul (div k p) p) 𝟘 :=
      congrArg (add _) hr_zero
    have e2 : add (mul (div k p) p) 𝟘 = mul (div k p) p := add_zero _
    have e3 : mul (div k p) p = mul p (div k p) := mul_comm _ _
    exact hspec.trans (e1.trans (e2.trans e3))
  · rintro ⟨q, hq⟩
    -- k = mul p q. shiftIter (mul p q) t = shiftIter (mul q p) t = t.
    have hcomm : mul p q = mul q p := mul_comm _ _
    have hkeq : k = mul q p := hq.trans hcomm
    rw [hkeq]
    exact shiftIter_mul_periodOf grp n t ht q

/-- **Inyectividad bajo el período**: si `i, j < periodOf` y `shiftIter i t = shiftIter j t`,
    entonces `i = j`. -/
theorem shiftIter_inj_below_period (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n))
    (i j : ℕ₀) (hi : lt₀ i (periodOf grp n t ht))
    (hj : lt₀ j (periodOf grp n t ht))
    (heq : shiftIter grp (σ n) i t = shiftIter grp (σ n) j t) :
    i = j := by
  -- WLOG i ≤ j; aplicamos cancelación.
  have hp_le : le₀ (periodOf grp n t ht) (σ n) := periodOf_le_succ_n grp n t ht
  have hi_lt_sn : lt₀ i (σ n) := lt_of_lt_of_le hi hp_le
  have hj_lt_sn : lt₀ j (σ n) := lt_of_lt_of_le hj hp_le
  have hin : le₀ i n := (le_iff_lt_succ i n).mpr hi_lt_sn
  have hjn : le₀ j n := (le_iff_lt_succ j n).mpr hj_lt_sn
  -- Helper: bajo a ≤ b, deduce a = b.
  have helper : ∀ a b : ℕ₀, le₀ a b → lt₀ b (periodOf grp n t ht) → le₀ b n →
      shiftIter grp (σ n) a t = shiftIter grp (σ n) b t → a = b := by
    intro a b hab hb_lt hbn heq'
    have hcancel : shiftIter grp (σ n) (Peano.Sub.sub b a) t = t :=
      shiftIter_cancel grp n t ht a b hab hbn heq'
    rcases trichotomy (Peano.Sub.sub b a) 𝟘 with hlt | heq0 | hgt
    · exact (nlt_n_0 _ hlt).elim
    · -- sub b a = 0 ⇒ a = b vía sub_k_add_k.
      have hsum : add (Peano.Sub.sub b a) a = b := sub_k_add_k b a hab
      have hzeroa : add 𝟘 a = b := heq0 ▸ hsum
      have : a = b := by rw [Peano.Add.zero_add] at hzeroa; exact hzeroa
      exact this
    · -- sub b a > 0 + shiftIter (sub b a) t = t ⇒ period ≤ sub b a ≤ b < period.
      have hge : le₀ (periodOf grp n t ht) (Peano.Sub.sub b a) :=
        periodOf_minimal grp n t ht hgt hcancel
      have hsub_le_b : le₀ (Peano.Sub.sub b a) b := Peano.Sub.sub_le_self b a
      have hp_le_b : le₀ (periodOf grp n t ht) b := le_trans _ _ _ hge hsub_le_b
      exact (le_not_lt hp_le_b hb_lt).elim
  rcases trichotomy i j with hij | hij | hij
  · exact helper i j (lt_imp_le _ _ hij) hj hjn heq
  · exact hij
  · exact (helper j i (lt_imp_le _ _ hij) hi hin heq.symm).symm

-- ==================================================================
-- §22. D.4.C parte 4: card (orbitOf) = periodOf, vía enumeración
-- ==================================================================

/-- Enumeración por el período: `periodEnum grp p m t = {shiftIter k t | k < m}`. -/
def periodEnum (grp : HFGroup) (p : ℕ₀) : ℕ₀ → HFSet → HFSet
  | .zero,   _ => HFSet.empty
  | .succ m, t => HFSet.insert (shiftIter grp p m t) (periodEnum grp p m t)

theorem mem_periodEnum (grp : HFGroup) (p : ℕ₀) :
    ∀ (m : ℕ₀) (t x : HFSet),
      x ∈ periodEnum grp p m t ↔ ∃ k : ℕ₀, lt₀ k m ∧ x = shiftIter grp p k t
  | .zero, _, x => by
      show x ∈ HFSet.empty ↔ _
      refine ⟨fun h => absurd h (HFSet.not_mem_empty x), ?_⟩
      rintro ⟨k, hk, _⟩
      exact (nlt_n_0 k hk).elim
  | .succ m, t, x => by
      show x ∈ HFSet.insert (shiftIter grp p m t) (periodEnum grp p m t) ↔ _
      rw [HFSet.mem_insert]
      constructor
      · rintro (hx | hx)
        · exact ⟨m, lt_succ_self m, hx⟩
        · obtain ⟨k, hk, hx⟩ := (mem_periodEnum grp p m t x).mp hx
          exact ⟨k, lt_trans _ _ _ hk (lt_succ_self m), hx⟩
      · rintro ⟨k, hk, hx⟩
        have hk_le_m : le₀ k m := (le_iff_lt_succ k m).mpr hk
        rcases trichotomy k m with h | h | h
        · exact Or.inr ((mem_periodEnum grp p m t x).mpr ⟨k, h, hx⟩)
        · exact Or.inl (hx.trans (congrArg (fun i => shiftIter grp p i t) h))
        · exact (le_not_lt hk_le_m h).elim

/-- Si `m ≤ periodOf`, todas las `shiftIter k t` con `k < m` son distintas,
    luego el cardinal es exactamente `m`. -/
theorem card_periodEnum_le_period (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    ∀ m : ℕ₀, le₀ m (periodOf grp n t ht) →
      HFSet.card (periodEnum grp (σ n) m t) = m
  | .zero, _ => by
      show HFSet.card HFSet.empty = 𝟘
      exact HFSet.card_empty
  | .succ m, hm => by
      have hm_lt : lt₀ m (periodOf grp n t ht) :=
        lt_of_lt_of_le (lt_succ_self m) hm
      have hm_le_p : le₀ m (periodOf grp n t ht) := lt_imp_le _ _ hm_lt
      have hrec : HFSet.card (periodEnum grp (σ n) m t) = m :=
        card_periodEnum_le_period grp n t ht m hm_le_p
      have hnotin : shiftIter grp (σ n) m t ∉ periodEnum grp (σ n) m t := by
        intro hin
        obtain ⟨k, hk, hk_eq⟩ :=
          (mem_periodEnum grp (σ n) m t (shiftIter grp (σ n) m t)).mp hin
        have hk_lt_p : lt₀ k (periodOf grp n t ht) :=
          lt_trans _ _ _ hk hm_lt
        have hkm_eq : m = k :=
          shiftIter_inj_below_period grp n t ht m k hm_lt hk_lt_p hk_eq
        exact (lt_irrefl k) (hkm_eq ▸ hk)
      show HFSet.card (HFSet.insert (shiftIter grp (σ n) m t)
                        (periodEnum grp (σ n) m t)) = σ m
      rw [HFSet.card_insert _ _ hnotin, hrec]

/-- `card (periodEnum (σ n) (periodOf) t) = periodOf`. -/
theorem card_periodEnum_period (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    HFSet.card (periodEnum grp (σ n) (periodOf grp n t ht) t)
      = periodOf grp n t ht :=
  card_periodEnum_le_period grp n t ht (periodOf grp n t ht) (le_refl _)

/-- **Reducción módulo período**: `shiftIter k t = shiftIter (k mod p) t`. -/
theorem shiftIter_eq_mod (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (k : ℕ₀) :
    shiftIter grp (σ n) k t
      = shiftIter grp (σ n) (mod k (periodOf grp n t ht)) t := by
  have hp_ne : periodOf grp n t ht ≠ 𝟘 := periodOf_ne_zero grp n t ht
  have hspec : k = add (mul (div k (periodOf grp n t ht))
                            (periodOf grp n t ht))
                       (mod k (periodOf grp n t ht)) := by
    have := divMod_spec k (periodOf grp n t ht) hp_ne
    show k = add (mul (divMod k (periodOf grp n t ht)).1 (periodOf grp n t ht))
                 (divMod k (periodOf grp n t ht)).2
    exact this
  have hspec' : k = add (mod k (periodOf grp n t ht))
                        (mul (div k (periodOf grp n t ht))
                             (periodOf grp n t ht)) := by
    have hc : add (mul (div k (periodOf grp n t ht)) (periodOf grp n t ht))
                  (mod k (periodOf grp n t ht))
            = add (mod k (periodOf grp n t ht))
                  (mul (div k (periodOf grp n t ht))
                       (periodOf grp n t ht)) := add_comm _ _
    exact hspec.trans hc
  have hsubst : shiftIter grp (σ n) k t
              = shiftIter grp (σ n)
                  (add (mod k (periodOf grp n t ht))
                       (mul (div k (periodOf grp n t ht))
                            (periodOf grp n t ht))) t :=
    congrArg (fun m => shiftIter grp (σ n) m t) hspec'
  have hsplit : shiftIter grp (σ n)
                  (add (mod k (periodOf grp n t ht))
                       (mul (div k (periodOf grp n t ht))
                            (periodOf grp n t ht))) t
              = shiftIter grp (σ n) (mod k (periodOf grp n t ht))
                  (shiftIter grp (σ n)
                    (mul (div k (periodOf grp n t ht))
                         (periodOf grp n t ht)) t) :=
    shiftIter_add grp (σ n) (mod k (periodOf grp n t ht))
      (mul (div k (periodOf grp n t ht)) (periodOf grp n t ht)) t
  have hmul : shiftIter grp (σ n)
                (mul (div k (periodOf grp n t ht))
                     (periodOf grp n t ht)) t = t :=
    shiftIter_mul_periodOf grp n t ht (div k (periodOf grp n t ht))
  rw [hmul] at hsplit
  exact hsubst.trans hsplit

/-- `orbitOf ⊆ periodEnum`. Vía reducción mod período. -/
theorem orbitOf_subset_periodEnum (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    ∀ x : HFSet, x ∈ orbitOf grp n t →
      x ∈ periodEnum grp (σ n) (periodOf grp n t ht) t := by
  intro x hx
  obtain ⟨k, _, hx_eq⟩ := (mem_orbitOf grp n t x).mp hx
  have hp_ne := periodOf_ne_zero grp n t ht
  have hmod_lt : lt₀ (mod k (periodOf grp n t ht)) (periodOf grp n t ht) :=
    mod_lt k (periodOf grp n t ht) hp_ne
  have hxeq : x = shiftIter grp (σ n) (mod k (periodOf grp n t ht)) t := by
    rw [hx_eq]; exact shiftIter_eq_mod grp n t ht k
  exact (mem_periodEnum grp (σ n) (periodOf grp n t ht) t x).mpr
    ⟨mod k (periodOf grp n t ht), hmod_lt, hxeq⟩

/-- `periodEnum ⊆ orbitOf`. Vía `periodOf ≤ σ n`. -/
theorem periodEnum_subset_orbitOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    ∀ x : HFSet, x ∈ periodEnum grp (σ n) (periodOf grp n t ht) t →
      x ∈ orbitOf grp n t := by
  intro x hx
  obtain ⟨k, hk_lt, hx_eq⟩ :=
    (mem_periodEnum grp (σ n) (periodOf grp n t ht) t x).mp hx
  have hp_le : le₀ (periodOf grp n t ht) (σ n) := periodOf_le_succ_n grp n t ht
  have hk_lt_sn : lt₀ k (σ n) := lt_of_lt_of_le hk_lt hp_le
  have hk_le_n : le₀ k n := (le_iff_lt_succ k n).mpr hk_lt_sn
  exact (mem_orbitOf grp n t x).mpr ⟨k, hk_le_n, hx_eq⟩

/-- **Igualdad de conjuntos**: `orbitOf = periodEnum (σ n) periodOf t`. -/
theorem orbitOf_eq_periodEnum (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    orbitOf grp n t = periodEnum grp (σ n) (periodOf grp n t ht) t :=
  HFSet.extensionality _ _ fun x =>
    ⟨orbitOf_subset_periodEnum grp n t ht x,
     periodEnum_subset_orbitOf grp n t ht x⟩

/-- **`card (orbitOf grp n t) = periodOf grp n t`**. -/
theorem card_orbitOf_eq_periodOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    HFSet.card (orbitOf grp n t) = periodOf grp n t ht := by
  rw [orbitOf_eq_periodEnum grp n t ht]
  exact card_periodEnum_period grp n t ht

-- ==================================================================
-- §23. D.4.C parte 5: caso primo — card (orbitOf) ∈ {𝟙, σ n}
-- ==================================================================

/-- **Caso primo**: si `σ n` es primo, entonces `card (orbitOf grp n t) ∈ {𝟙, σ n}`. -/
theorem card_orbitOf_one_or_succ (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hprime : Peano.Arith.Prime (σ n)) :
    HFSet.card (orbitOf grp n t) = 𝟙 ∨
    HFSet.card (orbitOf grp n t) = σ n := by
  rw [card_orbitOf_eq_periodOf grp n t ht]
  exact prime_divisors hprime (periodOf_dvd_succ_n grp n t ht)

-- ==================================================================
-- §24. D.4.D parte 1: card (orbitOf) = 𝟙 ↔ punto fijo
-- ==================================================================

/-- `periodOf grp n t = 𝟙` syss `t` es un punto fijo del shift. -/
theorem periodOf_eq_one_iff_fixed (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    periodOf grp n t ht = 𝟙 ↔ mckayShift grp (σ n) t = t := by
  constructor
  · intro hp
    have hspec := shiftIter_periodOf grp n t ht
    rw [hp] at hspec
    -- shiftIter 𝟙 t = mckayShift (shiftIter 𝟘 t) = mckayShift t
    exact hspec
  · intro hfix
    have h1 : shiftIter grp (σ n) 𝟙 t = t := hfix
    have hmin : le₀ (periodOf grp n t ht) 𝟙 :=
      periodOf_minimal grp n t ht (zero_lt_succ 𝟘) h1
    rcases (le_iff_lt_or_eq _ _).mp hmin with hlt | heq
    · exfalso
      have h0 : periodOf grp n t ht = 𝟘 := lt_b_1_then_b_eq_0 hlt
      exact periodOf_ne_zero grp n t ht h0
    · exact heq

/-- `card (orbitOf grp n t) = 𝟙` syss `t` es un punto fijo del shift. -/
theorem card_orbitOf_eq_one_iff_fixed (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    HFSet.card (orbitOf grp n t) = 𝟙 ↔ mckayShift grp (σ n) t = t := by
  rw [card_orbitOf_eq_periodOf grp n t ht]
  exact periodOf_eq_one_iff_fixed grp n t ht

-- ==================================================================
-- §25. D.4.D parte 2: no fijo ⇒ card (orbitOf) = σ n  (caso primo)
-- ==================================================================

/-- **Caso primo, no fijo**: si `σ n` es primo y `t` no es fijo,
    entonces `card (orbitOf grp n t) = σ n`. -/
theorem card_orbitOf_eq_succ_of_not_fixed (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hprime : Peano.Arith.Prime (σ n))
    (hnf : mckayShift grp (σ n) t ≠ t) :
    HFSet.card (orbitOf grp n t) = σ n := by
  rcases card_orbitOf_one_or_succ grp n t ht hprime with h1 | hp
  · exact absurd ((card_orbitOf_eq_one_iff_fixed grp n t ht).mp h1) hnf
  · exact hp

-- ==================================================================
-- §26. D.4.D parte 3: σ n ∣ card S para S ⊆ carrier shift-cerrado sin fijos
-- ==================================================================

/-- Helper: si `S ⊆ carrier` es cerrado por shift y `t ∈ S`, entonces
    `orbitOf grp n t ⊆ S`. -/
private theorem orbitOf_subset_of_shift_closed (grp : HFGroup) (n : ℕ₀)
    {S : HFSet} {t : HFSet} (htS : t ∈ S)
    (hcl : ∀ x, x ∈ S → mckayShift grp (σ n) x ∈ S) :
    orbitOf grp n t ⊆ S := by
  intro x hx
  obtain ⟨k, hkn, hxk⟩ := (mem_orbitOf grp n t x).mp hx
  rw [hxk]
  clear hx hxk hkn
  induction k with
  | zero => exact htS
  | succ k' ih =>
      show mckayShift grp (σ n) (shiftIter grp (σ n) k' t) ∈ S
      exact hcl _ ih

/-- Helper: `inter S O = O` cuando `O ⊆ S`. -/
private theorem inter_eq_of_subset {S O : HFSet} (hOS : O ⊆ S) :
    HFSet.inter S O = O :=
  HFSet.extensionality _ _ fun x => by
    rw [HFSet.mem_inter]
    exact ⟨fun h => h.2, fun h => ⟨hOS _ h, h⟩⟩

/-- Helper: si `mckayShift x ∈ orbitOf t`, entonces `x ∈ orbitOf t`. -/
private theorem mem_orbitOf_of_shift_mem (grp : HFGroup) (n : ℕ₀)
    {t x : HFSet} (ht : t ∈ HFSet.nPow grp.G (σ n))
    (hx : x ∈ HFSet.nPow grp.G (σ n))
    (h : mckayShift grp (σ n) x ∈ orbitOf grp n t) :
    x ∈ orbitOf grp n t := by
  have h_shift_in_orbit_x : mckayShift grp (σ n) x ∈ orbitOf grp n x := by
    have h1 : shiftIter grp (σ n) (σ 𝟘) x = mckayShift grp (σ n) x := rfl
    rw [← h1]
    exact shiftIter_mem_orbitOf grp n x hx (σ 𝟘)
  have h_orbits_eq : orbitOf grp n x = orbitOf grp n (mckayShift grp (σ n) x) :=
    (orbitOf_eq_of_mem grp n x (mckayShift grp (σ n) x) hx h_shift_in_orbit_x).symm
  have h_orbits_eq2 : orbitOf grp n (mckayShift grp (σ n) x) = orbitOf grp n t :=
    orbitOf_eq_of_mem grp n t (mckayShift grp (σ n) x) ht h
  have hxx : x ∈ orbitOf grp n x :=
    (mem_orbitOf grp n x x).mpr ⟨𝟘, Peano.Order.zero_le n, rfl⟩
  rw [h_orbits_eq, h_orbits_eq2] at hxx
  exact hxx

/-- **§26**: Si `σ n` es primo y `S ⊆ mckayCarrier grp (σ n)` es cerrado por
    shift y disjunto de los puntos fijos, entonces `σ n ∣ card S`. -/
theorem succ_n_dvd_card_of_shift_closed_no_fixed
    (grp : HFGroup) (n : ℕ₀) (hprime : Peano.Arith.Prime (σ n)) :
    ∀ (S : HFSet),
      S ⊆ mckayCarrier grp (σ n) →
      (∀ x, x ∈ S → mckayShift grp (σ n) x ≠ x) →
      (∀ x, x ∈ S → mckayShift grp (σ n) x ∈ S) →
      (σ n) ∣ HFSet.card S := by
  suffices key : ∀ m : ℕ₀, ∀ S : HFSet,
      S ⊆ mckayCarrier grp (σ n) →
      (∀ x, x ∈ S → mckayShift grp (σ n) x ≠ x) →
      (∀ x, x ∈ S → mckayShift grp (σ n) x ∈ S) →
      HFSet.card S = m →
      (σ n) ∣ m by
    intro S hsub hnf hcl
    exact key (HFSet.card S) S hsub hnf hcl rfl
  intro m
  refine Peano.WellFounded.strongInductionOn (P := fun m =>
      ∀ S : HFSet,
        S ⊆ mckayCarrier grp (σ n) →
        (∀ x, x ∈ S → mckayShift grp (σ n) x ≠ x) →
        (∀ x, x ∈ S → mckayShift grp (σ n) x ∈ S) →
        HFSet.card S = m →
        (σ n) ∣ m) m ?_
  intro m IH S hsub hnf hcl hcard
  cases hm : m with
  | zero =>
      exact ⟨𝟘, by rw [mul_zero]⟩
  | succ m' =>
      -- card S = σ m', so S is nonempty
      have hcard_sm' : HFSet.card S = σ m' := by rw [hcard, hm]
      have hSne : S ≠ HFSet.empty := fun heq => by
        rw [heq, HFSet.card_empty] at hcard_sm'
        exact (zero_ne_succ m') hcard_sm'
      -- Extract t ∈ S
      obtain ⟨t, htS⟩ : ∃ t, t ∈ S := HFSet.nonempty_of_ne_empty S hSne
      have ht_carrier : t ∈ mckayCarrier grp (σ n) := hsub _ htS
      have ht_nPow : t ∈ HFSet.nPow grp.G (σ n) :=
        mckayCarrier_subset_nPow grp (σ n) _ ht_carrier
      have ht_notfix : mckayShift grp (σ n) t ≠ t := hnf t htS
      -- card (orbitOf t) = σ n
      have hcardO : HFSet.card (orbitOf grp n t) = σ n :=
        card_orbitOf_eq_succ_of_not_fixed grp n t ht_nPow hprime ht_notfix
      -- orbitOf t ⊆ S
      have hO_sub_S : orbitOf grp n t ⊆ S :=
        orbitOf_subset_of_shift_closed grp n htS hcl
      -- card S = card (orbitOf t) + card (S \ orbitOf t)
      have hpart : HFSet.card S
                 = Peano.Add.add (HFSet.card (orbitOf grp n t))
                                 (HFSet.card (HFSet.setminus S (orbitOf grp n t))) := by
        have := HFSet.card_partition S (orbitOf grp n t)
        rw [inter_eq_of_subset hO_sub_S] at this
        exact this
      -- S' ⊆ carrier (where S' = S \ orbitOf t)
      have hsub' : HFSet.setminus S (orbitOf grp n t) ⊆ mckayCarrier grp (σ n) :=
        fun x hx => by
          rw [HFSet.mem_setminus] at hx
          exact hsub _ hx.1
      -- No fixed points in S'
      have hnf' : ∀ x, x ∈ HFSet.setminus S (orbitOf grp n t) →
                       mckayShift grp (σ n) x ≠ x := fun x hx => by
        rw [HFSet.mem_setminus] at hx
        exact hnf x hx.1
      -- S' shift-closed
      have hcl' : ∀ x, x ∈ HFSet.setminus S (orbitOf grp n t) →
                       mckayShift grp (σ n) x ∈ HFSet.setminus S (orbitOf grp n t) := by
        intro x hx
        rw [HFSet.mem_setminus] at hx
        obtain ⟨hxS, hxnO⟩ := hx
        refine (HFSet.mem_setminus _ _ _).mpr ⟨hcl x hxS, ?_⟩
        intro hshift_O
        have hx_nPow : x ∈ HFSet.nPow grp.G (σ n) :=
          mckayCarrier_subset_nPow grp (σ n) _ (hsub _ hxS)
        exact hxnO (mem_orbitOf_of_shift_mem grp n ht_nPow hx_nPow hshift_O)
      -- card S' < m
      have hcard_S'_lt :
          lt₀ (HFSet.card (HFSet.setminus S (orbitOf grp n t))) m := by
        rw [← hcard, hpart, hcardO]
        exact Peano.Add.lt_self_add_l
          (HFSet.card (HFSet.setminus S (orbitOf grp n t))) (σ n) (zero_ne_succ n).symm
      -- IH gives σ n ∣ card S'
      have hp_dvd_S' : (σ n) ∣ HFSet.card (HFSet.setminus S (orbitOf grp n t)) :=
        IH _ hcard_S'_lt _ hsub' hnf' hcl' rfl
      -- Combine
      have hp_dvd_sn : (σ n) ∣ σ n := divides_refl (σ n)
      have hp_dvd_sum :
          (σ n) ∣ Peano.Add.add (σ n)
                    (HFSet.card (HFSet.setminus S (orbitOf grp n t))) :=
        divides_add hp_dvd_sn hp_dvd_S'
      have hcard_eq : HFSet.card S
                    = Peano.Add.add (σ n)
                        (HFSet.card (HFSet.setminus S (orbitOf grp n t))) := by
        rw [hpart, hcardO]
      -- Goal: σ n ∣ σ m'.  σ m' = m = card S = σ n + ...
      have hgoal_eq : σ m' = Peano.Add.add (σ n)
                              (HFSet.card (HFSet.setminus S (orbitOf grp n t))) := by
        rw [← hm, ← hcard, hcard_eq]
      rw [hgoal_eq]
      exact hp_dvd_sum

-- ==================================================================
-- §27. D.4.D conclusión: σ n ∣ card (mckayFixedPoints)
-- ==================================================================

/-- **D.4.D / Lema de McKay**: si `σ n` es primo y `σ n ∣ card grp.G`, con `n ≠ 𝟘`,
    entonces `σ n ∣ card (mckayFixedPoints grp (σ n))`. -/
theorem succ_n_dvd_card_mckayFixedPoints
    (grp : HFGroup) (n : ℕ₀) (hprime : Peano.Arith.Prime (σ n))
    (hdvd : (σ n) ∣ HFSet.card grp.G) (hn : n ≠ 𝟘) :
    (σ n) ∣ HFSet.card (mckayFixedPoints grp (σ n)) := by
  -- p ∣ card C  (D.3)
  have hp_dvd_C : (σ n) ∣ HFSet.card (mckayCarrier grp (σ n)) :=
    dvd_card_mckayCarrier_succ grp (σ n) hdvd hn
  -- S = C \ F.  S ⊆ C, S shift-closed, S no fixed
  have hS_sub_C :
      HFSet.setminus (mckayCarrier grp (σ n)) (mckayFixedPoints grp (σ n)) ⊆
        mckayCarrier grp (σ n) := fun x hx => by
    rw [HFSet.mem_setminus] at hx; exact hx.1
  have hS_no_fix : ∀ x,
      x ∈ HFSet.setminus (mckayCarrier grp (σ n)) (mckayFixedPoints grp (σ n)) →
        mckayShift grp (σ n) x ≠ x := by
    intro x hx
    rw [HFSet.mem_setminus] at hx
    obtain ⟨hxC, hxnF⟩ := hx
    intro heq
    exact hxnF ((mem_mckayFixedPoints grp (σ n) x).mpr ⟨hxC, heq⟩)
  have hS_cl : ∀ x,
      x ∈ HFSet.setminus (mckayCarrier grp (σ n)) (mckayFixedPoints grp (σ n)) →
        mckayShift grp (σ n) x ∈
          HFSet.setminus (mckayCarrier grp (σ n)) (mckayFixedPoints grp (σ n)) := by
    intro x hx
    rw [HFSet.mem_setminus] at hx
    obtain ⟨hxC, hxnF⟩ := hx
    refine (HFSet.mem_setminus _ _ _).mpr
      ⟨mckayShift_mem_mckayCarrier grp (σ n) hxC, ?_⟩
    intro hshift_F
    -- mckayShift x ∈ F ⇒ x fixed (via equality of orbits)
    have hx_nPow : x ∈ HFSet.nPow grp.G (σ n) :=
      mckayCarrier_subset_nPow grp (σ n) _ hxC
    have hshift_in_orbit_x : mckayShift grp (σ n) x ∈ orbitOf grp n x := by
      have h1 : shiftIter grp (σ n) (σ 𝟘) x = mckayShift grp (σ n) x := rfl
      rw [← h1]
      exact shiftIter_mem_orbitOf grp n x hx_nPow (σ 𝟘)
    have horb_eq :
        orbitOf grp n x = orbitOf grp n (mckayShift grp (σ n) x) :=
      (orbitOf_eq_of_mem grp n x (mckayShift grp (σ n) x) hx_nPow hshift_in_orbit_x).symm
    have hshift_nPow : mckayShift grp (σ n) x ∈ HFSet.nPow grp.G (σ n) :=
      mckayCarrier_subset_nPow grp (σ n) _
        (mckayShift_mem_mckayCarrier grp (σ n) hxC)
    have hshift_fixed : mckayShift grp (σ n) (mckayShift grp (σ n) x) =
        mckayShift grp (σ n) x :=
      ((mem_mckayFixedPoints grp (σ n) _).mp hshift_F).2
    have h_card_orbit_shift_one :
        HFSet.card (orbitOf grp n (mckayShift grp (σ n) x)) = 𝟙 :=
      (card_orbitOf_eq_one_iff_fixed grp n
        (mckayShift grp (σ n) x) hshift_nPow).mpr hshift_fixed
    have h_card_orbit_x_one : HFSet.card (orbitOf grp n x) = 𝟙 := by
      rw [horb_eq]; exact h_card_orbit_shift_one
    have hx_fixed : mckayShift grp (σ n) x = x :=
      (card_orbitOf_eq_one_iff_fixed grp n x hx_nPow).mp h_card_orbit_x_one
    exact hxnF ((mem_mckayFixedPoints grp (σ n) x).mpr ⟨hxC, hx_fixed⟩)
  -- p ∣ card S  (§26)
  have hp_dvd_S : (σ n) ∣
      HFSet.card (HFSet.setminus (mckayCarrier grp (σ n)) (mckayFixedPoints grp (σ n))) :=
    succ_n_dvd_card_of_shift_closed_no_fixed grp n hprime _ hS_sub_C hS_no_fix hS_cl
  -- F ⊆ C, so inter C F = F, hence card C = card F + card S
  have hF_sub_C : mckayFixedPoints grp (σ n) ⊆ mckayCarrier grp (σ n) :=
    mckayFixedPoints_subset grp (σ n)
  have hinter :
      HFSet.inter (mckayCarrier grp (σ n)) (mckayFixedPoints grp (σ n)) =
        mckayFixedPoints grp (σ n) := inter_eq_of_subset hF_sub_C
  have hpart : HFSet.card (mckayCarrier grp (σ n))
             = Peano.Add.add (HFSet.card (mckayFixedPoints grp (σ n)))
                 (HFSet.card
                   (HFSet.setminus (mckayCarrier grp (σ n))
                     (mckayFixedPoints grp (σ n)))) := by
    have := HFSet.card_partition (mckayCarrier grp (σ n)) (mckayFixedPoints grp (σ n))
    rw [hinter] at this
    exact this
  -- Case split: card S < card C  or  card S = card C
  rcases (Peano.Order.le_iff_lt_or_eq _ _).mp
      (HFSet.card_setminus_le (mckayCarrier grp (σ n)) (mckayFixedPoints grp (σ n)))
      with hlt | heq
  · -- Strict
    have hp_dvd_diff : (σ n) ∣
        Peano.Sub.sub (HFSet.card (mckayCarrier grp (σ n)))
          (HFSet.card
            (HFSet.setminus (mckayCarrier grp (σ n))
              (mckayFixedPoints grp (σ n)))) :=
      divides_sub hlt hp_dvd_C hp_dvd_S
    have hsub_eq :
        Peano.Sub.sub (HFSet.card (mckayCarrier grp (σ n)))
          (HFSet.card
            (HFSet.setminus (mckayCarrier grp (σ n))
              (mckayFixedPoints grp (σ n))))
        = HFSet.card (mckayFixedPoints grp (σ n)) := by
      rw [hpart]
      have hle :
          le₀ (HFSet.card
                (HFSet.setminus (mckayCarrier grp (σ n))
                  (mckayFixedPoints grp (σ n))))
              (HFSet.card
                (HFSet.setminus (mckayCarrier grp (σ n))
                  (mckayFixedPoints grp (σ n)))) := Or.inr rfl
      have h1 :
          Peano.Add.add
            (Peano.Sub.sub
              (HFSet.card
                (HFSet.setminus (mckayCarrier grp (σ n))
                  (mckayFixedPoints grp (σ n))))
              (HFSet.card
                (HFSet.setminus (mckayCarrier grp (σ n))
                  (mckayFixedPoints grp (σ n)))))
            (HFSet.card (mckayFixedPoints grp (σ n)))
          = Peano.Sub.sub
              (Peano.Add.add
                (HFSet.card
                  (HFSet.setminus (mckayCarrier grp (σ n))
                    (mckayFixedPoints grp (σ n))))
                (HFSet.card (mckayFixedPoints grp (σ n))))
              (HFSet.card
                (HFSet.setminus (mckayCarrier grp (σ n))
                  (mckayFixedPoints grp (σ n)))) :=
        Peano.Sub.add_sub_assoc _ _ _ hle
      rw [Peano.Sub.sub_self, Peano.Add.zero_add] at h1
      rw [Peano.Add.add_comm (HFSet.card (mckayFixedPoints grp (σ n))) _]
      exact h1.symm
    rw [← hsub_eq]
    exact hp_dvd_diff
  · -- card S = card C  ⇒ card F = 𝟘
    have hF_zero : HFSet.card (mckayFixedPoints grp (σ n)) = 𝟘 := by
      have heq2 :
          Peano.Add.add (HFSet.card (mckayFixedPoints grp (σ n)))
            (HFSet.card
              (HFSet.setminus (mckayCarrier grp (σ n))
                (mckayFixedPoints grp (σ n))))
          = HFSet.card
              (HFSet.setminus (mckayCarrier grp (σ n))
                (mckayFixedPoints grp (σ n))) := by
        rw [← hpart]; exact heq.symm
      have hcancel :
          Peano.Add.add (HFSet.card (mckayFixedPoints grp (σ n)))
            (HFSet.card
              (HFSet.setminus (mckayCarrier grp (σ n))
                (mckayFixedPoints grp (σ n))))
          = Peano.Add.add 𝟘
              (HFSet.card
                (HFSet.setminus (mckayCarrier grp (σ n))
                  (mckayFixedPoints grp (σ n)))) := by
        rw [Peano.Add.zero_add]; exact heq2
      exact Peano.Add.cancelation_add _ _ _ hcancel
    rw [hF_zero]
    exact ⟨𝟘, by rw [mul_zero]⟩

-- ==================================================================
-- §29. Infraestructura: puntos fijos del shift y producto de tupla
-- ==================================================================

-- Expande mckayShift grp (σ (σ m)) ⟪a, b⟫ como par ordenado.
private theorem mckayShift_succ_pair (grp : HFGroup) (m : ℕ₀) (a b : HFSet) :
    mckayShift grp (σ (σ m)) ⟪a, b⟫ = ⟪⟪dropHead m a, b⟫, getHead m a⟫ := by
  show ⟪dropHead (σ m) ⟪a, b⟫, getHead (σ m) ⟪a, b⟫⟫
      = ⟪⟪dropHead m a, b⟫, getHead m a⟫
  have h1 : dropHead (σ m) ⟪a, b⟫ = ⟪dropHead m a, b⟫ := by
    show ⟪dropHead m (HFSet.fst ⟪a, b⟫), HFSet.snd ⟪a, b⟫⟫ = ⟪dropHead m a, b⟫
    rw [HFSet.fst_orderedPair_eq', HFSet.snd_orderedPair_eq']
  have h2 : getHead (σ m) ⟪a, b⟫ = getHead m a := by
    show getHead m (HFSet.fst ⟪a, b⟫) = getHead m a
    rw [HFSet.fst_orderedPair_eq']
  rw [h1, h2]

-- Si mckayShift fija t y snd(t)=e, entonces t = eTuple.
private theorem shift_fixed_snd_e_implies_eTuple (grp : HFGroup) :
    ∀ (n : ℕ₀) {t : HFSet},
      t ∈ HFSet.nPow grp.G (σ n) →
      mckayShift grp (σ n) t = t →
      HFSet.snd t = grp.e →
      t = eTuple grp (σ n)
  | .zero, t, ht, _, hsnd => by
      rw [HFSet.nPow_succ, HFSet.nPow_zero] at ht
      obtain ⟨a, b, ha, _hb, heq⟩ := (HFSet.mem_cartProd _ _ _).mp ht
      have ha_e : a = HFSet.empty := (HFSet.mem_singleton _ _).mp ha
      rw [heq, HFSet.snd_orderedPair_eq'] at hsnd
      rw [heq, ha_e, hsnd]; rfl
  | .succ m, t, ht, hfix, hsnd => by
      rw [HFSet.nPow_succ] at ht
      obtain ⟨a, b, ha, _hb, heq⟩ := (HFSet.mem_cartProd _ _ _).mp ht
      have hb_e : b = grp.e := by
        rw [heq, HFSet.snd_orderedPair_eq'] at hsnd; exact hsnd
      have hfix_t : (⟪⟪dropHead m a, b⟫, getHead m a⟫ : HFSet) = ⟪a, b⟫ := by
        rw [heq] at hfix; rw [← mckayShift_succ_pair]; exact hfix
      have hpair := (HFSet.orderedPair_eq_iff _ _ _ _).mp hfix_t
      have ha_eq : ⟪dropHead m a, b⟫ = a := hpair.1
      have hsnd_a : HFSet.snd a = grp.e := by
        have : HFSet.snd ⟪dropHead m a, b⟫ = HFSet.snd a := congrArg HFSet.snd ha_eq
        rw [HFSet.snd_orderedPair_eq'] at this
        exact hb_e ▸ this.symm
      have hfix_a : mckayShift grp (σ m) a = a := by
        show (⟪dropHead m a, getHead m a⟫ : HFSet) = a
        rw [hpair.2]; exact ha_eq
      have ha_et : a = eTuple grp (σ m) :=
        shift_fixed_snd_e_implies_eTuple grp m ha hfix_a hsnd_a
      rw [heq, ha_et, hb_e]; rfl

-- Si mckayShift fija t, entonces tupleProd(t) = gpow(snd t, σ n).
private theorem shift_fixed_tupleProd_eq_gpow (grp : HFGroup) :
    ∀ (n : ℕ₀) {t : HFSet},
      t ∈ HFSet.nPow grp.G (σ n) →
      mckayShift grp (σ n) t = t →
      tupleProd grp (σ n) t = gpow grp (HFSet.snd t) (σ n)
  | .zero, t, ht, _ => by
      rw [HFSet.nPow_succ, HFSet.nPow_zero] at ht
      obtain ⟨_a, b, _ha, hb, heq⟩ := (HFSet.mem_cartProd _ _ _).mp ht
      rw [heq, tupleProd_pair, tupleProd_zero, grp.op_id_left hb,
          HFSet.snd_orderedPair_eq', gpow_succ, gpow_zero, grp.op_id_left hb]
  | .succ m, t, ht, hfix => by
      rw [HFSet.nPow_succ] at ht
      obtain ⟨a, b, ha, _hb, heq⟩ := (HFSet.mem_cartProd _ _ _).mp ht
      have hfix_t : (⟪⟪dropHead m a, b⟫, getHead m a⟫ : HFSet) = ⟪a, b⟫ := by
        rw [heq] at hfix; rw [← mckayShift_succ_pair]; exact hfix
      have hpair := (HFSet.orderedPair_eq_iff _ _ _ _).mp hfix_t
      have ha_eq : ⟪dropHead m a, b⟫ = a := hpair.1
      have hsnd_a : HFSet.snd a = b := by
        have : HFSet.snd ⟪dropHead m a, b⟫ = HFSet.snd a := congrArg HFSet.snd ha_eq
        rw [HFSet.snd_orderedPair_eq'] at this; exact this.symm
      have hfix_a : mckayShift grp (σ m) a = a := by
        show (⟪dropHead m a, getHead m a⟫ : HFSet) = a
        rw [hpair.2]; exact ha_eq
      have ih := shift_fixed_tupleProd_eq_gpow grp m ha hfix_a
      rw [hsnd_a] at ih
      rw [heq, tupleProd_pair, ih, HFSet.snd_orderedPair_eq', ← gpow_succ]

-- ==================================================================
-- §30. El orden divide cualquier potencia que dé e;
--      si la potencia es prima, el orden es exactamente esa prima.
-- ==================================================================

/-- Si `g^m = e`, entonces `order g ∣ m`. -/
theorem order_dvd_of_gpow_eq_id (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    (m : ℕ₀) (hm : gpow grp g m = grp.e) : order grp hg ∣ m := by
  have hord_ne := order_ne_zero grp hg
  have hmod_eq : gpow grp g (mod m (order grp hg)) = grp.e :=
    (gpow_mod_order grp hg m).symm.trans hm
  have hmod_zero : mod m (order grp hg) = 𝟘 := by
    rcases trichotomy (mod m (order grp hg)) 𝟘 with h | h | h
    · exact (nlt_n_0 _ h).elim
    · exact h
    · exact absurd (mod_lt m _ hord_ne)
        (le_not_lt (order_minimal grp hg h hmod_eq))
  have hdec : m = add (mul (div m (order grp hg)) (order grp hg)) (mod m (order grp hg)) :=
    divMod_spec m (order grp hg) hord_ne
  rw [hmod_zero, add_zero] at hdec
  exact ⟨div m (order grp hg), by rw [mul_comm]; exact hdec⟩

/-- Si `g^(σ n) = e`, `σ n` es primo y `g ≠ e`, entonces `order g = σ n`. -/
theorem order_eq_prime_of_pow (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    {n : ℕ₀} (hp : Peano.Arith.Prime (σ n)) (hg_ne : g ≠ grp.e)
    (hpow : gpow grp g (σ n) = grp.e) : order grp hg = σ n := by
  have hdvd : order grp hg ∣ σ n := order_dvd_of_gpow_eq_id grp hg (σ n) hpow
  rcases prime_divisors hp hdvd with hord1 | hord_eq
  · have : gpow grp g 𝟙 = grp.e := hord1 ▸ gpow_order_eq_id grp hg
    exact absurd (gpow_one grp hg ▸ this) hg_ne
  · exact hord_eq

-- ==================================================================
-- §31. Injectividad de gpow bajo el orden; cardinalidad del
--      subgrupo cíclico = order.
-- ==================================================================

private theorem gpow_inj_below_order (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    {i j : ℕ₀} (hi : lt₀ i (order grp hg)) (hj : lt₀ j (order grp hg))
    (heq : gpow grp g i = gpow grp g j) : i = j := by
  rcases trichotomy i j with hij | hij | hij
  · exfalso
    -- i < j: sub j i > 0 y gpow(sub j i)=e, contradiciendo la minimalidad
    have hpos : lt₀ 𝟘 (Peano.Sub.sub j i) := by
      rcases trichotomy (Peano.Sub.sub j i) 𝟘 with h | h | h
      · exact (nlt_n_0 _ h).elim
      · have := sub_k_add_k j i (lt_imp_le _ _ hij)
        rw [h, zero_add] at this
        exact absurd this (ne_of_lt _ _ hij)
      · exact h
    have hle : le₀ (Peano.Sub.sub j i) (order grp hg) :=
      le_trans _ j _ (sub_le_self j i) (lt_imp_le _ _ hj)
    have hne : Peano.Sub.sub j i ≠ order grp hg := fun h =>
      absurd hj (nlt_of_le (h ▸ sub_le_self j i))
    have hlt : lt₀ (Peano.Sub.sub j i) (order grp hg) :=
      lt_of_le_neq_wp hle hne
    exact absurd hlt
      (le_not_lt (order_minimal grp hg hpos (gpow_sub_eq_id grp hg hij heq.symm)))
  · exact hij
  · exfalso
    -- j < i: sub i j > 0 y gpow(sub i j)=e, contradiciendo la minimalidad
    have hpos : lt₀ 𝟘 (Peano.Sub.sub i j) := by
      rcases trichotomy (Peano.Sub.sub i j) 𝟘 with h | h | h
      · exact (nlt_n_0 _ h).elim
      · have := sub_k_add_k i j (lt_imp_le _ _ hij)
        rw [h, zero_add] at this
        exact absurd this (ne_of_lt _ _ hij)
      · exact h
    have hle : le₀ (Peano.Sub.sub i j) (order grp hg) :=
      le_trans _ i _ (sub_le_self i j) (lt_imp_le _ _ hi)
    have hne : Peano.Sub.sub i j ≠ order grp hg := fun h =>
      absurd hi (nlt_of_le (h ▸ sub_le_self i j))
    have hlt : lt₀ (Peano.Sub.sub i j) (order grp hg) :=
      lt_of_le_neq_wp hle hne
    exact absurd hlt
      (le_not_lt (order_minimal grp hg hpos (gpow_sub_eq_id grp hg hij heq)))

-- card(gpowImg grp g m) = σ m cuando m < order.
private theorem gpowImg_card_eq (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    ∀ {m : ℕ₀}, lt₀ m (order grp hg) → HFSet.card (gpowImg grp g m) = σ m
  | .zero, _ => by
      show HFSet.card (HFSet.singleton (gpow grp g (𝟘 : ℕ₀))) = σ 𝟘
      have heq : HFSet.singleton (gpow grp g (𝟘 : ℕ₀)) =
                  HFSet.insert (gpow grp g (𝟘 : ℕ₀)) HFSet.empty :=
        HFSet.extensionality _ _ fun z => by
          rw [HFSet.mem_singleton, HFSet.mem_insert]
          exact ⟨Or.inl, fun h => h.elim id (absurd · (HFSet.not_mem_empty z))⟩
      rw [heq, HFSet.card_insert _ _ (HFSet.not_mem_empty _), HFSet.card_empty]
  | .succ m', hm => by
      have hm'_lt : lt₀ m' (order grp hg) :=
        lt_trans _ (σ m') _ (lt_succ_self m') hm
      have ih := gpowImg_card_eq grp hg hm'_lt
      have hnotin : gpow grp g (σ m') ∉ gpowImg grp g m' := by
        intro hmem
        obtain ⟨i, hi_le, hi_eq⟩ := (mem_gpowImg grp g m' _).mp hmem
        have hile_sm : le₀ i (σ m') :=
          le_trans _ m' _ hi_le (lt_imp_le _ _ (lt_succ_self m'))
        have hi_lt : lt₀ i (order grp hg) := by
          rcases trichotomy i (σ m') with h | h | h
          · exact lt_trans _ (σ m') _ h hm
          · rw [h]; exact hm
          · exact absurd h (nlt_of_le hile_sm)
        have heq_idx : σ m' = i :=
          gpow_inj_below_order grp hg hm hi_lt hi_eq
        exact absurd (heq_idx.symm ▸ hi_le) (nle_σn_n m')
      rw [show HFSet.card (gpowImg grp g (σ m')) =
                σ (HFSet.card (gpowImg grp g m')) from
              HFSet.card_insert _ _ hnotin,
          ih]

/-- La cardinalidad del subgrupo cíclico ⟨g⟩ es `order g`. -/
theorem cyclicCarrier_card_eq_order (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    HFSet.card (cyclicCarrier grp hg) = order grp hg := by
  show HFSet.card (gpowImg grp g (order grp hg)) = order grp hg
  cases h_ord : order grp hg with
  | zero => exact (order_ne_zero grp hg h_ord).elim
  | succ m =>
    have hm_lt : lt₀ m (order grp hg) := by rw [h_ord]; exact lt_succ_self m
    have hcard_m : HFSet.card (gpowImg grp g m) = σ m := gpowImg_card_eq grp hg hm_lt
    have he_mem : gpow grp g (σ m) ∈ gpowImg grp g m := by
      have hpow_e : gpow grp g (σ m) = grp.e := h_ord ▸ gpow_order_eq_id grp hg
      rw [hpow_e, ← gpow_zero grp g]
      exact (mem_gpowImg grp g m _).mpr ⟨𝟘, zero_le m, rfl⟩
    have hins_eq : gpowImg grp g (σ m) = gpowImg grp g m :=
      HFSet.extensionality _ _ fun x => by
        rw [show gpowImg grp g (σ m) =
              HFSet.insert (gpow grp g (σ m)) (gpowImg grp g m) from rfl,
            HFSet.mem_insert]
        exact ⟨fun h => h.elim (· ▸ he_mem) id, Or.inr⟩
    rw [hins_eq, hcard_m]

-- ==================================================================
-- §32. Teorema de Cauchy (vía McKay)
-- ==================================================================

/-- **Teorema de Cauchy** (vía el argumento de McKay):
    si `p` es primo y `p ∣ |G|`, existe un subgrupo de orden `p`. -/
theorem cauchy_minimal (grp : HFGroup) {n : ℕ₀} (hp : Peano.Arith.Prime (σ n))
    (hdvd : σ n ∣ HFSet.card grp.G) :
    ∃ sub : HFSubgroup grp, HFSet.card sub.H = σ n := by
  -- n ≠ 0, pues σ 0 = 1 no es primo
  have hn : n ≠ 𝟘 := by
    intro h; subst h
    exact absurd (prime_ge_two hp) (nle_σn_n 𝟙)
  -- Lema McKay: σ n ∣ |F|
  have hF_dvd : σ n ∣ HFSet.card (mckayFixedPoints grp (σ n)) :=
    succ_n_dvd_card_mckayFixedPoints grp n hp hdvd hn
  have hF_eTuple : eTuple grp (σ n) ∈ mckayFixedPoints grp (σ n) :=
    eTuple_mem_mckayFixedPoints grp (σ n)
  have hF_ne : mckayFixedPoints grp (σ n) ≠ HFSet.empty := fun h =>
    absurd (h ▸ hF_eTuple) (HFSet.not_mem_empty _)
  have hcard_F_ne : HFSet.card (mckayFixedPoints grp (σ n)) ≠ 𝟘 := fun h =>
    hF_ne (HFSet.card_eq_zero_iff.mp h)
  obtain ⟨k, hcard_F_eq⟩ := hF_dvd
  have hk_ne : k ≠ 𝟘 := fun hk0 =>
    hcard_F_ne (by rw [hcard_F_eq, hk0, mul_zero])
  have hcard_ge : le₀ (σ n) (HFSet.card (mckayFixedPoints grp (σ n))) := by
    rw [hcard_F_eq]; exact mul_le_right (σ n) k hk_ne
  have hcard_ge2 : le₀ 𝟚 (HFSet.card (mckayFixedPoints grp (σ n))) :=
    le_trans _ (σ n) _ (prime_ge_two hp) hcard_ge
  -- Existe t ∈ F con t ≠ eTuple (si no, |F| ≤ 1 < 2, contradicción)
  have hexists_ne : ∃ t ∈ mckayFixedPoints grp (σ n), t ≠ eTuple grp (σ n) :=
    Classical.byContradiction fun h_none => by
      have hall : ∀ t, t ∈ mckayFixedPoints grp (σ n) → t = eTuple grp (σ n) :=
        fun t ht => Classical.byContradiction fun ht_ne => h_none ⟨t, ht, ht_ne⟩
      have hF_sub : mckayFixedPoints grp (σ n) ⊆ HFSet.singleton (eTuple grp (σ n)) :=
        fun x hx => (HFSet.mem_singleton _ _).mpr (hall x hx)
      have hcard_sing : HFSet.card (HFSet.singleton (eTuple grp (σ n))) = 𝟙 := by
        have heq : HFSet.singleton (eTuple grp (σ n)) =
                    HFSet.insert (eTuple grp (σ n)) HFSet.empty :=
          HFSet.extensionality _ _ fun z => by
            rw [HFSet.mem_singleton, HFSet.mem_insert]
            exact ⟨Or.inl, fun h => h.elim id (absurd · (HFSet.not_mem_empty z))⟩
        rw [heq, HFSet.card_insert _ _ (HFSet.not_mem_empty _), HFSet.card_empty]; rfl
      have hcard_le : le₀ (HFSet.card (mckayFixedPoints grp (σ n))) 𝟙 :=
        hcard_sing ▸ HFSet.card_le_of_subset hF_sub
      exact absurd (le_trans _ _ _ hcard_ge2 hcard_le) (nle_σn_n 𝟙)
  obtain ⟨t, ht_F, ht_ne⟩ := hexists_ne
  have ht_car : t ∈ mckayCarrier grp (σ n) := mckayFixedPoints_subset grp (σ n) t ht_F
  have ht_nPow : t ∈ HFSet.nPow grp.G (σ n) :=
    mckayCarrier_subset_nPow grp (σ n) t ht_car
  have hshift_t : mckayShift grp (σ n) t = t :=
    ((mem_mckayFixedPoints grp (σ n) t).mp ht_F).2
  have htprod : tupleProd grp (σ n) t = grp.e :=
    ((mem_mckayCarrier grp (σ n) t).mp ht_car).2
  have hg : HFSet.snd t ∈ grp.G := snd_mem_of_mem_nPow grp.G n ht_nPow
  have hg_ne : HFSet.snd t ≠ grp.e := fun hge =>
    ht_ne (shift_fixed_snd_e_implies_eTuple grp n ht_nPow hshift_t hge)
  have hpow_eq : tupleProd grp (σ n) t = gpow grp (HFSet.snd t) (σ n) :=
    shift_fixed_tupleProd_eq_gpow grp n ht_nPow hshift_t
  have hpow : gpow grp (HFSet.snd t) (σ n) = grp.e := hpow_eq.symm.trans htprod
  have hord : order grp hg = σ n :=
    order_eq_prime_of_pow grp hg hp hg_ne hpow
  exact ⟨cyclicSubgroup grp hg,
         hord ▸ cyclicCarrier_card_eq_order grp hg⟩


-- ==================================================================
-- §33. Infraestructura para Sylow I: subgrupos auxiliares y preimagen
-- ==================================================================

/-- El grupo `grp` mismo, visto como subgrupo impropio. -/
def improperSubgroup (grp : HFGroup) : HFSubgroup grp where
  H          := grp.G
  H_sub      := id
  e_mem      := grp.e_mem
  op_closed  := grp.op_closed
  inv_closed := grp.inv_closed

theorem improperSubgroup_card (grp : HFGroup) :
    HFSet.card (improperSubgroup grp).H = HFSet.card grp.G := rfl

/-- Embed un sub-subgrupo `sub₂ ≤ sub₁.toHFGroup` de vuelta en `grp`. -/
def subgroupOfSubgroup {grp : HFGroup} (sub₁ : HFSubgroup grp)
    (sub₂ : HFSubgroup sub₁.toHFGroup) : HFSubgroup grp where
  H          := sub₂.H
  H_sub      := fun hx => sub₁.H_sub (sub₂.H_sub hx)
  e_mem      := sub₂.e_mem
  op_closed  := sub₂.op_closed
  inv_closed := sub₂.inv_closed

-- ==================================================================
-- §34. Cardinalidad de la preimagen bajo el cociente
-- ==================================================================

open HFSet in
/-- La preimagen de `Q ≤ G/N` bajo `π` tiene card = card(Q) · card(N). -/
theorem card_preimage_mul {grp : HFGroup}
    (sub_N : HFSubgroup grp) (hn_N : sub_N.isNormal)
    (Q : HFSubgroup (quotientGroup grp sub_N hn_N)) :
    HFSet.card (HFSubgroup.preimageSubgroup sub_N hn_N Q).H =
      mul (HFSet.card Q.H) (HFSet.card sub_N.H) := by
  -- Paso 1: preimage.H = sUnion Q.H
  have hpreimage_eq :
      (HFSubgroup.preimageSubgroup sub_N hn_N Q).H = sUnion Q.H := by
    apply extensionality; intro x
    rw [HFSubgroup.mem_preimageSubgroup_iff, mem_sUnion]
    constructor
    · rintro ⟨hxG, hcoset_mem⟩
      exact ⟨sub_N.rightCoset x, hcoset_mem, sub_N.rightCoset_self_mem hxG⟩
    · rintro ⟨C, hCQ, hxC⟩
      have hC_cosets : C ∈ sub_N.cosets :=
        Q.H_sub hCQ
      obtain ⟨a, haG, rfl⟩ := HFSubgroup.mem_cosets.mp hC_cosets
      have hmem_ra : x ∈ sub_N.rightCoset a :=
        hxC
      have hxG : x ∈ grp.G := by
        rw [HFSubgroup.mem_rightCoset _ haG] at hmem_ra
        obtain ⟨h, hh, rfl⟩ := hmem_ra
        exact grp.op_closed (sub_N.H_sub hh) haG
      refine ⟨hxG, ?_⟩
      -- rightCoset x = rightCoset a  (since x ∈ rightCoset a)
      have hcosetEq : sub_N.cosetEq a x := by
        rw [HFSubgroup.mem_rightCoset _ haG] at hmem_ra
        obtain ⟨h, hh, rfl⟩ := hmem_ra
        show grp.op (grp.op h a) (grp.inv a) ∈ sub_N.H
        rw [grp.op_assoc (sub_N.H_sub hh) haG (grp.inv_closed haG),
            grp.op_inv_right haG, grp.op_id_right (sub_N.H_sub hh)]
        exact hh
      rw [← (sub_N.cosetEq_iff_rightCoset_eq haG hxG).mp hcosetEq]
      exact hCQ
  -- Paso 2: Q.H es pairwise disjunta y uniforme
  have hQ_sub_cosets : ∀ C, C ∈ Q.H → C ∈ sub_N.cosets := fun C hC => Q.H_sub hC
  have hQ_unif : ∀ C, C ∈ Q.H → card C = card sub_N.H := fun C hC =>
    sub_N.coset_card_eq (hQ_sub_cosets C hC)
  have hQ_disj : ∀ C D, C ∈ Q.H → D ∈ Q.H → C ≠ D → inter C D = empty :=
    fun C D hC hD hCD =>
      sub_N.cosets_pairwise_disjoint (hQ_sub_cosets C hC) (hQ_sub_cosets D hD) hCD
  -- Paso 3: card(sUnion Q.H) = card(Q.H) * card(sub_N.H)
  rw [hpreimage_eq]
  exact card_sUnion_uniform_partition Q.H (card sub_N.H) hQ_unif hQ_disj

-- ==================================================================
-- §35. Lemas aritméticos sobre primos y potencias
-- ==================================================================

-- Si d | p^k y d ≠ 1, entonces p | d (p primo).
private theorem prime_dvd_of_dvd_prime_pow {p : ℕ₀} (hp : Peano.Arith.Prime p)
    (k : ℕ₀) {d : ℕ₀} (hd_pow : d ∣ p ^ k) (hd1 : d ≠ 𝟙) : p ∣ d := by
  induction k with
  | zero =>
    -- p ^ 𝟘 = 𝟙 por rfl a través del puente HPow/Peano.Pow
    exact absurd (antisymm_divides hd_pow (one_divides d)) hd1
  | succ k' ih =>
    have hps : p ^ σ k' = mul (p ^ k') p := by rw [pow_def]; exact Peano.Pow.pow_succ p k'
    rw [hps, mul_comm] at hd_pow
    rcases prime_coprime_or_dvd hp (n := d) with hdvd | hcop
    · exact hdvd
    · exact ih (coprime_dvd_of_dvd_mul (coprime_symm hcop) hd_pow)

-- ==================================================================
-- §36. Órbitas no centrales bajo la acción de conjugación
-- ==================================================================

/-- Un elemento en la órbita de un elemento no central sigue siendo no central. -/
private theorem noncentral_of_orb_noncentral {grp : HFGroup} {x y : HFSet}
    (hx : x ∈ grp.G) (hx_nc : x ∉ (center grp).H)
    (hy : y ∈ (HFGroupAction.conjugAction grp).orb x) : y ∉ (center grp).H := by
  -- y = g·x·g⁻¹ for some g. If y ∈ Z(G), then x ∈ Z(G) (by conjugation bijection).
  intro hy_center
  apply hx_nc
  rw [HFAlgebra.mem_center_iff]
  obtain ⟨hyG, g, hg, hact⟩ := (HFGroupAction.mem_orb_iff (HFGroupAction.conjugAction grp) x y).mp hy
  -- y = g·x·g⁻¹, and y ∈ Z(G): ∀ h ∈ G, h·y = y·h
  have hy_comm : ∀ h ∈ grp.G, grp.op h y = grp.op y h := by
    rw [HFAlgebra.mem_center_iff] at hy_center
    -- hy_center.2 : ∀ h, op y h = op h y; we need the symmetric form
    exact fun h hh => (hy_center.2 h hh).symm
  -- x ∈ G, and ∀ k ∈ G, k·x = x·k
  refine ⟨hx, fun k hk => ?_⟩
  -- Let h = g·k·g⁻¹. Then h·y = y·h (since y ∈ Z(G)).
  -- h·y = g·k·g⁻¹·y = g·k·g⁻¹·g·x·g⁻¹ = g·k·x·g⁻¹
  -- y·h = g·x·g⁻¹·g·k·g⁻¹ = g·x·k·g⁻¹
  -- So g·k·x·g⁻¹ = g·x·k·g⁻¹, thus k·x = x·k (cancel g and g⁻¹).
  have hginv : grp.inv g ∈ grp.G := grp.inv_closed hg
  have h_h : grp.op (grp.op g k) (grp.inv g) ∈ grp.G :=
    grp.op_closed (grp.op_closed hg hk) hginv
  -- Use hy_comm with h = g·k·g⁻¹:
  have hcomm := hy_comm (grp.op (grp.op g k) (grp.inv g)) h_h
  -- hcomm : (g·k·g⁻¹)·y = y·(g·k·g⁻¹)
  -- y = g·x·g⁻¹
  -- (g·k·g⁻¹)·(g·x·g⁻¹) = (g·x·g⁻¹)·(g·k·g⁻¹)
  -- g·k·x·g⁻¹ = g·x·k·g⁻¹
  -- k·x = x·k  (cancel g on left, g⁻¹ on right)
  -- goal: op x k = op k x (from mem_center_iff: ∀ h, op x h = op h x)
  -- hcomm : op (gkg⁻¹) y = op y (gkg⁻¹);  y = act g x = op (op g x) (inv g)
  have hgx_G : grp.op g x ∈ grp.G := grp.op_closed hg hx
  have hgxginv_G : grp.op (grp.op g x) (grp.inv g) ∈ grp.G :=
    grp.op_closed hgx_G hginv
  have hgk_G : grp.op g k ∈ grp.G := grp.op_closed hg hk
  -- Replace y with op (op g x) (inv g) in hcomm using hact definitionally
  have hy_conj : y = grp.op (grp.op g x) (grp.inv g) := hact.symm
  rw [hy_conj] at hcomm
  -- Simplify LHS of hcomm:
  -- (g·k·g⁻¹)·(g·x·g⁻¹) = g·k·(g⁻¹·g)·x·g⁻¹ = g·k·e·x·g⁻¹ = g·k·x·g⁻¹
  have lhs_eq : grp.op (grp.op (grp.op g k) (grp.inv g)) (grp.op (grp.op g x) (grp.inv g)) =
                grp.op (grp.op g (grp.op k x)) (grp.inv g) := by
    calc grp.op (grp.op (grp.op g k) (grp.inv g)) (grp.op (grp.op g x) (grp.inv g))
        = grp.op (grp.op g k) (grp.op (grp.inv g) (grp.op (grp.op g x) (grp.inv g))) :=
              grp.op_assoc hgk_G hginv hgxginv_G
      _ = grp.op (grp.op g k) (grp.op (grp.op (grp.inv g) (grp.op g x)) (grp.inv g)) := by
              rw [grp.op_assoc hginv hgx_G hginv]
      _ = grp.op (grp.op g k) (grp.op (grp.op (grp.op (grp.inv g) g) x) (grp.inv g)) := by
              rw [grp.op_assoc hginv hg hx]
      _ = grp.op (grp.op g k) (grp.op (grp.op grp.e x) (grp.inv g)) := by
              rw [grp.op_inv_left hg]
      _ = grp.op (grp.op g k) (grp.op x (grp.inv g)) := by
              rw [grp.op_id_left hx]
      _ = grp.op g (grp.op k (grp.op x (grp.inv g))) := by
              rw [grp.op_assoc hg hk (grp.op_closed hx hginv)]
      _ = grp.op g (grp.op (grp.op k x) (grp.inv g)) := by
              rw [grp.op_assoc hk hx hginv]
      _ = grp.op (grp.op g (grp.op k x)) (grp.inv g) := by
              rw [grp.op_assoc hg (grp.op_closed hk hx) hginv]
  -- Simplify RHS of hcomm:
  have rhs_eq : grp.op (grp.op (grp.op g x) (grp.inv g)) (grp.op (grp.op g k) (grp.inv g)) =
                grp.op (grp.op g (grp.op x k)) (grp.inv g) := by
    calc grp.op (grp.op (grp.op g x) (grp.inv g)) (grp.op (grp.op g k) (grp.inv g))
        = grp.op (grp.op g x) (grp.op (grp.inv g) (grp.op (grp.op g k) (grp.inv g))) :=
              grp.op_assoc hgx_G hginv (grp.op_closed hgk_G hginv)
      _ = grp.op (grp.op g x) (grp.op (grp.op (grp.inv g) (grp.op g k)) (grp.inv g)) := by
              rw [grp.op_assoc hginv hgk_G hginv]
      _ = grp.op (grp.op g x) (grp.op (grp.op (grp.op (grp.inv g) g) k) (grp.inv g)) := by
              rw [grp.op_assoc hginv hg hk]
      _ = grp.op (grp.op g x) (grp.op (grp.op grp.e k) (grp.inv g)) := by
              rw [grp.op_inv_left hg]
      _ = grp.op (grp.op g x) (grp.op k (grp.inv g)) := by
              rw [grp.op_id_left hk]
      _ = grp.op g (grp.op x (grp.op k (grp.inv g))) := by
              rw [grp.op_assoc hg hx (grp.op_closed hk hginv)]
      _ = grp.op g (grp.op (grp.op x k) (grp.inv g)) := by
              rw [grp.op_assoc hx hk hginv]
      _ = grp.op (grp.op g (grp.op x k)) (grp.inv g) := by
              rw [grp.op_assoc hg (grp.op_closed hx hk) hginv]
  rw [lhs_eq, rhs_eq] at hcomm
  have hkx_G : grp.op k x ∈ grp.G := grp.op_closed hk hx
  have hxk_G : grp.op x k ∈ grp.G := grp.op_closed hx hk
  have hgkx_G : grp.op g (grp.op k x) ∈ grp.G := grp.op_closed hg hkx_G
  have hgxk_G : grp.op g (grp.op x k) ∈ grp.G := grp.op_closed hg hxk_G
  -- Cancel g and g⁻¹: from g·(k·x)·g⁻¹ = g·(x·k)·g⁻¹, we get k·x = x·k
  -- goal: op x k = op k x (symmetric of what left_cancel gives)
  have hinner : grp.op g (grp.op k x) = grp.op g (grp.op x k) :=
    grp.right_cancel hginv hgkx_G hgxk_G hcomm
  exact (grp.left_cancel hg hkx_G hxk_G hinner).symm

/-- La órbita de un no-central bajo conjugación es cerrada bajo el shift del grupo. -/
private theorem conj_orb_closed_in_setminus {grp : HFGroup} {x : HFSet}
    (hx : x ∈ grp.G) (hx_nc : x ∉ (center grp).H) :
    (HFGroupAction.conjugAction grp).orb x ⊆ HFSet.setminus grp.G (center grp).H := by
  intro y hy
  have hyG : y ∈ grp.G := ((HFGroupAction.mem_orb_iff (HFGroupAction.conjugAction grp) x y).mp hy).1
  have hy_nc : y ∉ (center grp).H := noncentral_of_orb_noncentral hx hx_nc hy
  exact (HFSet.mem_setminus grp.G (center grp).H y).mpr ⟨hyG, hy_nc⟩

-- ==================================================================
-- §37. p divide la cardinalidad de G \ Z(G) cuando h_no_proper
-- ==================================================================

open Peano Peano.Arith Peano.Primes in
/-- Si para todo subgrupo propio M, `p^k ∤ |M|`, entonces `p ∣ |orb_conj(x)|`
    para todo `x ∉ Z(G)`. -/
private theorem p_dvd_orbit_of_no_proper {grp : HFGroup} {p k : ℕ₀}
    (hp : Peano.Arith.Prime p) (_hk : k ≠ 𝟘)
    (hdvd : p ^ k ∣ HFSet.card grp.G)
    (h_no_proper : ∀ sub : HFSubgroup grp,
        HFSet.card sub.H ≠ HFSet.card grp.G →
        ¬ (p ^ k ∣ HFSet.card sub.H))
    {x : HFSet} (hx : x ∈ grp.G) (hx_nc : x ∉ (center grp).H) :
    p ∣ HFSet.card ((HFGroupAction.conjugAction grp).orb x) := by
  -- Estabilizador de x es propio
  have hstab_ne : HFSet.card ((HFGroupAction.conjugAction grp).stab hx).H ≠ HFSet.card grp.G := by
    intro heq
    -- Si stab = G entonces orb = {x} → x ∈ Z(G), contradicción
    have h_os := (HFGroupAction.conjugAction grp).orbit_stabilizer hx
    have hG_ne : HFSet.card grp.G ≠ 𝟘 := by
      intro h0
      have := HFSet.card_eq_zero_iff.mp h0
      exact absurd (this ▸ grp.e_mem) (HFSet.not_mem_empty _)
    have h_orb_one : HFSet.card ((HFGroupAction.conjugAction grp).orb x) = 𝟙 := by
      apply mul_cancelation_right _ _ (HFSet.card grp.G) hG_ne
      rw [one_mul]; exact heq ▸ h_os
    -- orb x tiene un solo elemento x → x es un punto fijo de todo g → x ∈ Z(G)
    apply hx_nc
    rw [HFAlgebra.mem_center_iff]
    refine ⟨hx, fun g hg => ?_⟩
    -- card(orb x) = 1 → orb x = {x} → g·x·g⁻¹ = x → g·x = x·g
    have hx_in : x ∈ (HFGroupAction.conjugAction grp).orb x :=
      HFGroupAction.orb_self (HFGroupAction.conjugAction grp) hx
    have h_only : ∀ y ∈ (HFGroupAction.conjugAction grp).orb x, y = x := by
      intro y hy
      by_cases hyx : y = x
      · exact hyx
      · exfalso
        -- {x, y} ⊆ orb x but card{x,y} = 2 > 1 = card orb x
        have hxy_sub : HFSet.insert x (HFSet.insert y HFSet.empty) ⊆
            (HFGroupAction.conjugAction grp).orb x := fun z hz =>
          (HFSet.mem_insert z x _).mp hz |>.elim (· ▸ hx_in)
            (fun h => (HFSet.mem_insert z y _).mp h |>.elim (· ▸ hy)
              (absurd · (HFSet.not_mem_empty z)))
        have hx_notin_sy : x ∉ HFSet.insert y HFSet.empty :=
          fun h => (HFSet.mem_insert x y _).mp h |>.elim (fun h => hyx h.symm)
            (HFSet.not_mem_empty x)
        have hcard2 : HFSet.card (HFSet.insert x (HFSet.insert y HFSet.empty)) = 𝟚 := by
          rw [HFSet.card_insert _ _ hx_notin_sy,
              HFSet.card_insert _ _ (HFSet.not_mem_empty y), HFSet.card_empty]
          rfl
        have h2le1 : le₀ 𝟚 𝟙 := by
          have h := HFSet.card_le_of_subset hxy_sub
          rw [hcard2, h_orb_one] at h; exact h
        exact absurd h2le1 (nle_σn_n 𝟙)
    have hact_eq : (HFGroupAction.conjugAction grp).act g x = x :=
      h_only _ ((HFGroupAction.mem_orb_iff (HFGroupAction.conjugAction grp) x _).mpr
        ⟨(HFGroupAction.conjugAction grp).act_closed hg hx, g, hg, rfl⟩)
    -- act g x = g·x·g⁻¹ = x → g·x = x·g
    -- goal: op x g = op g x; the calc below proves op g x = op x g, use .symm
    have hginv : grp.inv g ∈ grp.G := grp.inv_closed hg
    have hgx_G : grp.op g x ∈ grp.G := grp.op_closed hg hx
    exact (calc grp.op g x
        = grp.op (grp.op g x) grp.e := (grp.op_id_right hgx_G).symm
      _ = grp.op (grp.op g x) (grp.op (grp.inv g) g) := by rw [grp.op_inv_left hg]
      _ = grp.op (grp.op (grp.op g x) (grp.inv g)) g := (grp.op_assoc hgx_G hginv hg).symm
      _ = grp.op x g := by
              -- make act g x syntactic, then apply hact_eq
              have hact_def : grp.op (grp.op g x) (grp.inv g) =
                              (HFGroupAction.conjugAction grp).act g x := rfl
              rw [hact_def, hact_eq]).symm
  -- Por h_no_proper: p^k ∤ |stab x|
  have h_stab_ndvd := h_no_proper ((HFGroupAction.conjugAction grp).stab hx) hstab_ne
  -- Por contradicción: si p ∤ |orb x| entonces Coprime(p^k, |orb x|) → p^k | |stab x|
  apply Classical.byContradiction; intro h_orb_ndvd
  apply h_stab_ndvd
  have h_cop : Coprime (p ^ k) (HFSet.card ((HFGroupAction.conjugAction grp).orb x)) := by
    unfold Coprime IsGCD
    refine ⟨one_divides _, one_divides _, ?_⟩
    intro c ⟨hc_pow, hc_orb⟩
    by_cases hc1 : c = 𝟙
    · exact hc1 ▸ divides_refl 𝟙
    · exact absurd
          (divides_trans (prime_dvd_of_dvd_prime_pow hp k hc_pow hc1) hc_orb)
          h_orb_ndvd
  obtain ⟨r, hr⟩ := hdvd
  have h_os := (HFGroupAction.conjugAction grp).orbit_stabilizer hx
  -- h_os : orb.card * stab.H.card = card G
  -- hr   : card G = p^k * r
  -- coprime_dvd_of_dvd_mul : Coprime a b → a ∣ (b * c) → a ∣ c
  -- p^k ∣ (orb * stab) via h_os.trans hr, so p^k ∣ stab
  exact coprime_dvd_of_dvd_mul h_cop ⟨r, h_os.trans hr⟩

open Peano Peano.Arith in
/-- Por inducción fuerte sobre |S|: si S ⊆ G, S ⊆ G\Z(G), órbitas de conjugación
    cerradas en S y cada órbita divisible por p, entonces p | |S|. -/
private theorem p_dvd_card_orbit_closed_set {grp : HFGroup} {p : ℕ₀} (_hp : Peano.Arith.Prime p)
    (S : HFSet)
    (hS_sub : S ⊆ grp.G)
    (hS_nc : ∀ x ∈ S, x ∉ (center grp).H)
    (hS_closed : ∀ x ∈ S, (HFGroupAction.conjugAction grp).orb x ⊆ S)
    (hS_dvd : ∀ x ∈ S, p ∣ HFSet.card ((HFGroupAction.conjugAction grp).orb x)) :
    p ∣ HFSet.card S := by
  -- Inducción fuerte sobre card S, parametrizada sobre T para que IH sea útil
  refine (Peano.WellFounded.strongInductionOn (HFSet.card S) (P := fun n =>
      ∀ T : HFSet,
      HFSet.card T = n →
      T ⊆ grp.G →
      (∀ x ∈ T, x ∉ (center grp).H) →
      (∀ x ∈ T, (HFGroupAction.conjugAction grp).orb x ⊆ T) →
      (∀ x ∈ T, p ∣ HFSet.card ((HFGroupAction.conjugAction grp).orb x)) →
      p ∣ HFSet.card T) ?_ S rfl hS_sub hS_nc hS_closed hS_dvd)
  intro n ih T hcard hT_sub hT_nc hT_closed hT_dvd
  by_cases hT_empty : T = HFSet.empty
  · rw [hT_empty, HFSet.card_empty]; exact divides_zero p
  · -- T ≠ ∅: existe x₀ ∈ T
    obtain ⟨x₀, hx₀⟩ := HFSet.nonempty_of_ne_empty T hT_empty
    have hx₀_G : x₀ ∈ grp.G := hT_sub x₀ hx₀   -- explicit element
    let O := (HFGroupAction.conjugAction grp).orb x₀
    have hx₀_O : x₀ ∈ O :=
      HFGroupAction.orb_self (HFGroupAction.conjugAction grp) hx₀_G
    -- O ⊆ T (hT_closed takes explicit element, then membership, then subset proof)
    have hO_sub_T : O ⊆ T := hT_closed x₀ hx₀
    -- T = O ∪ (T \ O)
    have hT_split : T = HFSet.union O (HFSet.setminus T O) := by
      apply HFSet.extensionality; intro y
      rw [HFSet.mem_union, HFSet.mem_setminus]
      exact ⟨fun hy => if hyo : y ∈ O then Or.inl hyo else Or.inr ⟨hy, hyo⟩,
             fun h => h.elim (fun hy_O => hO_sub_T y hy_O) (·.1)⟩
    -- inter O (T \ O) = ∅
    have hdisj : HFSet.inter O (HFSet.setminus T O) = HFSet.empty := by
      apply HFSet.extensionality; intro y
      constructor
      · intro hy
        have ⟨hyO, hyTO⟩ := (HFSet.mem_inter O (HFSet.setminus T O) y).mp hy
        exact absurd hyO ((HFSet.mem_setminus T O y).mp hyTO).2
      · intro hy; exact absurd hy (HFSet.not_mem_empty y)
    -- card T = card O + card(T \ O)
    have hcard_split : HFSet.card T = add (HFSet.card O) (HFSet.card (HFSet.setminus T O)) :=
      congrArg HFSet.card hT_split |>.trans
        (HFSet.card_union_disjoint O (HFSet.setminus T O) hdisj)
    -- card(T \ O) < card T = n
    have hcard_lt : lt₀ (HFSet.card (HFSet.setminus T O)) n := by
      rw [← hcard, hcard_split]
      have hO_ne : O ≠ HFSet.empty := fun h => absurd (h ▸ hx₀_O) (HFSet.not_mem_empty x₀)
      -- lt_self_add_l : lt₀ b (add a b) when a ≠ 0
      exact Peano.Add.lt_self_add_l _ _ (fun h => hO_ne (HFSet.card_eq_zero_iff.mp h))
    -- Sublemmas for IH (all calls need explicit element before membership proof)
    have hTO_sub : HFSet.setminus T O ⊆ grp.G :=
      fun y hy => hT_sub y ((HFSet.mem_setminus T O y).mp hy).1
    have hTO_nc : ∀ y ∈ HFSet.setminus T O, y ∉ (center grp).H :=
      fun y hy => hT_nc y ((HFSet.mem_setminus T O y).mp hy).1
    have hTO_closed : ∀ y ∈ HFSet.setminus T O,
        (HFGroupAction.conjugAction grp).orb y ⊆ HFSet.setminus T O := by
      intro y hy
      have ⟨hyT, hyO⟩ := (HFSet.mem_setminus T O y).mp hy
      intro z hz
      have hzT : z ∈ T := hT_closed y hyT z hz   -- explicit z and hz
      have hzO : z ∉ O := by
        intro hzO
        have hy_G : y ∈ grp.G := hT_sub y hyT   -- explicit y
        rcases (HFGroupAction.conjugAction grp).orbits_partition hy_G hx₀_G with heq | hdisj_yo
        · -- heq : orb y = orb x₀; use rw to get y ∈ O
          have : y ∈ (HFGroupAction.conjugAction grp).orb y :=
            HFGroupAction.orb_self _ hy_G
          rw [heq] at this
          exact absurd this hyO
        · exact absurd ((HFSet.mem_inter _ O z).mpr ⟨hz, hzO⟩)
            (hdisj_yo ▸ HFSet.not_mem_empty z)
      exact (HFSet.mem_setminus T O z).mpr ⟨hzT, hzO⟩
    have hTO_dvd : ∀ y ∈ HFSet.setminus T O,
        p ∣ HFSet.card ((HFGroupAction.conjugAction grp).orb y) :=
      fun y hy => hT_dvd y ((HFSet.mem_setminus T O y).mp hy).1
    -- Apply IH to T \ O
    have hdvd_TO : p ∣ HFSet.card (HFSet.setminus T O) :=
      ih (HFSet.card (HFSet.setminus T O)) hcard_lt
        (HFSet.setminus T O) rfl hTO_sub hTO_nc hTO_closed hTO_dvd
    rw [hcard_split]
    exact divides_add (hT_dvd x₀ hx₀) hdvd_TO

open Peano Peano.Arith in
/-- Si `∀ M prop., p^k ∤ |M|`, entonces `p ∣ card(G \ Z(G))`. -/
private theorem p_dvd_setminus_center_of_no_proper {grp : HFGroup} {p k : ℕ₀}
    (hp : Peano.Arith.Prime p) (hk : k ≠ 𝟘)
    (hdvd : p ^ k ∣ HFSet.card grp.G)
    (h_no_proper : ∀ sub : HFSubgroup grp,
        HFSet.card sub.H ≠ HFSet.card grp.G →
        ¬ (p ^ k ∣ HFSet.card sub.H)) :
    p ∣ HFSet.card (HFSet.setminus grp.G (center grp).H) := by
  let S := HFSet.setminus grp.G (center grp).H
  apply p_dvd_card_orbit_closed_set hp S
  · -- S ⊆ G
    exact fun y hy => (HFSet.mem_setminus grp.G (center grp).H y).mp hy |>.1
  · -- ∀ x ∈ S, x ∉ Z(G)
    exact fun y hy => (HFSet.mem_setminus grp.G (center grp).H y).mp hy |>.2
  · -- orb(x) ⊆ S for x ∈ S
    intro x hxS
    have hx := (HFSet.mem_setminus grp.G (center grp).H x).mp hxS
    exact conj_orb_closed_in_setminus hx.1 hx.2
  · -- p | |orb(x)| for x ∈ S
    intro x hxS
    have hx := (HFSet.mem_setminus grp.G (center grp).H x).mp hxS
    exact p_dvd_orbit_of_no_proper hp hk hdvd h_no_proper hx.1 hx.2

open Peano Peano.Arith in
/-- Si `∀ M prop., p^k ∤ |M|`, entonces `p ∣ card(Z(G))`. -/
private theorem p_dvd_center_of_no_proper {grp : HFGroup} {p k : ℕ₀}
    (hp : Peano.Arith.Prime p) (hk : k ≠ 𝟘)
    (hdvd : p ^ k ∣ HFSet.card grp.G)
    (h_no_proper : ∀ sub : HFSubgroup grp,
        HFSet.card sub.H ≠ HFSet.card grp.G →
        ¬ (p ^ k ∣ HFSet.card sub.H)) :
    p ∣ HFSet.card (center grp).H := by
  have hp_sm := p_dvd_setminus_center_of_no_proper hp hk hdvd h_no_proper
  have hclass := class_equation grp
  -- Derivar p ∣ card G (ya que k ≠ 0)
  have hp_G : p ∣ HFSet.card grp.G := by
    cases k with
    | zero => exact absurd rfl hk
    | succ k' =>
      have hps : p ^ σ k' = mul (p ^ k') p := by rw [pow_def]; exact Peano.Pow.pow_succ p k'
      exact divides_trans ⟨p ^ k', by rw [hps, mul_comm]⟩ hdvd
  -- card Z(G) > 0 (pues e ∈ Z(G))
  have hcenter_pos : HFSet.card (center grp).H ≠ 𝟘 := fun h =>
    absurd ((HFSet.card_eq_zero_iff.mp h) ▸ (center grp).e_mem) (HFSet.not_mem_empty _)
  -- card(G \ Z(G)) < card G (pues card Z > 0)
  have hlt : lt₀ (HFSet.card (HFSet.setminus grp.G (center grp).H)) (HFSet.card grp.G) := by
    -- lt_self_add_l a b h : lt₀ a (add b a)  (b on the left of add)
    rw [hclass]
    exact Peano.Add.lt_self_add_l _ _ hcenter_pos
  have hle := lt_imp_le _ _ hlt
  -- sub(card G, card(G\Z)) = card Z(G)
  have hcenter_eq : Peano.Sub.sub (HFSet.card grp.G)
        (HFSet.card (HFSet.setminus grp.G (center grp).H)) =
      HFSet.card (center grp).H := by
    have key := Peano.Sub.sub_k_add_k (HFSet.card grp.G)
      (HFSet.card (HFSet.setminus grp.G (center grp).H)) hle
    apply Peano.Add.add_cancel (HFSet.card (HFSet.setminus grp.G (center grp).H))
    -- Goal: add (card(G\Z)) (sub G (G\Z)) = add (card(G\Z)) (card Z)
    -- key: add (sub G (G\Z)) (card(G\Z)) = G;  hclass: G = add (card Z) (card(G\Z))
    rw [add_comm _ (Peano.Sub.sub _ _)]
    exact (key.trans hclass).trans (add_comm _ _)
  rw [← hcenter_eq]
  exact divides_sub hlt hp_G hp_sm

-- ==================================================================
-- §38. Subgrupo cíclico generado por elemento central es normal
-- ==================================================================

/-- El subgrupo cíclico `⟨z⟩` de un elemento central `z ∈ Z(G)` es normal. -/
private theorem cyclicSubgroup_of_central_isNormal {grp : HFGroup} {z : HFSet}
    (hz : z ∈ grp.G) (hz_center : z ∈ (center grp).H) :
    (cyclicSubgroup grp hz).isNormal := by
  -- isNormal : ∀ (g n : HFSet), g ∈ G → n ∈ H → op (op g n) (inv g) ∈ H
  intro g n hg hn
  rw [HFAlgebra.mem_center_iff] at hz_center
  -- hz_center.1 : z ∈ grp.G,  hz_center.2 : ∀ h ∈ G, op h z = op z h
  have hn_comm : ∀ h ∈ grp.G, grp.op h n = grp.op n h := by
    intro h hh
    have hcomm_gpow : ∀ m : ℕ₀, grp.op h (gpow grp z m) = grp.op (gpow grp z m) h := by
      intro m; induction m with
      | zero =>
        rw [gpow_zero, grp.op_id_right hh, grp.op_id_left hh]
      | succ m' ihm' =>
        rw [gpow_succ]
        have pm := gpow_mem grp hz m'
        calc grp.op h (grp.op (gpow grp z m') z)
            = grp.op (grp.op h (gpow grp z m')) z := by rw [grp.op_assoc hh pm hz_center.1]
          _ = grp.op (grp.op (gpow grp z m') h) z := by rw [ihm']
          _ = grp.op (gpow grp z m') (grp.op h z) := by rw [← grp.op_assoc pm hh hz_center.1]
          _ = grp.op (gpow grp z m') (grp.op z h) := by rw [hz_center.2 h hh]
          _ = grp.op (grp.op (gpow grp z m') z) h := by rw [grp.op_assoc pm hz_center.1 hh]
    obtain ⟨k, _, hk⟩ := (mem_cyclicCarrier grp hz n).mp hn
    rw [hk]; exact hcomm_gpow k
  have hconj_eq : grp.op (grp.op g n) (grp.inv g) = n := by
    have hn_G : n ∈ grp.G := (cyclicSubgroup grp hz).H_sub hn
    rw [hn_comm g hg]
    rw [grp.op_assoc hn_G hg (grp.inv_closed hg)]
    rw [grp.op_inv_right hg, grp.op_id_right hn_G]
  rw [hconj_eq]; exact hn

-- ==================================================================
-- §39. Aritmética de la cardinalidad en el cociente
-- ==================================================================

open Peano Peano.Arith in
/-- Card du quotient: |G/⟨z⟩| = |G| / p quand |⟨z⟩| = p. -/
private theorem card_quotient_cyclic {grp : HFGroup} {z : HFSet}
    (hz : z ∈ grp.G) (hz_center : z ∈ (center grp).H)
    {p : ℕ₀} (hord : order grp hz = p) :
    HFSet.card (quotientGroup grp (cyclicSubgroup grp hz)
      (cyclicSubgroup_of_central_isNormal hz hz_center)).G =
    div (HFSet.card grp.G) p := by
  -- card G/⟨z⟩ = index(⟨z⟩) = card G / card ⟨z⟩
  have hcyc_card : HFSet.card (cyclicSubgroup grp hz).H = p := by
    rw [← hord]; exact cyclicCarrier_card_eq_order grp hz
  have hlag := (cyclicSubgroup grp hz).card_G_eq_card_H_mul_index
  -- card G = card(cosets) * card ⟨z⟩ = card G/⟨z⟩ * p
  have hcycne : HFSet.card (cyclicSubgroup grp hz).H ≠ 𝟘 := by
    rw [hcyc_card]; exact hord ▸ order_ne_zero grp hz
  have hp_ne : p ≠ 𝟘 := hcyc_card ▸ hcycne
  rw [hcyc_card] at hlag
  -- hlag : card G = mul (card cosets) p
  -- card(G/⟨z⟩) = card(cosets) = card G / p
  show HFSet.card (cyclicSubgroup grp hz).cosets = div (HFSet.card grp.G) _
  have hp_dvd : p ∣ HFSet.card grp.G := ⟨_, hlag.trans (mul_comm _ _)⟩
  exact (mul_cancelation_right _ _ p hp_ne
    ((div_mul_cancel hp_ne hp_dvd).trans hlag)).symm

-- ==================================================================
-- §40. Primer Teorema de Sylow (caso general)
-- ==================================================================

open Peano Peano.Arith in
/-- **Primer Teorema de Sylow**: Si `p` es primo y `p^k ∣ |G|`, existe un subgrupo
    de `G` de orden `p^k`. Prueba por inducción fuerte sobre `|G|`. -/
theorem sylow_first (grp : HFGroup) (p k : ℕ₀)
    (hp : Peano.Arith.Prime p) (hdvd : p ^ k ∣ HFSet.card grp.G) :
    ∃ sub : HFSubgroup grp, HFSet.card sub.H = p ^ k := by
  refine (Peano.WellFounded.strongInductionOn (HFSet.card grp.G) (P := fun n =>
    ∀ (grp : HFGroup), HFSet.card grp.G = n →
    ∀ (p k : ℕ₀), Peano.Arith.Prime p → p ^ k ∣ HFSet.card grp.G →
    ∃ sub : HFSubgroup grp, HFSet.card sub.H = p ^ k) ?_ grp rfl p k hp hdvd)
  intro n ih grp' hcard' p' k' hp' hdvd'
  cases k' with
  | zero => exact sylow_first_zero grp' p'
  | succ m =>
    by_cases h_proper :
        ∃ sub : HFSubgroup grp', HFSet.card sub.H ≠ HFSet.card grp'.G ∧
                                  p' ^ (σ m) ∣ HFSet.card sub.H
    · -- Caso 2: ∃ M propio con p'^(σm) | |M|; aplicar HI a M
      obtain ⟨M, hM_ne, hM_dvd⟩ := h_proper
      have hM_lt : lt₀ (HFSet.card M.H) n := by
        rw [← hcard']
        rcases (le_iff_lt_or_eq _ _).mp
          (HFSet.card_le_of_subset (fun x hx => M.H_sub hx)) with h | h
        · exact h
        · exact absurd h hM_ne
      -- M.toHFGroup.G = M.H definitionally
      obtain ⟨sub_M, hsub_M⟩ := ih (HFSet.card M.H) hM_lt M.toHFGroup rfl p' (σ m) hp' hM_dvd
      exact ⟨subgroupOfSubgroup M sub_M, hsub_M⟩
    · -- Caso 3: ∀ M propio, p'^(σm) ∤ |M|
      have h_no_proper : ∀ sub : HFSubgroup grp',
          HFSet.card sub.H ≠ HFSet.card grp'.G →
          ¬ (p' ^ (σ m) ∣ HFSet.card sub.H) :=
        fun sub hne hdvd_sub => h_proper ⟨sub, hne, hdvd_sub⟩
      by_cases h_eq_card : HFSet.card grp'.G = p' ^ (σ m)
      · exact ⟨improperSubgroup grp', by rw [improperSubgroup_card, h_eq_card]⟩
      · -- Caso 3b: descomponer p' (primo ≥ 2, luego ≠ 𝟘)
        cases p' with
        | zero => exact absurd rfl hp'.1
        | succ p'_pred =>
        -- hp_center : σ p'_pred ∣ card Z(G')
        have hp_center : σ p'_pred ∣ HFSet.card (center grp').H :=
          p_dvd_center_of_no_proper hp' (zero_ne_succ m).symm hdvd' h_no_proper
        -- Cauchy en Z(G')
        obtain ⟨z_sub, hz_card⟩ := cauchy_minimal (center grp').toHFGroup hp' hp_center
        let N := subgroupOfSubgroup (center grp') z_sub  -- N.H = z_sub.H definitionally
        have hN_card : HFSet.card N.H = σ p'_pred := hz_card
        have hp'_ne : (σ p'_pred) ≠ 𝟘 := (zero_ne_succ p'_pred).symm
        -- N ⊴ G' (N ≤ Z(G'), centro abeliano)
        have hN_normal : N.isNormal := by
          intro g n hg hn
          have hn_cH : n ∈ (center grp').H := z_sub.H_sub hn
          have hn_G : n ∈ grp'.G := (center grp').H_sub hn_cH
          rw [HFAlgebra.mem_center_iff] at hn_cH
          -- hn_cH.2 g hg : op n g = op g n; necesitamos reescribir op g n → op n g
          have hconj : grp'.op (grp'.op g n) (grp'.inv g) = n := by
            rw [← hn_cH.2 g hg, grp'.op_assoc hn_G hg (grp'.inv_closed hg),
                grp'.op_inv_right hg, grp'.op_id_right hn_G]
          rw [hconj]; exact hn
        -- Q = G'/N; Lagrange: card G' = card(cosets) · (σ p'_pred)
        let Q := quotientGroup grp' N hN_normal
        have hlag_N := N.card_G_eq_card_H_mul_index
        rw [hN_card] at hlag_N
        -- hlag_N : card G' = mul (card N.cosets) (σ p'_pred)
        have hQ_card : HFSet.card Q.G = div (HFSet.card grp'.G) (σ p'_pred) := by
          show HFSet.card N.cosets = div (HFSet.card grp'.G) (σ p'_pred)
          have hp_dvd_G : σ p'_pred ∣ HFSet.card grp'.G :=
            ⟨_, hlag_N.trans (mul_comm _ _)⟩
          exact (mul_cancelation_right _ _ (σ p'_pred) hp'_ne
            ((div_mul_cancel hp'_ne hp_dvd_G).trans hlag_N)).symm
        -- p'^m ∣ |Q|
        have hQ_dvd : (σ p'_pred) ^ m ∣ HFSet.card Q.G := by
          rw [hQ_card]
          obtain ⟨c, hc⟩ := hdvd'
          have hps : (σ p'_pred) ^ σ m = mul (σ p'_pred) ((σ p'_pred) ^ m) := by
            rw [pow_def]; exact (Peano.Pow.pow_succ (σ p'_pred) m).trans (mul_comm _ _)
          -- card G' = p' · (p'^m · c)
          have hc' : HFSet.card grp'.G = mul (σ p'_pred) (mul ((σ p'_pred) ^ m) c) := by
            rw [hc, hps, mul_assoc]
          have hdvd_G : (σ p'_pred) ∣ HFSet.card grp'.G :=
            ⟨mul ((σ p'_pred) ^ m) c, hc'⟩
          refine ⟨c, ?_⟩
          -- div(card G', p') = p'^m · c
          -- Use right-cancellation: (div G p') · p' = G = p' · (p'^m · c) = (p'^m · c) · p'
          apply mul_cancelation_right _ _ (σ p'_pred) hp'_ne
          -- mul (div G p') p' = G = mul (p'^m · c) p'
          exact (div_mul_cancel hp'_ne hdvd_G).trans (hc'.trans (mul_comm _ _))
        -- |Q| < n
        have hcosets_ne : HFSet.card N.cosets ≠ 𝟘 := by
          intro h
          have hmem : N.cosetOf grp'.e ∈ N.cosets := N.cosetOf_mem_cosets grp'.e_mem
          rw [HFSet.card_eq_zero_iff.mp h] at hmem
          exact HFSet.not_mem_empty _ hmem
        have hQ_lt : lt₀ (HFSet.card Q.G) n := by
          rw [← hcard']
          -- Q.G = N.cosets definitionally; hlag_N : card G = mul (card cosets) p'
          show lt₀ (HFSet.card N.cosets) (HFSet.card grp'.G)
          rw [hlag_N]
          -- prime_ge_two : le₀ 𝟚 p' ≠ lt₀ 𝟙 p' in general; bridge via succ_lt_succ_iff
          have hp_gt1 : lt₀ 𝟙 (σ p'_pred) :=
            (succ_lt_succ_iff 𝟘 p'_pred).mpr
              (pos_of_ne_zero _ (fun h => hp'.2.1 (show σ p'_pred = 𝟙 by rw [h]; rfl)))
          exact Peano.Mul.mul_lt_left _ _ hcosets_ne hp_gt1
        -- HI sobre Q
        obtain ⟨sub_Q, hsub_Q⟩ :=
          ih (HFSet.card Q.G) hQ_lt Q rfl (σ p'_pred) m hp' hQ_dvd
        -- Preimagen P = π⁻¹(sub_Q): |P| = p'^m · p' = p'^(σm)
        let P := HFSubgroup.preimageSubgroup N hN_normal sub_Q
        have hP_card : HFSet.card P.H = (σ p'_pred) ^ σ m := by
          rw [card_preimage_mul, hsub_Q, hN_card]
          -- goal: mul ((σ p'_pred)^m) (σ p'_pred) = (σ p'_pred)^(σm)
          have hps2 : (σ p'_pred) ^ σ m = mul ((σ p'_pred) ^ m) (σ p'_pred) := by
            rw [pow_def]; exact Peano.Pow.pow_succ (σ p'_pred) m
          exact hps2.symm
        exact ⟨P, hP_card⟩

end HFAlgebra

-- ======================================================================
-- Exports
-- ======================================================================
--
-- Público (HFAlgebra — definiciones básicas):
--   pow_dvd_card              : ∃ m, p^k · m = card X
--   isPSubgroup               : ∃ k, card sub.H = p^k
--   isSylowExponent           : p^n ∣ |G| ∧ p^(n+1) ∤ |G|
--   isSylowSubgroup           : ∃ n, isSylowExponent ∧ card sub.H = p^n
--   trivial / trivial_card    : subgrupo trivial y su cardinalidad = 1
--   pow_dvd_card_of_le        : a ≤ b → p^b ∣ |G| → p^a ∣ |G|
--   sylow_card_eq             : todos los Sylow-p tienen el mismo cardinal
--   sylow_first_zero          : caso n = 0 del primer teorema de Sylow
--
-- Público (HFAlgebra — gpow y order):
--   gpow / gpow_zero / gpow_succ / gpow_one / gpow_mem / gpow_add
--   order / order_pos / order_ne_zero
--   gpow_order_eq_id / order_minimal / order_le_card
--   gpow_mul_order_eq_id / gpow_mod_order
--   cyclicCarrier / cyclicSubgroup
--
-- Público (HFAlgebra — infraestructura de McKay D.4.A–D.4.C):
--   mckayCarrier / mem_mckayCarrier / mckayCarrier_subset_nPow
--   mckayShift / mckayShift_mem_nPow / mckayShift_mem_mckayCarrier
--   mckayFixedPoints / mem_mckayFixedPoints / mckayFixedPoints_subset
--   shiftIter / shiftIter_mem_nPow / shiftIter_mem_mckayCarrier
--   shiftIter_period / shiftIter_eq_id_iff_periodOf_dvd / shiftIter_inj_below_period
--   orbitOf / mem_orbitOf / card_orbitOf_le / orbitOf_eq_of_mem
--   orbitOf_eq_or_disjoint
--   periodOf / periodOf_pos / periodOf_ne_zero
--   shiftIter_periodOf / periodOf_minimal / periodOf_le_succ_n / periodOf_dvd_succ_n
--   dvd_card_mckayCarrier_succ        : p ∣ |G|, n ≠ 𝟘 → p ∣ |carrier(σ n)|  (D.3)
--   card_orbitOf_eq_periodOf          : card(orbitOf t) = periodOf t            (§22)
--   card_orbitOf_one_or_succ          : primo → card ∈ {1, σ n}                 (§23)
--
-- Público (HFAlgebra — D.4.D argumento de McKay, §24–§27):
--   periodOf_eq_one_iff_fixed         : period = 1 ↔ mckayShift t = t          (§24)
--   card_orbitOf_eq_one_iff_fixed     : card = 1 ↔ mckayShift t = t            (§24)
--   card_orbitOf_eq_succ_of_not_fixed : ¬fijo → card(orbit) = σ n              (§25)
--   succ_n_dvd_card_of_shift_closed_no_fixed :
--       S ⊆ carrier, S shift-cerrado, sin fijos → σ n ∣ card S                  (§26)
--   succ_n_dvd_card_mckayFixedPoints  :
--       primo(σ n) ∧ σ n ∣ |G| → σ n ∣ card(mckayFixedPoints)   (D.4.D/McKay)  (§27)
--
-- Público (HFAlgebra — §28–§32: punto fijo canónico, Cauchy):
--   eTuple_mem_mckayFixedPoints       : eTuple grp p ∈ mckayFixedPoints grp p   (§28)
--   order_dvd_of_gpow_eq_id           : g^m = e → order g ∣ m                  (§30)
--   order_eq_prime_of_pow             : g^p = e, primo p, g ≠ e → order g = p   (§30)
--   cyclicCarrier_card_eq_order       : card(⟨g⟩) = order g                    (§31)
--   cauchy_minimal                    : primo p, p ∣ |G| → ∃ sub, card sub = p  (§32)
--
-- Público (HFAlgebra — §33–§40: Primer Teorema de Sylow):
--   subgroupOfSubgroup                : subgrupo de subgrupo es subgrupo de G   (§33)
--   card_preimage_mul                 : card(π⁻¹(Q)) = card(Q) · card(N)       (§34)
--   cyclicSubgroup_of_central_isNormal: ⟨z⟩ normal cuando z ∈ Z(G)             (§38)
--   card_quotient_cyclic              : card(G/⟨z⟩) = card(G)/p, |⟨z⟩| = p      (§39)
--   sylow_first                       : **Primer Teorema de Sylow** —          (§40)
--       primo p, p^k ∣ |G| → ∃ subgrupo de orden p^k
--       (inducción fuerte sobre |G|; ramas: subgrupo propio p-divisible,
--        |G| = p^k, o Cauchy en Z(G) + cociente G/N + preimagen)
