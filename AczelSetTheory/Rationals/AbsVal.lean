/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/AbsVal.lean
-- Valor absoluto sobre ℚ₀cls y propiedades básicas (M2B, parcial).
--
-- API entregada:
--   absVal              : ℚ₀cls → ℚ₀cls
--   absVal_zero         : absVal 0 = 0
--   absVal_of_nonneg    : 0 ≤ q → absVal q = q
--   absVal_of_nonpos    : q ≤ 0 → absVal q = -q
--   absVal_nonneg       : 0 ≤ absVal q
--   absVal_neg          : absVal (-q) = absVal q
--   absVal_zero_iff     : absVal q = 0 ↔ q = 0
--   absVal_idempotent   : absVal (absVal q) = absVal q
--   absVal_sub_comm     : absVal (a - b) = absVal (b - a)
--   absVal_mul          : absVal (a * b) = absVal a * absVal b
--   absVal_add_le       : absVal (a + b) ≤ absVal a + absVal b   (triangular)
--
-- Dependencies: AczelSetTheory.Rationals.Basic
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.Basic

namespace ℚ₀cls

-- ============================================================
-- Sección 1: Definición de valor absoluto
-- ============================================================

/-- Valor absoluto en ℚ₀cls: `q` si `0 ≤ q`, `-q` en caso contrario. Computable
gracias a `instDecidableLE`. -/
def absVal (q : ℚ₀cls) : ℚ₀cls := if 0 ≤ q then q else -q

-- ============================================================
-- Sección 2: Propiedades de casos
-- ============================================================

theorem absVal_of_nonneg {q : ℚ₀cls} (h : 0 ≤ q) : absVal q = q := by
  simp [absVal, h]

theorem absVal_of_nonpos {q : ℚ₀cls} (h : q ≤ 0) : absVal q = -q := by
  by_cases hpos : (0 : ℚ₀cls) ≤ q
  · -- q = 0
    have hzero : q = 0 := le_antisymm h hpos
    rw [absVal, if_pos hpos, hzero, neg_zero]
  · simp [absVal, hpos]

theorem absVal_zero : absVal (0 : ℚ₀cls) = 0 := by
  rw [absVal_of_nonneg (le_refl 0)]

-- ============================================================
-- Sección 3: No-negatividad e idempotencia
-- ============================================================

theorem absVal_nonneg (q : ℚ₀cls) : 0 ≤ absVal q := by
  by_cases h : (0 : ℚ₀cls) ≤ q
  · rw [absVal_of_nonneg h]; exact h
  · -- ¬(0 ≤ q) ⇒ q ≤ 0 (por totalidad), luego absVal q = -q ≥ 0
    have hle : q ≤ 0 := (le_total 0 q).resolve_left h
    rw [absVal_of_nonpos hle]
    -- 0 ≤ -q  ⟺  -0 ≤ -q  (ya que neg_zero), y neg_le_neg de q ≤ 0 da -0 ≤ -q.
    have := neg_le_neg hle
    rwa [neg_zero] at this

theorem absVal_idempotent (q : ℚ₀cls) : absVal (absVal q) = absVal q :=
  absVal_of_nonneg (absVal_nonneg q)

-- ============================================================
-- Sección 4: Simetría bajo negación
-- ============================================================

theorem absVal_neg (q : ℚ₀cls) : absVal (Neg.neg q) = absVal q := by
  by_cases hq : (0 : ℚ₀cls) ≤ q
  · -- q ≥ 0 ⇒ -q ≤ 0
    have hnq : Neg.neg q ≤ 0 := by
      have := neg_le_neg hq
      rwa [neg_zero] at this
    rw [absVal_of_nonneg hq, absVal_of_nonpos hnq, neg_neg]
  · -- ¬(0 ≤ q) ⇒ q ≤ 0, y -q ≥ 0
    have hqle : q ≤ 0 := (le_total 0 q).resolve_left hq
    have hnq : 0 ≤ Neg.neg q := by
      have := neg_le_neg hqle
      rwa [neg_zero] at this
    rw [absVal_of_nonpos hqle, absVal_of_nonneg hnq]

-- ============================================================
-- Sección 5: Caracterización del cero
-- ============================================================

theorem absVal_zero_iff (q : ℚ₀cls) : absVal q = 0 ↔ q = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ absVal_zero⟩
  by_cases hq : (0 : ℚ₀cls) ≤ q
  · -- absVal q = q, luego q = 0
    rw [absVal_of_nonneg hq] at h; exact h
  · -- ¬(0 ≤ q), q ≤ 0, absVal q = -q = 0 ⇒ -(-q) = -0 ⇒ q = 0
    have hqle : q ≤ 0 := (le_total 0 q).resolve_left hq
    rw [absVal_of_nonpos hqle] at h
    have : Neg.neg (Neg.neg q) = Neg.neg 0 := congrArg Neg.neg h
    rw [neg_neg, neg_zero] at this
    exact this

-- ============================================================
-- Sección 6: Sub-conmutatividad, producto y desigualdad triangular
-- ============================================================

theorem absVal_sub_comm (a b : ℚ₀cls) : absVal (a - b) = absVal (b - a) := by
  have hkey : Neg.neg (b + Neg.neg a) = a + Neg.neg b := by
    have h1 : Neg.neg (b + Neg.neg a) = Neg.neg b + Neg.neg (Neg.neg a) :=
      neg_add b (Neg.neg a)
    have h2 : Neg.neg (Neg.neg a) = a := neg_neg a
    rw [h1, h2]
    exact add_comm (Neg.neg b) a
  have hsc : absVal (a - b) = absVal (Neg.neg (b - a)) := by
    show absVal (a + Neg.neg b) = absVal (Neg.neg (b + Neg.neg a))
    congr 1
    exact hkey.symm
  rw [hsc, absVal_neg]

theorem absVal_mul (a b : ℚ₀cls) : absVal (a * b) = absVal a * absVal b := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · -- 0 ≤ a, 0 ≤ b
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    rw [absVal_of_nonneg hab, absVal_of_nonneg ha, absVal_of_nonneg hb]
  · -- 0 ≤ a, b ≤ 0
    have hab : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hb
    rw [absVal_of_nonpos hab, absVal_of_nonneg ha, absVal_of_nonpos hb, mul_neg]
  · -- a ≤ 0, 0 ≤ b
    have hab : a * b ≤ 0 := by
      rw [mul_comm]; exact mul_nonpos_of_nonneg_of_nonpos hb ha
    rw [absVal_of_nonpos hab, absVal_of_nonpos ha, absVal_of_nonneg hb, neg_mul]
  · -- a ≤ 0, b ≤ 0
    have hab : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos ha hb
    rw [absVal_of_nonneg hab, absVal_of_nonpos ha, absVal_of_nonpos hb,
        neg_mul, mul_neg, neg_neg]

end ℚ₀cls

-- ============================================================
-- Sección 3: le_absVal y absVal_add_le
-- Dentro del namespace ℚ₀cls la notación + resuelve a ℚ₀cls.instAdd
-- (backtracking desde la notación global de Peano). Los helpers
-- q0_add_le_add_* del nivel raíz ya no son necesarios.
-- ============================================================

namespace ℚ₀cls

theorem le_absVal (q : ℚ₀cls) : q ≤ absVal q := by
  by_cases h : (0 : ℚ₀cls) ≤ q
  · rw [absVal_of_nonneg h]; exact le_refl q
  · have hle : q ≤ 0 := (le_total 0 q).resolve_left h
    rw [absVal_of_nonpos hle]
    have h0nq : (0 : ℚ₀cls) ≤ -q := by
      have := neg_le_neg hle; rwa [neg_zero] at this
    exact le_trans hle h0nq

theorem neg_le_absVal (q : ℚ₀cls) : Neg.neg q ≤ ℚ₀cls.absVal q := by
  have h1 : Neg.neg q ≤ ℚ₀cls.absVal (Neg.neg q) := ℚ₀cls.le_absVal (Neg.neg q)
  have h2 : ℚ₀cls.absVal (Neg.neg q) = ℚ₀cls.absVal q := ℚ₀cls.absVal_neg q
  rw [h2] at h1
  exact h1

theorem absVal_add_le (a b : ℚ₀cls) :
    absVal (a + b) ≤ absVal a + absVal b := by
  by_cases h : (0 : ℚ₀cls) ≤ a + b
  · rw [absVal_of_nonneg h]
    exact le_trans
      (add_le_add_left (le_absVal b) a)
      (add_le_add_right (le_absVal a) (absVal b))
  · have hle := (le_total (0 : ℚ₀cls) _).resolve_left h
    rw [absVal_of_nonpos hle]
    have h1 : -a ≤ absVal a := by
      have h' := le_absVal (-a); rwa [absVal_neg] at h'
    have h2 : -b ≤ absVal b := by
      have h' := le_absVal (-b); rwa [absVal_neg] at h'
    -- -(a+b) es definitionally Neg.neg (Add.add a b); evitar notación + en calc
    have hstep : Neg.neg (Add.add a b) = Add.add (Neg.neg a) (Neg.neg b) := neg_add a b
    exact le_trans (hstep ▸ le_refl _)
      (le_trans (add_le_add_right h1 _) (add_le_add_left h2 _))


theorem absVal_mul_sub_mul (a b c d : ℚ₀cls) :
    absVal (a * b - c * d) ≤ Add.add (absVal a * absVal (b - d)) (absVal d * absVal (a - c)) := by
  have h_eq : a * b - c * d = Add.add (a * (b - d)) (d * (a - c)) := by
    calc
      a * b - c * d = Add.add (a * b) (Neg.neg (c * d)) := rfl
      _ = Add.add (Add.add (a * b) 0) (Neg.neg (c * d)) := by rw [add_zero]
      _ = Add.add (Add.add (a * b) (Add.add (Neg.neg (a * d)) (a * d))) (Neg.neg (c * d)) := by rw [neg_add_self (a * d)]
      _ = Add.add (Add.add (Add.add (a * b) (Neg.neg (a * d))) (a * d)) (Neg.neg (c * d)) := by rw [add_assoc (a * b) (Neg.neg (a * d)) (a * d)]
      _ = Add.add (Add.add (a * b) (Neg.neg (a * d))) (Add.add (a * d) (Neg.neg (c * d))) := by rw [add_assoc (Add.add (a * b) (Neg.neg (a * d))) (a * d) (Neg.neg (c * d))]
      _ = Add.add (Add.add (a * b) (a * (Neg.neg d))) (Add.add (a * d) (Neg.neg (c * d))) := by rw [mul_neg a d]
      _ = Add.add (a * Add.add b (Neg.neg d)) (Add.add (a * d) (Neg.neg (c * d))) := by rw [← left_distrib a b (Neg.neg d)]
      _ = Add.add (a * (b - d)) (Add.add (a * d) (Neg.neg (c * d))) := rfl
      _ = Add.add (a * (b - d)) (Add.add (d * a) (Neg.neg (c * d))) := by rw [mul_comm a d]
      _ = Add.add (a * (b - d)) (Add.add (d * a) (Neg.neg (d * c))) := by rw [mul_comm c d]
      _ = Add.add (a * (b - d)) (Add.add (d * a) (d * (Neg.neg c))) := by rw [mul_neg d c]
      _ = Add.add (a * (b - d)) (d * Add.add a (Neg.neg c)) := by rw [← left_distrib d a (Neg.neg c)]
      _ = Add.add (a * (b - d)) (d * (a - c)) := rfl

  rw [h_eq]
  have h_tri := absVal_add_le (a * (b - d)) (d * (a - c))
  have h_mul1 : absVal (a * (b - d)) = absVal a * absVal (b - d) := absVal_mul a (b - d)
  have h_mul2 : absVal (d * (a - c)) = absVal d * absVal (a - c) := absVal_mul d (a - c)
  rw [h_mul1, h_mul2] at h_tri
  exact h_tri

theorem le_div_add_one_mul (a b : ℕ₀) (hb : b ≠ 𝟘) : le₀ a (mul (add (div a b) 𝟙) b) := by
  have heq : a = add (mul (div a b) b) (mod a b) := divMod_spec a b hb
  have hlt : lt₀ (mod a b) b := mod_lt a b hb
  have h_add : lt₀ (add (mul (div a b) b) (mod a b)) (add (mul (div a b) b) b) :=
    (add_lt_add_left_iff (mul (div a b) b) (mod a b) b).mpr hlt
  rw [←heq] at h_add
  have hrw : add (mul (div a b) b) b = mul (add (div a b) 𝟙) b := by
    have h1 : mul (add (div a b) 𝟙) b = add (mul (div a b) b) (mul 𝟙 b) := Peano.Mul.add_mul (div a b) 𝟙 b
    have h2 : mul 𝟙 b = b := Peano.Mul.one_mul b
    rw [h2] at h1
    exact h1.symm
  rw [hrw] at h_add
  exact lt_imp_le _ _ h_add

theorem le_abs_self (z : ℤ₀cls) : z ≤ ℤ₀cls.abs z := by
  by_cases h : 0 ≤ z
  · unfold ℤ₀cls.abs
    rw [if_pos h]
    exact ℤ₀cls.le_refl z
  · have hz0 : z ≤ 0 := by
      cases ℤ₀cls.le_total 0 z with
      | inl h1 => exact absurd h1 h
      | inr h2 => exact h2
    have h0abs : 0 ≤ ℤ₀cls.abs z := ℤ₀cls.abs_nonneg z
    exact ℤ₀cls.le_trans hz0 h0abs

theorem neg_le_abs_self (z : ℤ₀cls) : -z ≤ ℤ₀cls.abs z := by
  have h := le_abs_self (-z)
  have h2 : ℤ₀cls.abs (-z) = ℤ₀cls.abs z := ℤ₀cls.abs_neg z
  rw [h2] at h
  exact h

theorem le_boundNat (q : ℚ₀cls) : absVal q ≤ ofNat₀ (boundNat q) := by
  refine Quotient.inductionOn q (fun p => ?_)
  -- absVal q <= N means q <= N and -q <= N
  -- Wait, since absVal q is either q or -q, if we prove both mk p.1 p.2 <= N and mk (-p.1) p.2 <= N
  -- it will be greater than absVal q.
  have h_bound : ℤ₀cls.abs p.1 ≤ ℤ₀cls.ofNat (add (div (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val) 𝟙) * ℤ₀cls.ofNat p.2.val := by
    -- ℤ₀cls.abs p.1 = ofNat (toNat (abs p.1))
    have h_nat_le := le_div_add_one_mul (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val p.2.property
    calc ℤ₀cls.abs p.1 = ℤ₀cls.ofNat (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) := ℤ₀cls.nonneg_eq_ofNat (ℤ₀cls.abs_nonneg p.1)
         _ ≤ ℤ₀cls.ofNat (mul (add (div (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val) 𝟙) p.2.val) := ℤ₀cls.le_ofNat_iff.mpr h_nat_le
         _ = ℤ₀cls.ofNat (add (div (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val) 𝟙) * ℤ₀cls.ofNat p.2.val := ℤ₀cls.ofNat_mul (add (div (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val) 𝟙) p.2.val
  
  -- We want absVal (mk p.1 p.2) <= mk (ofNat (...)) den1
  -- By cases on 0 <= q
  let den1 : ℕ₁ := ⟨𝟙, Peano.Axioms.succ_neq_zero 𝟘⟩
  by_cases h : (0 : ℚ₀cls) ≤ (mk p.1 p.2 : ℚ₀cls)
  · change absVal (mk p.1 p.2 : ℚ₀cls) ≤ _
    rw [absVal_of_nonneg h]
    -- we want mk p.1 p.2 <= mk (ofNat (...)) den1
    have h_den : den1.val = 𝟙 := rfl
    show Mul.mul p.1 (ℤ₀cls.ofNat den1.val) ≤ Mul.mul (ℤ₀cls.ofNat (add (div (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val) 𝟙)) (ℤ₀cls.ofNat p.2.val)
    rw [h_den, ℤ₀cls.ofNat_one, ℤ₀cls.mul_one]
    have hp_le_abs : p.1 ≤ ℤ₀cls.abs p.1 := le_abs_self p.1
    exact ℤ₀cls.le_trans hp_le_abs h_bound
  · have hl : (mk p.1 p.2 : ℚ₀cls) ≤ 0 := by
      cases le_total 0 (mk p.1 p.2 : ℚ₀cls) with
      | inl h1 => exact absurd h1 h
      | inr h2 => exact h2
    change absVal (mk p.1 p.2 : ℚ₀cls) ≤ _
    rw [absVal_of_nonpos hl]
    -- we want -mk p.1 p.2 <= mk (ofNat (...)) den1
    -- -mk p.1 p.2 = mk (-p.1) p.2
    have hneg : - (mk p.1 p.2 : ℚ₀cls) = mk (-p.1) p.2 := rfl
    rw [hneg]
    have h_den : den1.val = 𝟙 := rfl
    show Mul.mul (-p.1) (ℤ₀cls.ofNat den1.val) ≤ Mul.mul (ℤ₀cls.ofNat (add (div (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val) 𝟙)) (ℤ₀cls.ofNat p.2.val)
    rw [h_den, ℤ₀cls.ofNat_one, ℤ₀cls.mul_one]
    have hp_neg_le_abs : -p.1 ≤ ℤ₀cls.abs p.1 := neg_le_abs_self p.1
    exact ℤ₀cls.le_trans hp_neg_le_abs h_bound

end ℚ₀cls