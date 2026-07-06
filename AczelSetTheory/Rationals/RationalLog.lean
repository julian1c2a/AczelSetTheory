/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/RationalLog.lean
-- Logaritmo de un racional `r > 0` como sucesión de Cauchy de ℚ₀, por la serie
-- del `artanh` con reducción de argumento:
--
--   ln r = ln n + 2·Σ_{k≥0} u^(2k+1)/(2k+1),   u = (r-n)/(r+n),   n ∈ ℕ elegido.
--
-- Si `|u| ≤ 1/2` (garantizado eligiendo `n ≈ r`), las sumas parciales cumplen la
-- cota diádica directamente y `isCauchy_of_dyadic_step` da Cauchy.
--
-- ESTADO: base (definiciones + puente `(1/2)^m = 1/2^m` + cota geométrica).
--
-- Dependencies: Rationals.PowOrder, Rationals.Bisection, Rationals.Inv
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.PowOrder
import AczelSetTheory.Rationals.Bisection
import AczelSetTheory.Rationals.Inv

namespace ℚ₀

-- ============================================================
-- Sección 1: Puente entre pow2 y pow (1/2)
-- ============================================================

/-- `1/2^0 = 1`. -/
theorem pow2_zero : pow2 𝟘 = 1 := by
  show mk (ℤ₀.ofNat (σ 𝟘)) (pow2_den 𝟘) = 1
  have hden : pow2_den 𝟘 = den1 := by
    apply Subtype.ext
    show Peano.Pow.pow (σ (σ 𝟘)) 𝟘 = 𝟙
    rfl
  rw [hden]
  rfl

/-- `(1/2)^m = 1/2^m`. -/
theorem pow_pow2_one (m : ℕ₀) : pow (pow2 𝟙) m = pow2 m := by
  induction m with
  | zero => rw [pow_zero, pow2_zero]
  | succ k ih =>
    rw [pow_succ, ih]
    show Mul.mul (pow2 𝟙) (pow2 k) = pow2 (σ k)
    rw [← pow2_add]
    congr 1
    show Peano.Add.add 𝟙 k = σ k
    rw [show (𝟙 : ℕ₀) = σ 𝟘 from rfl, Peano.Add.succ_add, Peano.Add.zero_add]

-- ============================================================
-- Sección 2: Cota geométrica de las potencias de |u| ≤ 1/2
-- ============================================================

/-- Si `|u| ≤ 1/2`, entonces `|u|^m ≤ 1/2^m` para todo `m`. -/
theorem pow_absVal_le_pow2 {u : ℚ₀} (hu : absVal u ≤ pow2 𝟙) (m : ℕ₀) :
    pow (absVal u) m ≤ pow2 m := by
  have h := pow_le_pow_left (absVal_nonneg u) hu m
  rwa [pow_pow2_one] at h

-- ============================================================
-- Sección 3: Serie del artanh (definiciones)
-- ============================================================

/-- Exponente/denominador `2j+1` del `j`-ésimo término de la serie del artanh. -/
def oddIdx (j : ℕ₀) : ℕ₀ := σ (Peano.Mul.mul (σ (σ 𝟘)) j)

/-- `j`-ésimo término de la serie del artanh: `u^(2j+1)/(2j+1)`. -/
def artanhTerm (u : ℚ₀) (j : ℕ₀) : ℚ₀ :=
  pow u (oddIdx j) * inv (ofNat₀ (oddIdx j))

/-- Sumas parciales de `Σ_{j=0}^{k} u^(2j+1)/(2j+1)`. -/
def artanhSeq (u : ℚ₀) : ℕ₀ → ℚ₀
  | 𝟘 => artanhTerm u 𝟘
  | σ k => Add.add (artanhSeq u k) (artanhTerm u (σ k))

-- ============================================================
-- Sección 4: Cota de paso y Cauchy de la serie del artanh
-- ============================================================

theorem oddIdx_ne_zero (j : ℕ₀) : oddIdx j ≠ 𝟘 := by
  unfold oddIdx; exact Peano.Axioms.succ_neq_zero _

theorem ofNat₀_ne_zero {m : ℕ₀} (hm : m ≠ 𝟘) : ofNat₀ m ≠ 0 := by
  rw [ofNat₀_eq_mk]; intro h
  exact hm (ℤ₀.ofNat_injective ((mk_eq_zero_iff.mp h).trans ℤ₀.ofNat_zero.symm))

/-- `j ≤ 2j+1`. -/
theorem self_le_oddIdx (j : ℕ₀) : Peano.Order.le₀ j (oddIdx j) := by
  unfold oddIdx
  have h1 : Peano.Order.le₀ j (Peano.Mul.mul (σ (σ 𝟘)) j) := by
    have hm := Peano.Mul.mul_le_mono_right j (show Peano.Order.le₀ 𝟙 (σ (σ 𝟘)) by decide)
    rwa [Peano.Mul.one_mul] at hm
  exact Peano.Order.le_trans _ _ _ h1 (Peano.Order.le_succ_self _)

/-- `1 ≤ ofNat₀ (2j+1)`. -/
theorem one_le_ofNat₀_oddIdx (j : ℕ₀) : (1 : ℚ₀) ≤ ofNat₀ (oddIdx j) := by
  have h : Peano.Order.le₀ 𝟙 (oddIdx j) := by
    unfold oddIdx
    exact Peano.Order.succ_le_succ_if (Peano.Order.zero_le _)
  have h2 := ofNat₀_le_ofNat₀ h
  rwa [show ofNat₀ 𝟙 = (1 : ℚ₀) from rfl] at h2

/-- Cota del `(k+1)`-ésimo término: `|u^(2k+3)/(2k+3)| ≤ 1/2^(k+1)` si `|u| ≤ 1/2`. -/
theorem artanhTerm_bound {u : ℚ₀} (hu : absVal u ≤ pow2 𝟙) (k : ℕ₀) :
    absVal (artanhTerm u (σ k)) ≤ pow2 (σ k) := by
  show absVal (pow u (oddIdx (σ k)) * inv (ofNat₀ (oddIdx (σ k)))) ≤ pow2 (σ k)
  rw [absVal_mul, absVal_pow]
  have hinvnn : 0 ≤ inv (ofNat₀ (oddIdx (σ k))) :=
    inv_nonneg (ofNat₀_nonneg _) (ofNat₀_ne_zero (oddIdx_ne_zero (σ k)))
  rw [absVal_of_nonneg hinvnn]
  have hstep1 : pow (absVal u) (oddIdx (σ k)) * inv (ofNat₀ (oddIdx (σ k)))
              ≤ pow2 (oddIdx (σ k)) * 1 :=
    mul_le_mul (pow_absVal_le_pow2 hu (oddIdx (σ k)))
               (inv_le_one (one_le_ofNat₀_oddIdx (σ k)))
               (pow_nonneg (absVal_nonneg u) _) hinvnn
  rw [mul_one] at hstep1
  exact le_trans hstep1 (pow2_le_of_le (self_le_oddIdx (σ k)))

theorem artanhSeq_step {u : ℚ₀} (hu : absVal u ≤ pow2 𝟙) (k : ℕ₀) :
    absVal (artanhSeq u (σ k) - artanhSeq u k) ≤ pow2 (σ k) := by
  have he : Add.add (artanhSeq u (σ k)) (Neg.neg (artanhSeq u k)) = artanhTerm u (σ k) := by
    show Add.add (Add.add (artanhSeq u k) (artanhTerm u (σ k))) (Neg.neg (artanhSeq u k))
       = artanhTerm u (σ k)
    rw [add_comm (artanhSeq u k) (artanhTerm u (σ k)), add_assoc, add_neg_self, add_zero]
  show absVal (Add.add (artanhSeq u (σ k)) (Neg.neg (artanhSeq u k))) ≤ pow2 (σ k)
  rw [he]
  exact artanhTerm_bound hu k

/-- **La serie del artanh es de Cauchy** cuando `|u| ≤ 1/2`. -/
theorem artanhSeq_isCauchy {u : ℚ₀} (hu : absVal u ≤ pow2 𝟙) : IsCauchy (artanhSeq u) :=
  isCauchy_of_dyadic_step (artanhSeq_step hu)

end ℚ₀
