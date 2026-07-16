/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/IsCauchy.lean
-- Sucesiones de Cauchy diádicas sobre ℚ₀cls (M3B).
--
-- API entregada:
--   pow2              : ℕ₀ → ℚ₀cls             -- 1/2^n
--   IsCauchy          : (ℕ₀ → ℚ₀cls) → Prop   -- cond. simétrica con min
--   IsCauchy₂         : (ℕ₀ → ℚ₀cls) → Prop   -- cond. asimétrica (n ≤ m)
--   isCauchy_iff_isCauchy₂                   -- equivalencia
--
-- Diseño:
--   IsCauchy  es la definición principal: ∀ n m, |f n - f m| ≤ 1/2^(min n m)
--   IsCauchy₂ es la alternativa asimétrica: ∀ n m, n ≤ m → |f m - f n| ≤ 1/2^n
--   La condición simétrica evita llevar hipótesis de orden y es directamente
--   compatible con absVal_sub_comm.
--
-- Dependencies: AczelSetTheory.Rationals.Basic
--               AczelSetTheory.Rationals.AbsVal
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.AbsVal
import Peano.PeanoNat.Combinatorics.Pow

namespace ℚ₀cls

-- ============================================================
-- Sección 1: pow2 — potencias diádicas inversas 1/2^n
-- ============================================================

/-- `pow2 n = 1/2^n` en ℚ₀cls. Construido directamente como el racional con
numerador 1 y denominador 2^n. -/
def pow2_den (n : ℕ₀) : ℕ₁ :=
  ⟨Peano.Pow.pow (σ (σ 𝟘)) n, Peano.Pow.pow_ne_zero (by decide) n⟩

-- pow2 n = 1 / 2^n
theorem pow2_den_succ (n : ℕ₀) : (pow2_den (σ n)).val = Peano.Mul.mul (pow2_den n).val (σ (σ 𝟘)) := rfl

def pow2 (n : ℕ₀) : ℚ₀cls :=
  ℚ₀cls.mk (ℤ₀cls.ofNat (σ 𝟘)) (pow2_den n)

theorem pow2_nonneg (n : ℕ₀) : (0 : ℚ₀cls) ≤ pow2 n := by
  show Mul.mul (0:ℤ₀cls) (ℤ₀cls.ofNat (pow2_den n).val) ≤ Mul.mul (ℤ₀cls.ofNat (σ 𝟘)) (ℤ₀cls.ofNat 𝟙)
  rw [ℤ₀cls.zero_mul]
  have h1 : Mul.mul (ℤ₀cls.ofNat (σ 𝟘)) (ℤ₀cls.ofNat 𝟙) = ℤ₀cls.ofNat (σ 𝟘) := by
    rw [← ℤ₀cls.ofNat_mul]
    have h1_1 : Peano.Mul.mul (σ 𝟘) 𝟙 = σ 𝟘 := Peano.Mul.mul_one _
    rw [h1_1]
  rw [h1]
  exact ℤ₀cls.zero_le_ofNat _

theorem pow2_succ_add (n : ℕ₀) : Add.add (pow2 (σ n)) (pow2 (σ n)) = pow2 n := by
  dsimp [pow2]
  rw [ℚ₀cls.add_mk, ℚ₀cls.mk_eq_iff]
  
  -- left side right_distrib
  have h_distrib : Add.add (Mul.mul (ℤ₀cls.ofNat (σ 𝟘)) (ℤ₀cls.ofNat (ℚ₀cls.pow2_den (σ n)).val)) (Mul.mul (ℤ₀cls.ofNat (σ 𝟘)) (ℤ₀cls.ofNat (ℚ₀cls.pow2_den (σ n)).val)) = Mul.mul (Add.add (ℤ₀cls.ofNat (σ 𝟘)) (ℤ₀cls.ofNat (σ 𝟘))) (ℤ₀cls.ofNat (ℚ₀cls.pow2_den (σ n)).val) := by
    rw [ℤ₀cls.right_distrib]
  rw [h_distrib]
  
  -- 1 + 1 = 2
  have h_add : Add.add (ℤ₀cls.ofNat (σ 𝟘)) (ℤ₀cls.ofNat (σ 𝟘)) = ℤ₀cls.ofNat (σ (σ 𝟘)) := by
    rw [← ℤ₀cls.ofNat_add]
    rfl
  rw [h_add]
  
  -- right side 1 * X = X
  have h_one_mul : Mul.mul (ℤ₀cls.ofNat (σ 𝟘)) (ℤ₀cls.ofNat (mulDen (ℚ₀cls.pow2_den (σ n)) (ℚ₀cls.pow2_den (σ n))).val) = ℤ₀cls.ofNat (mulDen (ℚ₀cls.pow2_den (σ n)) (ℚ₀cls.pow2_den (σ n))).val := by
    rw [← ℤ₀cls.ofNat_mul]
    apply congrArg
    exact Peano.Mul.one_mul _
  rw [h_one_mul]

  -- rewrite A = B * 2
  have h_A : ℤ₀cls.ofNat (ℚ₀cls.pow2_den (σ n)).val = Mul.mul (ℤ₀cls.ofNat (ℚ₀cls.pow2_den n).val) (ℤ₀cls.ofNat (σ (σ 𝟘))) := by
    rw [ℚ₀cls.pow2_den_succ, ℤ₀cls.ofNat_mul]
  rw [h_A]

  -- rewrite right side mulDen X X = X * X
  have h_mulDen : ℤ₀cls.ofNat (mulDen (ℚ₀cls.pow2_den (σ n)) (ℚ₀cls.pow2_den (σ n))).val = Mul.mul (ℤ₀cls.ofNat (ℚ₀cls.pow2_den (σ n)).val) (ℤ₀cls.ofNat (ℚ₀cls.pow2_den (σ n)).val) := by
    change ℤ₀cls.ofNat (Peano.Mul.mul (ℚ₀cls.pow2_den (σ n)).val (ℚ₀cls.pow2_den (σ n)).val) = _
    rw [ℤ₀cls.ofNat_mul]
  rw [h_mulDen]
  rw [h_A]

  let two := ℤ₀cls.ofNat (σ(σ𝟘))
  let B := ℤ₀cls.ofNat (ℚ₀cls.pow2_den n).val
  
  have h_left : Mul.mul (Mul.mul two (Mul.mul B two)) B = Mul.mul (Mul.mul two two) (Mul.mul B B) := by
    rw [ℤ₀cls.mul_comm B two]
    rw [← ℤ₀cls.mul_assoc two two B]
    rw [ℤ₀cls.mul_assoc (Mul.mul two two) B B]
  
  have h_right : Mul.mul (Mul.mul B two) (Mul.mul B two) = Mul.mul (Mul.mul two two) (Mul.mul B B) := by
    rw [← ℤ₀cls.mul_assoc (Mul.mul B two) B two]
    have h_inner : Mul.mul (Mul.mul B two) B = Mul.mul (Mul.mul B B) two := by
      rw [ℤ₀cls.mul_assoc B two B]
      rw [ℤ₀cls.mul_comm two B]
      rw [← ℤ₀cls.mul_assoc B B two]
    rw [h_inner]
    rw [ℤ₀cls.mul_assoc (Mul.mul B B) two two]
    rw [ℤ₀cls.mul_comm (Mul.mul B B) (Mul.mul two two)]

  rw [h_left, h_right]

theorem pow2_add (n m : ℕ₀) : pow2 (Peano.Add.add n m) = Mul.mul (pow2 n) (pow2 m) := by
  dsimp [pow2]
  rw [ℚ₀cls.mul_mk, ℚ₀cls.mk_eq_iff]
  have h_one : ℤ₀cls.ofNat (σ 𝟘) = 1 := ℤ₀cls.ofNat_one
  rw [h_one]
  rw [ℤ₀cls.one_mul, ℤ₀cls.one_mul, ℤ₀cls.one_mul]
  apply congrArg ℤ₀cls.ofNat
  exact Eq.symm (Peano.Pow.pow_add_eq_mul_pow (σ (σ 𝟘)) n m)

theorem pow2_le_one (k : ℕ₀) : pow2 k ≤ ofNat₀ 𝟙 := by
  have h_pow2_def : pow2 k = ℚ₀cls.mk (ℤ₀cls.ofNat (σ 𝟘)) (pow2_den k) := rfl
  have h_one_def : ofNat₀ 𝟙 = ℚ₀cls.mk (ℤ₀cls.ofNat (σ 𝟘)) den1 := rfl
  rw [h_pow2_def, h_one_def, ℚ₀cls.mk_le_mk]
  have h_den1 : ℤ₀cls.ofNat den1.val = 1 := rfl
  have h_num : ℤ₀cls.ofNat (σ 𝟘) = 1 := rfl
  rw [h_num, h_den1, ℤ₀cls.mul_one, ℤ₀cls.one_mul]
  have h_den_pos : 1 ≤ ℤ₀cls.ofNat (pow2_den k).val := by
    change ℤ₀cls.ofNat 𝟙 ≤ ℤ₀cls.ofNat (pow2_den k).val
    rw [ℤ₀cls.le_ofNat_iff]
    have h_ne_0 := (pow2_den k).property
    match h_val : (pow2_den k).val with
    | 𝟘 => rw [h_val] at h_ne_0; exact False.elim (h_ne_0 rfl)
    | σ y =>
      change Peano.Order.le₀ 𝟙 (σ y)
      exact Peano.Order.succ_le_succ_if (Peano.Order.zero_le y)
  exact h_den_pos
theorem pow2_ne_zero (k : ℕ₀) : ℚ₀cls.pow2 k ≠ 0 := by
  intro h
  have h_pow2_def : ℚ₀cls.pow2 k = ℚ₀cls.mk (ℤ₀cls.ofNat (σ 𝟘)) (ℚ₀cls.pow2_den k) := rfl
  have h_zero_def : (0 : ℚ₀cls) = ℚ₀cls.mk (ℤ₀cls.ofNat 𝟘) den1 := rfl
  rw [h_pow2_def, h_zero_def] at h
  have hz := ℚ₀cls.mk_eq_zero_iff.mp h
  have hz_inj := ℤ₀cls.ofNat_injective hz
  exact Peano.Axioms.succ_neq_zero 𝟘 hz_inj

theorem pow2_bound (K : ℕ₀) : Mul.mul (ofNat₀ K) (pow2 K) ≤ ofNat₀ 𝟙 := by
  rw [ofNat₀_eq_mk K, ofNat₀_eq_mk 𝟙]
  dsimp [pow2]
  rw [ℚ₀cls.mul_mk, ℚ₀cls.mk_le_mk]
  have h_one : ℤ₀cls.ofNat (σ 𝟘) = 1 := ℤ₀cls.ofNat_one
  rw [h_one]
  have h_den1 : ℤ₀cls.ofNat den1.val = 1 := ℤ₀cls.ofNat_one
  rw [h_den1]
  rw [ℤ₀cls.mul_one, ℤ₀cls.mul_one, ℤ₀cls.ofNat_one, ℤ₀cls.one_mul]
  rw [ℤ₀cls.le_ofNat_iff]
  have h_den1_val : den1.val = 𝟙 := rfl
  have h_mul_den : (mulDen den1 (pow2_den K)).val = Peano.Mul.mul den1.val (pow2_den K).val := rfl
  rw [h_mul_den, h_den1_val]
  have h_one_mul : Peano.Mul.mul 𝟙 (pow2_den K).val = (pow2_den K).val := Peano.Mul.one_mul (pow2_den K).val
  rw [h_one_mul]
  exact Peano.Pow.n_le_two_pow_n K

-- ============================================================
-- Sección 2: Definiciones de Cauchy
-- ============================================================

/-- Condición de Cauchy diádica **simétrica**: para toda sucesión f : ℕ₀ → ℚ₀cls,
`|f n - f m| ≤ 1/2^(min n m)`.

Es la definición principal porque no requiere hipótesis de orden entre n y m,
y es compatible con `absVal_sub_comm`. -/
def IsCauchy (f : ℕ₀ → ℚ₀cls) : Prop :=
  ∀ n m : ℕ₀, absVal (f n - f m) ≤ pow2 (Peano.Lattice.min n m)

/-- Condición de Cauchy diádica **asimétrica**: para n ≤ m, `|f m - f n| ≤ 1/2^n`.

Alternativa más próxima a la presentación clásica "la sucesión converge a ritmo
diádico". Equivalente a `IsCauchy` (ver `isCauchy_iff_isCauchy₂`). -/
def IsCauchy₂ (f : ℕ₀ → ℚ₀cls) : Prop :=
  ∀ n m : ℕ₀, n ≤ m → absVal (f m - f n) ≤ pow2 n

-- ============================================================
-- Sección 3: Equivalencia entre las dos condiciones
-- ============================================================

/-- `IsCauchy f ↔ IsCauchy₂ f`.

**Idea**: la condición simétrica se reduce a la asimétrica usando
`le_then_min_eq_left` (cuando n ≤ m, `min n m = n`) y `absVal_sub_comm`
(que intercambia los argumentos de la diferencia). -/
theorem isCauchy_iff_isCauchy₂ (f : ℕ₀ → ℚ₀cls) : IsCauchy f ↔ IsCauchy₂ f := by
  constructor
  · -- IsCauchy → IsCauchy₂
    intro h n m hnm
    have hmin : Peano.Lattice.min n m = n := Peano.Lattice.le_then_min_eq_left n m hnm
    calc absVal (f m - f n)
        = absVal (f n - f m)             := absVal_sub_comm (f m) (f n)
      _ ≤ pow2 (Peano.Lattice.min n m)  := h n m
      _ = pow2 n                         := by rw [hmin]
  · -- IsCauchy₂ → IsCauchy
    intro h n m
    rcases Peano.Order.le_total n m with hnm | hmn
    · -- caso n ≤ m: min n m = n
      have hmin : Peano.Lattice.min n m = n := Peano.Lattice.le_then_min_eq_left n m hnm
      calc absVal (f n - f m)
          = absVal (f m - f n)             := absVal_sub_comm (f n) (f m)
        _ ≤ pow2 n                         := h n m hnm
        _ = pow2 (Peano.Lattice.min n m)  := by rw [hmin]
    · -- caso m ≤ n: min n m = m
      have hmin : Peano.Lattice.min n m = m := by
        rw [Peano.Lattice.min_comm]
        exact Peano.Lattice.le_then_min_eq_left m n hmn
      calc absVal (f n - f m)
          ≤ pow2 m                         := h m n hmn
        _ = pow2 (Peano.Lattice.min n m)  := by rw [hmin]

end ℚ₀cls
