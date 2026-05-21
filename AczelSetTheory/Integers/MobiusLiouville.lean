/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/MobiusLiouville.lean
-- Función de Möbius μ y función de Liouville λ con valores en ℤ₀.
--
-- Público:
--   ℤ₀.negOnePow  : ℕ₀ → ℤ₀        ((-1)^k)
--   ℤ₀.mobius     : ℕ₀ → ℤ₀        (μ(n))
--   ℤ₀.liouville  : ℕ₀ → ℤ₀        (λ(n))
--
-- Lemas:
--   negOnePow_zero, negOnePow_succ, negOnePow_one, negOnePow_two
--   negOnePow_add, negOnePow_mul_self
--   mobius_one, mobius_prime, mobius_prime_sq
--   mobius_eq_liouville_of_squarefree, mobius_sq
--   liouville_one, liouville_prime, liouville_sq, liouville_ne_zero
--   liouville_mul, liouville_prime_pow

import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.PadicVal

namespace ℤ₀

open Peano Peano.Axioms Peano.Add Peano.Mul Peano.Order Peano.StrictOrder
open Peano.Arith
open Peano.Primes

-- ─────────────────────────────────────────────────────────────────────────────
-- (-1)^k en ℤ₀
-- ─────────────────────────────────────────────────────────────────────────────

/-- Potencia de -1 en ℤ₀ por recursión estructural sobre ℕ₀. -/
def negOnePow (k : ℕ₀) : ℤ₀ :=
  match k with
  | .zero    => 1
  | .succ k' => Neg.neg (negOnePow k')

theorem negOnePow_zero : negOnePow 𝟘 = 1 := rfl

theorem negOnePow_succ (k : ℕ₀) : negOnePow (σ k) = Neg.neg (negOnePow k) := rfl

theorem negOnePow_one : negOnePow 𝟙 = negOne := rfl

theorem negOnePow_two : negOnePow 𝟚 = 1 := by
  show Neg.neg (negOnePow 𝟙) = 1
  rw [negOnePow_one]
  rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- Propiedades algebraicas de negOnePow
-- ─────────────────────────────────────────────────────────────────────────────

private theorem neg_mul_neg (a b : ℤ₀) :
    Mul.mul (Neg.neg a) (Neg.neg b) = Mul.mul a b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem negOnePow_add (a b : ℕ₀) :
    negOnePow (Peano.Add.add a b) = Mul.mul (negOnePow a) (negOnePow b) := by
  induction b with
  | zero =>
    have h0 : Peano.Add.add a 𝟘 = a := by omega₀
    rw [h0, negOnePow_zero, mul_one]
  | succ b ih =>
    have hstep : Peano.Add.add a (σ b) = σ (Peano.Add.add a b) := by omega₀
    rw [hstep, negOnePow_succ, ih, negOnePow_succ]
    exact (mul_neg (negOnePow a) (negOnePow b)).symm

theorem negOnePow_mul_self (k : ℕ₀) :
    Mul.mul (negOnePow k) (negOnePow k) = 1 := by
  induction k with
  | zero      => rw [negOnePow_zero, mul_one]
  | succ k ih =>
    show Mul.mul (Neg.neg (negOnePow k)) (Neg.neg (negOnePow k)) = 1
    rw [neg_mul_neg, ih]

-- ─────────────────────────────────────────────────────────────────────────────
-- Función de Möbius
-- ─────────────────────────────────────────────────────────────────────────────

private noncomputable instance (n : ℕ₀) : Decidable (squarefree n) := Classical.propDecidable _

/-- μ(n) = (-1)^Ω(n) si n es libre de cuadrados, 0 en otro caso. -/
noncomputable def mobius (n : ℕ₀) : ℤ₀ :=
  if squarefree n then negOnePow (Omega_prime n) else 0

-- ─────────────────────────────────────────────────────────────────────────────
-- Función de Liouville
-- ─────────────────────────────────────────────────────────────────────────────

/-- λ(n) = (-1)^Ω(n), donde Ω(n) es el número de factores primos con multiplicidad. -/
noncomputable def liouville (n : ℕ₀) : ℤ₀ :=
  negOnePow (Omega_prime n)

-- ─────────────────────────────────────────────────────────────────────────────
-- Valores en n = 1
-- ─────────────────────────────────────────────────────────────────────────────

theorem mobius_one : mobius 𝟙 = 1 := by
  unfold mobius
  rw [if_pos squarefree_one, Omega_prime_one, negOnePow_zero]

theorem liouville_one : liouville 𝟙 = 1 := by
  unfold liouville
  rw [Omega_prime_one, negOnePow_zero]

-- ─────────────────────────────────────────────────────────────────────────────
-- Valores en primos
-- ─────────────────────────────────────────────────────────────────────────────

theorem mobius_prime {p : ℕ₀} (hp : Peano.Arith.Prime p) : mobius p = negOne := by
  unfold mobius
  rw [if_pos (squarefree_prime hp), Omega_prime_prime hp, negOnePow_one]

theorem liouville_prime {p : ℕ₀} (hp : Peano.Arith.Prime p) : liouville p = negOne := by
  unfold liouville
  rw [Omega_prime_prime hp, negOnePow_one]

-- ─────────────────────────────────────────────────────────────────────────────
-- μ(p²) = 0 (no libre de cuadrados)
-- ─────────────────────────────────────────────────────────────────────────────

theorem mobius_prime_sq {p : ℕ₀} (hp : Peano.Arith.Prime p) : mobius (Peano.Mul.mul p p) = 0 := by
  unfold mobius
  rw [if_neg (not_squarefree_prime_sq hp)]

-- ─────────────────────────────────────────────────────────────────────────────
-- Propiedades algebraicas: liouville y mobius
-- ─────────────────────────────────────────────────────────────────────────────

theorem liouville_sq (n : ℕ₀) : Mul.mul (liouville n) (liouville n) = 1 := by
  unfold liouville; exact negOnePow_mul_self _

theorem liouville_ne_zero (n : ℕ₀) : liouville n ≠ 0 := fun h => by
  have hone := liouville_sq n
  rw [h, zero_mul] at hone
  exact absurd (ofNat_injective (ofNat_zero.trans (hone.trans ofNat_one.symm))) (by omega₀)

theorem mobius_eq_liouville_of_squarefree {n : ℕ₀} (h : squarefree n) :
    mobius n = liouville n := by
  unfold mobius liouville; rw [if_pos h]

theorem mobius_sq (n : ℕ₀) :
    Mul.mul (mobius n) (mobius n) = if squarefree n then 1 else 0 := by
  unfold mobius
  split_ifs with h
  · exact negOnePow_mul_self _
  · exact zero_mul 0

-- ─────────────────────────────────────────────────────────────────────────────
-- Multiplicatividad de liouville
-- ─────────────────────────────────────────────────────────────────────────────

/-- λ es completamente multiplicativa: λ(m·n) = λ(m)·λ(n) para m, n ≠ 0.
    (Usa Omega_prime_mul, que tiene un sorry.) -/
theorem liouville_mul {m n : ℕ₀} (hm : m ≠ 𝟘) (hn : n ≠ 𝟘) :
    liouville (Peano.Mul.mul m n) = Mul.mul (liouville m) (liouville n) := by
  unfold liouville
  rw [Omega_prime_mul hm hn, negOnePow_add]

open Peano.Pow in
/-- λ(p^k) = (-1)^k para p primo. -/
theorem liouville_prime_pow {p k : ℕ₀} (hp : Peano.Arith.Prime p) :
    liouville (Peano.Pow.pow p k) = negOnePow k := by
  induction k with
  | zero => rw [pow_zero, liouville_one, negOnePow_zero]
  | succ k' ih =>
    rw [pow_succ,
        liouville_mul (pow_ne_zero (prime_ne_zero hp) k') (prime_ne_zero hp),
        ih, liouville_prime hp, ← negOnePow_one, ← negOnePow_add]

end ℤ₀
