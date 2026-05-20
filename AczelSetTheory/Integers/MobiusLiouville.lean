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
--   negOnePow_zero, negOnePow_succ, negOnePow_one
--   mobius_one, mobius_prime, mobius_prime_sq
--   liouville_one, liouville_prime

import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.PadicVal

namespace ℤ₀

open Peano Peano.Axioms Peano.Add Peano.Mul Peano.Order Peano.StrictOrder hiding Prime
open Peano.Arith hiding Prime
open Peano.Primes hiding Prime

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
  -- Neg.neg negOne = mk (negRaw (𝟘, 𝟙)) = mk (𝟙, 𝟘) = 1 definitionally
  rfl

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

end ℤ₀
