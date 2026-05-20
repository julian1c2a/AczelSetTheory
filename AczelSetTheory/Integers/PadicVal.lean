/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/PadicVal.lean
-- Valuación p-ádica y funciones aritméticas auxiliares en ℕ₀.
--
-- Público:
--   padicVal   : ℕ₀ → ℕ₀ → ℕ₀      (vₚ(n))
--   squarefree : ℕ₀ → Prop
--   Omega_prime : ℕ₀ → ℕ₀           (Ω(n) = factores primos con multiplicidad)
--
-- Lemas:
--   padicVal_zero_right, padicVal_of_not_cond, padicVal_succ_dvd
--   padicVal_prime_self, padicVal_prime_of_ndvd
--   squarefree_one, squarefree_prime, not_squarefree_prime_sq
--   Omega_prime_zero, Omega_prime_one, Omega_prime_prime

import AczelSetTheory.PList.Omega0
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Div

open Peano Peano.Axioms Peano.Add Peano.Mul Peano.Order Peano.StrictOrder hiding Prime
open Peano.Div Peano.Arith hiding Prime
open Peano.WellFounded
open Peano.Primes hiding Prime

-- ─────────────────────────────────────────────────────────────────────────────
-- Valuación p-ádica
-- ─────────────────────────────────────────────────────────────────────────────

private noncomputable instance (p n : ℕ₀) : Decidable (p ∣ n) := Classical.propDecidable _

/-- Mayor potencia de `p` que divide a `n`. Vale 0 si `p < 2`, `n = 0`, o `p ∤ n`. -/
noncomputable def padicVal (p n : ℕ₀) : ℕ₀ :=
  if h : le₀ 𝟚 p ∧ n ≠ 𝟘 ∧ p ∣ n then σ (padicVal p (n / p))
  else 𝟘
termination_by n
decreasing_by
  exact div_lt_self n p (le_succ_then_lt 𝟙 p h.1) h.2.1

theorem padicVal_zero_right (p : ℕ₀) : padicVal p 𝟘 = 𝟘 := by
  unfold padicVal; exact dif_neg (fun ⟨_, h, _⟩ => h rfl)

theorem padicVal_of_not_cond {p n : ℕ₀}
    (h : ¬ (le₀ 𝟚 p ∧ n ≠ 𝟘 ∧ p ∣ n)) : padicVal p n = 𝟘 := by
  unfold padicVal; exact dif_neg h

theorem padicVal_succ_dvd {p n : ℕ₀} (hp : le₀ 𝟚 p) (hn : n ≠ 𝟘) (hdvd : p ∣ n) :
    padicVal p n = σ (padicVal p (n / p)) := by
  unfold padicVal; exact dif_pos ⟨hp, hn, hdvd⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- Lema auxiliar: p / p = 1
-- ─────────────────────────────────────────────────────────────────────────────

private theorem div_self_eq_one {p : ℕ₀} (hp : p ≠ 𝟘) : p / p = 𝟙 := by
  have h1 : mul (p / p) p = p := div_mul_cancel hp (divides_refl p)
  have h2 : mul 𝟙 p = p := one_mul p
  exact mul_cancelation_right (p / p) 𝟙 p hp (h1.trans h2.symm)

-- ─────────────────────────────────────────────────────────────────────────────
-- Valuación de un primo
-- ─────────────────────────────────────────────────────────────────────────────

theorem padicVal_prime_self {p : ℕ₀} (hp : Peano.Arith.Prime p) : padicVal p p = 𝟙 := by
  have hp2 := prime_ge_two hp
  have hp0 := prime_ne_zero hp
  rw [padicVal_succ_dvd hp2 hp0 (divides_refl p), div_self_eq_one hp0]
  unfold padicVal; exact dif_neg (fun ⟨_, h, _⟩ => h rfl)

theorem padicVal_prime_of_ndvd {p q : ℕ₀} (hp : Peano.Arith.Prime p) (hq : Peano.Arith.Prime q) (hne : p ≠ q) :
    padicVal p q = 𝟘 := by
  apply padicVal_of_not_cond
  intro ⟨_, _, hdvd⟩
  rcases prime_divisors hq hdvd with h | h
  · have := prime_ge_two hp; omega₀
  · exact hne h

-- ─────────────────────────────────────────────────────────────────────────────
-- Libre de cuadrados
-- ─────────────────────────────────────────────────────────────────────────────

/-- `n` es libre de cuadrados: ningún primo aparece al cuadrado en su factorización. -/
def squarefree (n : ℕ₀) : Prop :=
  n ≠ 𝟘 ∧ ∀ p : ℕ₀, Peano.Arith.Prime p → le₀ (padicVal p n) 𝟙

theorem squarefree_one : squarefree 𝟙 := by
  refine ⟨by omega₀, fun p hp => ?_⟩
  have hv : padicVal p 𝟙 = 𝟘 := by
    apply padicVal_of_not_cond
    intro ⟨hp2, _, hdvd⟩
    have hle := divides_le hdvd (by omega₀ : 𝟙 ≠ 𝟘)
    have := prime_ge_two hp
    omega₀
  rw [hv]; omega₀

theorem squarefree_prime {p : ℕ₀} (hp : Peano.Arith.Prime p) : squarefree p := by
  refine ⟨prime_ne_zero hp, fun q hq => ?_⟩
  by_cases hqp : q = p
  · subst hqp; rw [padicVal_prime_self hp]; omega₀
  · rw [padicVal_prime_of_ndvd hq hp (Ne.symm hqp)]; omega₀

theorem not_squarefree_prime_sq {p : ℕ₀} (hp : Peano.Arith.Prime p) : ¬ squarefree (mul p p) := by
  intro ⟨_, hle⟩
  have hp2 := prime_ge_two hp
  have hp0 := prime_ne_zero hp
  have hpp0 : mul p p ≠ 𝟘 := by
    have hpos := pos_of_ne_zero p hp0
    have hpos2 := Peano.Mul.mul_pos hpos hpos
    intro h; rw [h] at hpos2; exact lt_irrefl hpos2
  have hdvd : p ∣ mul p p := ⟨p, rfl⟩
  have hdiv : mul p p / p = p := by
    have h1 : mul (mul p p / p) p = mul p p := div_mul_cancel hp0 hdvd
    exact mul_cancelation_right (mul p p / p) p p hp0 h1
  have hv2 : padicVal p (mul p p) = 𝟚 := by
    rw [padicVal_succ_dvd hp2 hpp0 hdvd, hdiv, padicVal_prime_self hp]
  have := hle p hp
  rw [hv2] at this
  exact le_succ_then_lt 𝟙 𝟙 this

-- ─────────────────────────────────────────────────────────────────────────────
-- Ω(n): número de factores primos con multiplicidad
-- ─────────────────────────────────────────────────────────────────────────────

/-- Número de factores primos de `n` contados con multiplicidad.
    Ω(0) = Ω(1) = 0, Ω(p) = 1, Ω(p·m) = 1 + Ω(m). -/
noncomputable def Omega_prime (n : ℕ₀) : ℕ₀ :=
  if h : le₀ 𝟚 n then
    σ (Omega_prime (n / smallestDivisor n))
  else 𝟘
termination_by n
decreasing_by
  have hp2 : le₀ 𝟚 (smallestDivisor n) := smallestDivisor_ge_two h
  have hn0 : n ≠ 𝟘 := by intro h0; subst h0; exact le_succ_then_lt 𝟙 𝟘 h
  exact div_lt_self n (smallestDivisor n) (le_succ_then_lt 𝟙 (smallestDivisor n) hp2) hn0

theorem Omega_prime_zero : Omega_prime 𝟘 = 𝟘 := by
  unfold Omega_prime; exact dif_neg (fun h => le_succ_then_lt 𝟙 𝟘 h)

theorem Omega_prime_one : Omega_prime 𝟙 = 𝟘 := by
  unfold Omega_prime; exact dif_neg (fun h => le_succ_then_lt 𝟙 𝟙 h)

theorem Omega_prime_prime {p : ℕ₀} (hp : Peano.Arith.Prime p) : Omega_prime p = 𝟙 := by
  have hp2 := prime_ge_two hp
  have hp0 := prime_ne_zero hp
  have hsd : smallestDivisor p = p := prime_imp_smallestDivisor_eq_self hp
  have h1 : Omega_prime p = σ (Omega_prime (p / smallestDivisor p)) := by
    show (if h : le₀ 𝟚 p then σ (Omega_prime (p / smallestDivisor p)) else 𝟘) =
          σ (Omega_prime (p / smallestDivisor p))
    exact dif_pos hp2
  rw [h1, hsd, div_self_eq_one hp0, Omega_prime_one]
  rfl
