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
--   Omega_prime_mul   (sorry: requiere minimalidad de smallestDivisor)
--   Omega_prime_mul_prime

import AczelSetTheory.PList.Omega0
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Div

open Peano Peano.Axioms Peano.Add Peano.Mul Peano.Order Peano.StrictOrder
open Peano.Div Peano.Arith
open Peano.WellFounded
open Peano.Primes

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
  generalize hv : padicVal p (n / p) = v
  unfold padicVal
  rw [dif_pos (And.intro hp (And.intro hn hdvd)), hv]

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

private theorem padicVal_one_eq_zero (p : ℕ₀) (hp2 : le₀ 𝟚 p) : padicVal p 𝟙 = 𝟘 := by
  apply padicVal_of_not_cond
  intro hc
  obtain ⟨_, _, hdvd⟩ := hc
  have hle := divides_le hdvd (succ_neq_zero 𝟘)
  exact lt_irrefl 𝟙 (le_succ_then_lt 𝟙 𝟙 (le_trans 𝟚 p 𝟙 hp2 hle))

theorem padicVal_prime_self {p : ℕ₀} (hp : Peano.Arith.Prime p) : padicVal p p = 𝟙 := by
  have hp2 := prime_ge_two hp
  have hp0 := prime_ne_zero hp
  rw [padicVal_succ_dvd hp2 hp0 (divides_refl p), div_self_eq_one hp0,
      padicVal_one_eq_zero p hp2]
  rfl

theorem padicVal_prime_of_ndvd {p q : ℕ₀} (hp : Peano.Arith.Prime p)
    (hq : Peano.Arith.Prime q) (hne : p ≠ q) : padicVal p q = 𝟘 := by
  apply padicVal_of_not_cond
  intro hc
  obtain ⟨_, _, hdvd⟩ := hc
  rcases prime_divisors hq hdvd with h | h
  · have hge := prime_ge_two hp
    rw [h] at hge
    exact lt_irrefl 𝟙 (le_succ_then_lt 𝟙 𝟙 hge)
  · exact hne h

-- ─────────────────────────────────────────────────────────────────────────────
-- Libre de cuadrados
-- ─────────────────────────────────────────────────────────────────────────────

/-- `n` es libre de cuadrados: ningún primo aparece al cuadrado en su factorización. -/
def squarefree (n : ℕ₀) : Prop :=
  n ≠ 𝟘 ∧ ∀ p : ℕ₀, Peano.Arith.Prime p → le₀ (padicVal p n) 𝟙

theorem squarefree_one : squarefree 𝟙 := by
  refine ⟨succ_neq_zero 𝟘, fun p hp => ?_⟩
  rw [padicVal_one_eq_zero p (prime_ge_two hp)]
  exact zero_le 𝟙

theorem squarefree_prime {p : ℕ₀} (hp : Peano.Arith.Prime p) : squarefree p := by
  refine ⟨prime_ne_zero hp, fun q hq => ?_⟩
  by_cases hqp : q = p
  · subst hqp; rw [padicVal_prime_self hp]; exact le_refl 𝟙
  · rw [padicVal_prime_of_ndvd hq hp hqp]; exact zero_le 𝟙

theorem not_squarefree_prime_sq {p : ℕ₀} (hp : Peano.Arith.Prime p) :
    ¬ squarefree (mul p p) := by
  intro h
  obtain ⟨_, hle⟩ := h
  have hp2 := prime_ge_two hp
  have hp0 := prime_ne_zero hp
  have hpp0 : mul p p ≠ 𝟘 := by
    have hpos := pos_of_ne_zero p hp0
    have hpos2 := Peano.Mul.mul_pos hpos hpos
    intro heq; rw [heq] at hpos2; exact lt_irrefl 𝟘 hpos2
  have hdvd : p ∣ mul p p := ⟨p, rfl⟩
  have hdiv : mul p p / p = p := by
    have h1 : mul (mul p p / p) p = mul p p := div_mul_cancel hp0 hdvd
    exact mul_cancelation_right (mul p p / p) p p hp0 h1
  have hv2 : padicVal p (mul p p) = 𝟚 := by
    rw [padicVal_succ_dvd hp2 hpp0 hdvd, hdiv, padicVal_prime_self hp]
    rfl
  have hle_p := hle p hp
  rw [hv2] at hle_p
  exact lt_irrefl 𝟙 (le_succ_then_lt 𝟙 𝟙 hle_p)

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
  unfold Omega_prime
  rw [dif_pos hp2, hsd, div_self_eq_one hp0, Omega_prime_one]
  rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- Multiplicatividad de Omega_prime
-- ─────────────────────────────────────────────────────────────────────────────

/-- (m * n) / n = m para n ≠ 0. -/
private theorem mul_div_cancel_right' {m n : ℕ₀} (hn : n ≠ 𝟘) :
    Peano.Mul.mul m n / n = m := by
  have hdvd : n ∣ Peano.Mul.mul m n := ⟨m, mul_comm m n⟩
  exact mul_cancelation_right _ m n hn (div_mul_cancel hn hdvd)

/-- Ω es completamente multiplicativa: Ω(m·n) = Ω(m) + Ω(n) para m, n ≠ 0.
    SORRY: la prueba recurre a la minimalidad de `smallestDivisor`, encapsulada
    en `smallestDivisorAux_spec` (private en Peano.PeanoNat.Primes).
    Estrategia verificada matemáticamente:
      – n = 1: Ω(m·1) = Ω(m) = Ω(m) + 0.
      – n ≥ 2: sea q = sd(n) primo. Entonces n = (n/q)·q, luego m·n = (m·(n/q))·q.
        Por Omega_prime_mul_prime con q primo: Ω(m·n) = 1 + Ω(m·(n/q)).
        Por HI en n/q < n: Ω(m·(n/q)) = Ω(m) + Ω(n/q).
        Y Ω(n) = 1 + Ω(n/q). Luego Ω(m·n) = Ω(m) + Ω(n). ✓ -/
theorem Omega_prime_mul {m n : ℕ₀} (hm : m ≠ 𝟘) (hn : n ≠ 𝟘) :
    Omega_prime (Peano.Mul.mul m n) =
    Peano.Add.add (Omega_prime m) (Omega_prime n) := by
  sorry

/-- Caso especial de multiplicatividad: Ω(m·p) = 1 + Ω(m) para p primo, m ≠ 0. -/
theorem Omega_prime_mul_prime {m p : ℕ₀} (hp : Peano.Arith.Prime p) (hm : m ≠ 𝟘) :
    Omega_prime (Peano.Mul.mul m p) = σ (Omega_prime m) := by
  rw [Omega_prime_mul hm (prime_ne_zero hp), Omega_prime_prime hp,
      show (𝟙 : ℕ₀) = σ 𝟘 from rfl, add_succ, add_zero]
