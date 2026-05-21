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
--   Omega_prime_mul
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

set_option linter.unusedVariables false in
/-- Mayor potencia de `p` que divide a `n`. Vale 0 si `p < 2`, `n = 0`, o `p ∤ n`. -/
def padicVal (p n : ℕ₀) : ℕ₀ :=
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

set_option linter.unusedVariables false in
/-- Número de factores primos de `n` contados con multiplicidad.
    Ω(0) = Ω(1) = 0, Ω(p) = 1, Ω(p·m) = 1 + Ω(m). -/
def Omega_prime (n : ℕ₀) : ℕ₀ :=
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

/-- n / q ≠ 0 cuando q | n, q ≠ 0 y n ≠ 0. -/
private theorem div_ne_zero_of_dvd {n q : ℕ₀} (hq : q ≠ 𝟘) (hdvd : q ∣ n) (hn : n ≠ 𝟘) :
    n / q ≠ 𝟘 := by
  intro h0
  have h := div_mul_cancel hq hdvd
  rw [h0, zero_mul] at h
  exact hn h.symm

/-- Un paso de la definición de Omega_prime: cuando n ≥ 2, Ω(n) = σ(Ω(n / sd(n))). -/
private theorem Omega_prime_step {n : ℕ₀} (hn : le₀ 𝟚 n) :
    Omega_prime n = σ (Omega_prime (n / smallestDivisor n)) := by
  rw [Omega_prime.eq_1, dif_pos hn]

/-- Caso especial de multiplicatividad: Ω(m·p) = 1 + Ω(m) para p primo, m ≠ 0.
    Prueba por inducción fuerte sobre m, sin depender de Omega_prime_mul. -/
theorem Omega_prime_mul_prime {m p : ℕ₀} (hp : Peano.Arith.Prime p) (hm : m ≠ 𝟘) :
    Omega_prime (Peano.Mul.mul m p) = σ (Omega_prime m) := by
  revert hm
  apply strongInductionOn
    (P := fun m => m ≠ 𝟘 → Omega_prime (mul m p) = σ (Omega_prime m)) m
  intro m ih hm
  -- Caso base: m = 1
  by_cases hm1 : m = 𝟙
  · subst hm1; rw [one_mul, Omega_prime_prime hp, Omega_prime_one]; rfl
  -- Caso inductivo: m ≥ 2
  have hp2 := prime_ge_two hp
  have hp0 := prime_ne_zero hp
  have hm2 : le₀ 𝟚 m := by
    rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hm) with h | h
    · exact lt_then_le_succ_wp h
    · exact absurd h.symm hm1
  -- mul m p ≥ 2 (pues p ≥ 2 y m ≥ 1)
  have hmn2 : le₀ 𝟚 (mul m p) :=
    le_trans 𝟚 p (mul m p) hp2 (mul_le_left p m hm)
  -- Sea q = sd(mul m p)
  have hq_prime := smallestDivisor_prime hmn2
  have hq2      := smallestDivisor_ge_two hmn2
  have hq0      : smallestDivisor (mul m p) ≠ 𝟘 := prime_ne_zero hq_prime
  have hq_dvd   := smallestDivisor_dvd hmn2
  -- Por prime_dvd_mul: q | m ó q | p
  rcases prime_dvd_mul hq_prime hq_dvd with hqm | hqp
  · -- ── Caso q | m ──────────────────────────────────────────────────────────
    -- sd(m) = q: minimalidad cruzada
    have hsdm_eq : smallestDivisor m = smallestDivisor (mul m p) := by
      apply le_antisymm
      · -- sd(m) ≤ sd(m*p): q es divisor primo de m
        exact smallestDivisor_le_of_prime_dvd hm2 hq_prime hqm
      · -- sd(m*p) ≤ sd(m): sd(m) | m*p (via sd(m) | m | m*p)
        exact smallestDivisor_le_of_prime_dvd hmn2 (smallestDivisor_prime hm2)
          (divides_trans (smallestDivisor_dvd hm2) ⟨p, rfl⟩)
    -- m/q < m y m/q ≠ 0
    have hq_gt1 : lt₀ 𝟙 (smallestDivisor (mul m p)) := le_succ_then_lt 𝟙 _ hq2
    have hmq_lt : lt₀ (m / smallestDivisor (mul m p)) m :=
      div_lt_self m _ hq_gt1 hm
    have hmq0 : m / smallestDivisor (mul m p) ≠ 𝟘 :=
      div_ne_zero_of_dvd hq0 hqm hm
    -- mul m p / q = mul (m/q) p
    have hdiv_eq : mul m p / smallestDivisor (mul m p) =
        mul (m / smallestDivisor (mul m p)) p :=
      mul_div_of_dvd_left hq0 hqm p
    -- IH: Omega_prime(mul (m/q) p) = σ(Omega_prime(m/q))
    have ih_mq := ih _ hmq_lt hmq0
    -- Omega_prime m = σ(Omega_prime(m/q))
    have hOm : Omega_prime m = σ (Omega_prime (m / smallestDivisor (mul m p))) := by
      have hOm' : Omega_prime m = σ (Omega_prime (m / smallestDivisor m)) :=
        Omega_prime_step hm2
      rw [hsdm_eq] at hOm'; exact hOm'
    -- Ω(m*p) = σ(Ω((m/q)*p)) = σ(σ(Ω(m/q))) = σ(Ω(m))
    rw [Omega_prime_step hmn2, hdiv_eq, ih_mq, hOm]
  · -- ── Caso q | p → q = p ──────────────────────────────────────────────────
    rcases prime_divisors hp hqp with h1 | heq
    · -- q = 1: contradicción con q ≥ 2
      rw [h1] at hq2
      exact absurd (le_succ_then_lt 𝟙 𝟙 hq2) (lt_irrefl 𝟙)
    · -- q = p: sd(m*p) = p, y mul m p / p = m
      rw [Omega_prime_step hmn2, heq, mul_div_cancel_right' hp0]

/-- Ω es completamente multiplicativa: Ω(m·n) = Ω(m) + Ω(n) para m, n ≠ 0.
    Prueba por inducción fuerte sobre n, usando Omega_prime_mul_prime. -/
theorem Omega_prime_mul {m n : ℕ₀} (hm : m ≠ 𝟘) (hn : n ≠ 𝟘) :
    Omega_prime (Peano.Mul.mul m n) =
    Peano.Add.add (Omega_prime m) (Omega_prime n) := by
  revert hn
  apply strongInductionOn
    (P := fun n => n ≠ 𝟘 → Omega_prime (mul m n) = add (Omega_prime m) (Omega_prime n)) n
  intro n ih hn
  -- Caso base: n = 1
  by_cases hn1 : n = 𝟙
  · subst hn1; rw [mul_one, Omega_prime_one, add_zero]
  -- Caso inductivo: n ≥ 2
  have hn2 : le₀ 𝟚 n := by
    rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hn) with h | h
    · exact lt_then_le_succ_wp h
    · exact absurd h.symm hn1
  -- Sea q = sd(n)
  have hq_prime := smallestDivisor_prime hn2
  have hq2      := smallestDivisor_ge_two hn2
  have hq0      : smallestDivisor n ≠ 𝟘 := prime_ne_zero hq_prime
  have hq_dvd   := smallestDivisor_dvd hn2
  have hq_gt1 : lt₀ 𝟙 (smallestDivisor n) := le_succ_then_lt 𝟙 _ hq2
  -- n/q < n y n/q ≠ 0
  have hnq_lt : lt₀ (n / smallestDivisor n) n := div_lt_self n _ hq_gt1 hn
  have hnq0   : n / smallestDivisor n ≠ 𝟘 := div_ne_zero_of_dvd hq0 hq_dvd hn
  -- n = (n/q) · q  →  m·n = (m·(n/q))·q
  have hn_eq  : n = mul (n / smallestDivisor n) (smallestDivisor n) :=
    (div_mul_cancel hq0 hq_dvd).symm
  have hmn_eq : mul m n = mul (mul m (n / smallestDivisor n)) (smallestDivisor n) :=
    (congrArg (mul m) hn_eq).trans (mul_assoc (n / smallestDivisor n) m (smallestDivisor n)).symm
  -- mul m (n/q) ≠ 0
  have hmnq0 : mul m (n / smallestDivisor n) ≠ 𝟘 :=
    eq_zero_of_mul_eq_zero hm hnq0
  -- Ω(m·n) = Ω((m·(n/q))·q) = σ(Ω(m·(n/q)))
  rw [hmn_eq, Omega_prime_mul_prime hq_prime hmnq0]
  -- IH: Ω(m·(n/q)) = Ω(m) + Ω(n/q)
  rw [ih _ hnq_lt hnq0]
  -- Ω(n) = σ(Ω(n/q))
  have hOn : Omega_prime n = σ (Omega_prime (n / smallestDivisor n)) :=
    Omega_prime_step hn2
  -- σ(Ω(m) + Ω(n/q)) = Ω(m) + σ(Ω(n/q)) = Ω(m) + Ω(n)
  rw [hOn, add_succ]
