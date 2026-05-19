/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/PrimeVN.lean
-- Teoría de primos en HFSet vía transporte desde Peano.
--
-- Predicados HF (definidos vía card):
--   dvd_HF     : HFSet → HFSet → Prop   (a ∣ₕ b)
--   prime_HF   : HFSet → Prop
--   coprime_HF : HFSet → HFSet → Prop   (gcd = 1)
--
-- Lemas de conexión:
--   vN_dvd_iff, vN_prime_iff, vN_coprime_iff
--
-- Teoremas transportados:
--   vN_prime_ne_zero/one, vN_not_prime_zero/one
--   vN_one_lt_prime, vN_prime_ge_two
--   vN_prime_divisors
--   vN_coprime_symm
--   vN_prime_coprime_or_dvd  (tricotomía primo)
--   vN_coprime_dvd_of_dvd_mul  (Lema de Gauss)
--   vN_prime_imp_irreducible, vN_irreducible_imp_prime
--   vN_exists_prime_divisor
--   vN_exists_prime_factorization
--   vN_unique_prime_factorization  (TFA)
--   vN_isPrimeb_iff

import AczelSetTheory.VN.CardVN
import AczelSetTheory.VN.GcdVN
import Peano.PeanoNat.Primes

open Peano Peano.Arith Peano.Primes

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Predicados HFSet para teoría de números
-- ─────────────────────────────────────────────────────────────────

/-- `a` divide a `b` en HFSet (ambos deben ser naturales de Von Neumann). -/
def dvd_HF (a b : HFSet) : Prop :=
  HFSet.isNat a ∧ HFSet.isNat b ∧ HFSet.card a ∣ HFSet.card b

/-- `p` es primo en HFSet (natural de Von Neumann primo). -/
def prime_HF (p : HFSet) : Prop :=
  HFSet.isNat p ∧ Arith.Prime (HFSet.card p)

/-- `a` y `b` son coprimos en HFSet: `gcd(card a, card b) = 1`. -/
def coprime_HF (a b : HFSet) : Prop :=
  HFSet.isNat a ∧ HFSet.isNat b ∧ gcd (HFSet.card a) (HFSet.card b) = 𝟙

-- ─────────────────────────────────────────────────────────────────
-- Lemas de conexión con ℕ₀
-- ─────────────────────────────────────────────────────────────────

theorem vN_dvd_iff {n m : ℕ₀} : dvd_HF (vN n) (vN m) ↔ n ∣ m := by
  simp [dvd_HF, isNat_vN, card_vN]

theorem vN_prime_iff {n : ℕ₀} : prime_HF (vN n) ↔ Arith.Prime n := by
  simp [prime_HF, isNat_vN, card_vN]

theorem vN_coprime_iff {n m : ℕ₀} : coprime_HF (vN n) (vN m) ↔ gcd n m = 𝟙 := by
  simp [coprime_HF, isNat_vN, card_vN]

-- ─────────────────────────────────────────────────────────────────
-- Propiedades básicas de primo
-- ─────────────────────────────────────────────────────────────────

theorem vN_prime_ne_zero {p : ℕ₀} (hp : Arith.Prime p) : vN p ≠ vN 𝟘 :=
  fun h => absurd (vN_injective h) (prime_ne_zero hp)

theorem vN_prime_ne_one {p : ℕ₀} (hp : Arith.Prime p) : vN p ≠ vN 𝟙 :=
  fun h => absurd (vN_injective h) (prime_ne_one hp)

theorem vN_not_prime_zero : ¬ prime_HF (vN 𝟘) := by
  rw [vN_prime_iff]; exact not_prime_zero

theorem vN_not_prime_one : ¬ prime_HF (vN 𝟙) := by
  rw [vN_prime_iff]; exact not_prime_one

theorem vN_one_lt_prime {p : ℕ₀} (hp : Arith.Prime p) : lt₀ 𝟙 p :=
  one_lt_prime hp

theorem vN_prime_ge_two {p : ℕ₀} (hp : Arith.Prime p) : le₀ 𝟚 p :=
  prime_ge_two hp

-- ─────────────────────────────────────────────────────────────────
-- Divisores de un primo
-- ─────────────────────────────────────────────────────────────────

theorem vN_prime_divisors {p d : ℕ₀} (hp : Arith.Prime p) (hd : d ∣ p) :
    vN d = vN 𝟙 ∨ vN d = vN p :=
  (prime_divisors hp hd).imp (congrArg vN) (congrArg vN)

-- ─────────────────────────────────────────────────────────────────
-- Coprimalidad
-- ─────────────────────────────────────────────────────────────────

theorem vN_coprime_symm {a b : ℕ₀} (h : coprime_HF (vN a) (vN b)) :
    coprime_HF (vN b) (vN a) := by
  rw [vN_coprime_iff] at h ⊢
  rwa [gcd_comm]

theorem vN_prime_coprime_or_dvd {p n : ℕ₀} (hp : Arith.Prime p) :
    dvd_HF (vN p) (vN n) ∨ coprime_HF (vN p) (vN n) := by
  rw [vN_dvd_iff, vN_coprime_iff]
  rcases @prime_coprime_or_dvd p n hp with h | h
  · exact Or.inl h
  · exact Or.inr ((gcd_eq_one_iff_coprime p n).mpr h)

-- ─────────────────────────────────────────────────────────────────
-- Lema de Gauss: coprimo ∧ divide producto → divide factor
-- ─────────────────────────────────────────────────────────────────

theorem vN_coprime_dvd_of_dvd_mul {a b c : ℕ₀}
    (hcop : coprime_HF (vN a) (vN b)) (hdvd : dvd_HF (vN a) (vN (mul b c))) :
    dvd_HF (vN a) (vN c) := by
  rw [vN_dvd_iff] at hdvd ⊢
  rw [vN_coprime_iff] at hcop
  exact coprime_dvd_of_dvd_mul ((gcd_eq_one_iff_coprime a b).mp hcop) hdvd

-- ─────────────────────────────────────────────────────────────────
-- Irreducibilidad
-- ─────────────────────────────────────────────────────────────────

theorem vN_prime_imp_irreducible {p : ℕ₀} (hp : Arith.Prime p) :
    Peano.Primes.Irreducible p :=
  prime_imp_irreducible hp

theorem vN_irreducible_imp_prime {p : ℕ₀} (hp0 : p ≠ 𝟘) (hi : Peano.Primes.Irreducible p) :
    Arith.Prime p :=
  irreducible_imp_prime hp0 hi

-- ─────────────────────────────────────────────────────────────────
-- Existencia de divisor primo (toda n ≥ 2 tiene uno)
-- ─────────────────────────────────────────────────────────────────

theorem vN_exists_prime_divisor {n : ℕ₀} (hn : le₀ 𝟚 n) :
    ∃ p : ℕ₀, Arith.Prime p ∧ dvd_HF (vN p) (vN n) := by
  obtain ⟨p, hp, hdvd⟩ := exists_prime_divisor n hn
  exact ⟨p, hp, vN_dvd_iff.mpr hdvd⟩

-- ─────────────────────────────────────────────────────────────────
-- Teorema Fundamental de la Aritmética — Existencia
-- ─────────────────────────────────────────────────────────────────

theorem vN_exists_prime_factorization {n : ℕ₀} (hn : le₀ 𝟚 n) :
    ∃ ps : List ℕ₀, PrimeList ps ∧ vN (product_list ps) = vN n := by
  obtain ⟨ps, hps, heq⟩ := exists_prime_factorization n hn
  exact ⟨ps, hps, congrArg vN heq⟩

-- ─────────────────────────────────────────────────────────────────
-- Teorema Fundamental de la Aritmética — Unicidad
-- ─────────────────────────────────────────────────────────────────

theorem vN_unique_prime_factorization {ps qs : List ℕ₀}
    (hps : PrimeList ps) (hqs : PrimeList qs)
    (heq : vN (product_list ps) = vN (product_list qs))
    (p : ℕ₀) (hp : Arith.Prime p) :
    Peano.List.lengthₚ (List.filter (fun q => decide (q = p)) ps) =
    Peano.List.lengthₚ (List.filter (fun q => decide (q = p)) qs) :=
  unique_prime_factorization ps qs hps hqs (vN_injective heq) p hp

-- ─────────────────────────────────────────────────────────────────
-- Test de primalidad computable
-- ─────────────────────────────────────────────────────────────────

theorem vN_isPrimeb_iff {n : ℕ₀} : isPrimeb n = true ↔ prime_HF (vN n) := by
  rw [vN_prime_iff]
  exact isPrimeb_iff

end VN
