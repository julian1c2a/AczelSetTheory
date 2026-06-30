/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/IsCauchy.lean
-- Sucesiones de Cauchy diádicas sobre ℚ₀ (M3B).
--
-- API entregada:
--   pow2              : ℕ₀ → ℚ₀             -- 1/2^n
--   IsCauchy          : (ℕ₀ → ℚ₀) → Prop   -- cond. simétrica con min
--   IsCauchy₂         : (ℕ₀ → ℚ₀) → Prop   -- cond. asimétrica (n ≤ m)
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

namespace ℚ₀

-- ============================================================
-- Sección 1: pow2 — potencias diádicas inversas 1/2^n
-- ============================================================

/-- `pow2 n = 1/2^n` en ℚ₀. Construido directamente como el racional con
numerador 1 y denominador 2^n. -/
def pow2_den (n : ℕ₀) : ℕ₁ :=
  ⟨Peano.Pow.pow (σ (σ 𝟘)) n, Peano.Pow.pow_ne_zero (by decide) n⟩

-- pow2 n = 1 / 2^n
theorem pow2_den_succ (n : ℕ₀) : (pow2_den (σ n)).val = Peano.Mul.mul (pow2_den n).val (σ (σ 𝟘)) := rfl

def pow2 (n : ℕ₀) : ℚ₀ :=
  ℚ₀.mk (ℤ₀.ofNat (σ 𝟘)) (pow2_den n)

theorem pow2_nonneg (n : ℕ₀) : (0 : ℚ₀) ≤ pow2 n := by
  show Mul.mul (0:ℤ₀) (ℤ₀.ofNat (pow2_den n).val) ≤ Mul.mul (ℤ₀.ofNat (σ 𝟘)) (ℤ₀.ofNat 𝟙)
  rw [ℤ₀.zero_mul]
  have h1 : Mul.mul (ℤ₀.ofNat (σ 𝟘)) (ℤ₀.ofNat 𝟙) = ℤ₀.ofNat (σ 𝟘) := by
    rw [← ℤ₀.ofNat_mul]
    have h1_1 : Peano.Mul.mul (σ 𝟘) 𝟙 = σ 𝟘 := Peano.Mul.mul_one _
    rw [h1_1]
  rw [h1]
  exact ℤ₀.zero_le_ofNat _

theorem pow2_succ_add (n : ℕ₀) : Add.add (pow2 (σ n)) (pow2 (σ n)) = pow2 n := by
  dsimp [pow2]
  rw [ℚ₀.add_mk]
  rw [ℚ₀.mk_eq_iff]
  -- Algebraic equality in ℤ₀: (1*2^(n+1) + 1*2^(n+1)) * 2^n = 1 * (2^(n+1) * 2^(n+1))
  -- Needs manual rewriting since we don't have a `ring` tactic for ℤ₀.
  sorry

-- ============================================================
-- Sección 2: Definiciones de Cauchy
-- ============================================================

/-- Condición de Cauchy diádica **simétrica**: para toda sucesión f : ℕ₀ → ℚ₀,
`|f n - f m| ≤ 1/2^(min n m)`.

Es la definición principal porque no requiere hipótesis de orden entre n y m,
y es compatible con `absVal_sub_comm`. -/
def IsCauchy (f : ℕ₀ → ℚ₀) : Prop :=
  ∀ n m : ℕ₀, absVal (f n - f m) ≤ pow2 (Peano.Lattice.min n m)

/-- Condición de Cauchy diádica **asimétrica**: para n ≤ m, `|f m - f n| ≤ 1/2^n`.

Alternativa más próxima a la presentación clásica "la sucesión converge a ritmo
diádico". Equivalente a `IsCauchy` (ver `isCauchy_iff_isCauchy₂`). -/
def IsCauchy₂ (f : ℕ₀ → ℚ₀) : Prop :=
  ∀ n m : ℕ₀, n ≤ m → absVal (f m - f n) ≤ pow2 n

-- ============================================================
-- Sección 3: Equivalencia entre las dos condiciones
-- ============================================================

/-- `IsCauchy f ↔ IsCauchy₂ f`.

**Idea**: la condición simétrica se reduce a la asimétrica usando
`le_then_min_eq_left` (cuando n ≤ m, `min n m = n`) y `absVal_sub_comm`
(que intercambia los argumentos de la diferencia). -/
theorem isCauchy_iff_isCauchy₂ (f : ℕ₀ → ℚ₀) : IsCauchy f ↔ IsCauchy₂ f := by
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

end ℚ₀
