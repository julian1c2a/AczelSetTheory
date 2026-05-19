/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/BinomVN.lean
-- Transporte del coeficiente binomial de Peano a HFSet mediante vN.
--
-- Contenido:
--   binomVN              : ℕ₀ → ℕ₀ → HFSet   (imagen directa de vN)
--   binomVN_def          : binomVN n k = vN (binom n k)
--   vN_binom_zero_zero   : vN (binom 𝟘 𝟘) = vN 𝟙
--   vN_binom_zero_succ   : vN (binom 𝟘 (σ k)) = vN 𝟘
--   vN_binom_succ_zero   : vN (binom (σ n) 𝟘) = vN 𝟙
--   vN_binom_pascal      : vN (binom (σ n) (σ k)) = vN (add (binom n k) (binom n (σ k)))
--   vN_binom_n_zero      : vN (binom n 𝟘) = vN 𝟙
--   vN_binom_n_one       : vN (binom n 𝟙) = vN n
--   vN_binom_self        : vN (binom n n) = vN 𝟙
--   vN_binom_eq_zero_gt  : lt₀ n k → vN (binom n k) = vN 𝟘

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Combinatorics.Binom

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición: coeficiente binomial en la imagen de vN
-- ─────────────────────────────────────────────────────────────────

/-- Coeficiente binomial de von Neumann: imagen de `binom n k` bajo el embedding vN. -/
def binomVN (n k : ℕ₀) : HFSet := vN (binom n k)

theorem binomVN_def (n k : ℕ₀) : binomVN n k = vN (binom n k) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Leyes transportadas vía congrArg vN
-- ─────────────────────────────────────────────────────────────────

/-- C(0, 0) = 1 en la imagen de vN. -/
theorem vN_binom_zero_zero : vN (binom 𝟘 𝟘) = vN 𝟙 :=
  congrArg vN binom_zero_zero

/-- C(0, k+1) = 0 en la imagen de vN. -/
theorem vN_binom_zero_succ (k : ℕ₀) : vN (binom 𝟘 (σ k)) = vN 𝟘 :=
  congrArg vN (binom_zero_succ k)

/-- C(n+1, 0) = 1 en la imagen de vN. -/
theorem vN_binom_succ_zero (n : ℕ₀) : vN (binom (σ n) 𝟘) = vN 𝟙 :=
  congrArg vN (binom_succ_zero n)

/-- Regla de Pascal: C(n+1, k+1) = C(n, k) + C(n, k+1). -/
theorem vN_binom_pascal (n k : ℕ₀) :
    vN (binom (σ n) (σ k)) = vN (add (binom n k) (binom n (σ k))) :=
  congrArg vN (binom_pascal n k)

/-- C(n, 0) = 1 en la imagen de vN. -/
theorem vN_binom_n_zero (n : ℕ₀) : vN (binom n 𝟘) = vN 𝟙 :=
  congrArg vN (binom_n_zero n)

/-- C(n, 1) = n en la imagen de vN. -/
theorem vN_binom_n_one (n : ℕ₀) : vN (binom n 𝟙) = vN n :=
  congrArg vN (binom_n_one n)

/-- C(n, n) = 1 en la imagen de vN. -/
theorem vN_binom_self (n : ℕ₀) : vN (binom n n) = vN 𝟙 :=
  congrArg vN (binom_self n)

/-- Si k > n, entonces C(n, k) = 0 en la imagen de vN. -/
theorem vN_binom_eq_zero_gt {n k : ℕ₀} (h : lt₀ n k) : vN (binom n k) = vN 𝟘 :=
  congrArg vN (binom_eq_zero_of_gt h)

end VN
