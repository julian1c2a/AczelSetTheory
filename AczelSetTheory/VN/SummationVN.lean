/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/SummationVN.lean
-- Transporte del sumatorio finito (finSum) de Peano a HFSet vía vN.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Combinatorics.Summation

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición
-- ─────────────────────────────────────────────────────────────────

/-- Sumatorio finito transportado: vN (Σ_{k=0}^{n} f(k)). -/
def finSumVN (f : ℕ₀ → ℕ₀) (n : ℕ₀) : HFSet := vN (finSum f n)

-- ─────────────────────────────────────────────────────────────────
-- Ecuaciones de recursión
-- ─────────────────────────────────────────────────────────────────

theorem vN_finSum_zero (f : ℕ₀ → ℕ₀) :
    vN (finSum f 𝟘) = vN (f 𝟘) :=
  congrArg vN (finSum_zero f)

theorem vN_finSum_succ (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
    vN (finSum f (σ n)) = vN (add (finSum f n) (f (σ n))) :=
  congrArg vN (finSum_succ f n)

-- ─────────────────────────────────────────────────────────────────
-- Propiedades básicas
-- ─────────────────────────────────────────────────────────────────

theorem vN_finSum_zero_fn (n : ℕ₀) :
    vN (finSum (fun _ => 𝟘) n) = vN 𝟘 :=
  congrArg vN (finSum_zero_fn n)

theorem vN_finSum_const (c n : ℕ₀) :
    vN (finSum (fun _ => c) n) = vN (mul (σ n) c) :=
  congrArg vN (finSum_const c n)

theorem vN_finSum_add_fn (f g : ℕ₀ → ℕ₀) (n : ℕ₀) :
    vN (finSum (fun k => add (f k) (g k)) n) =
    vN (add (finSum f n) (finSum g n)) :=
  congrArg vN (finSum_add_fn f g n)

theorem vN_finSum_mul_const (c : ℕ₀) (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
    vN (finSum (fun k => mul c (f k)) n) = vN (mul c (finSum f n)) :=
  congrArg vN (finSum_mul_const c f n)

-- ─────────────────────────────────────────────────────────────────
-- Desplazamiento de índice
-- ─────────────────────────────────────────────────────────────────

theorem vN_finSum_succ_left (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
    vN (finSum f (σ n)) = vN (add (f 𝟘) (finSum (fun k => f (σ k)) n)) :=
  congrArg vN (finSum_succ_left f n)

theorem vN_finSum_reverse (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
    vN (finSum f n) = vN (finSum (fun k => f (Peano.Sub.sub n k)) n) :=
  congrArg vN (finSum_reverse f n)

end VN
