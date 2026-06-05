/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/LogVN.lean
-- Transporte del logaritmo entero (log b n / clog b n) de Peano a HFSet vía vN.
-- log b n = ⌊log_b n⌋;  clog b n = ⌈log_b n⌉.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Log

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definiciones
-- ─────────────────────────────────────────────────────────────────

/-- Logaritmo entero inferior en base b: vN ⌊log_b n⌋. -/
def logVN (b n : ℕ₀) : HFSet := vN (log b n)

/-- Resto del logaritmo: vN (n - b^⌊log_b n⌋). -/
def logRemVN (b n : ℕ₀) : HFSet := vN (logRem b n)

/-- Logaritmo entero superior en base b: vN ⌈log_b n⌉. -/
def clogVN (b n : ℕ₀) : HFSet := vN (clog b n)

-- ─────────────────────────────────────────────────────────────────
-- Casos base
-- ─────────────────────────────────────────────────────────────────

theorem vN_log_zero (b : ℕ₀) : vN (log b 𝟘) = vN 𝟘 :=
  congrArg vN (log_zero b)

theorem vN_logRem_zero (b : ℕ₀) : vN (logRem b 𝟘) = vN 𝟘 :=
  congrArg vN (logRem_zero b)

theorem vN_log_one {b : ℕ₀} (hb : Peano.StrictOrder.lt₀ 𝟙 b) :
    vN (log b 𝟙) = vN 𝟘 :=
  congrArg vN (log_one hb)

theorem vN_logRem_one {b : ℕ₀} (hb : Peano.StrictOrder.lt₀ 𝟙 b) :
    vN (logRem b 𝟙) = vN 𝟘 :=
  congrArg vN (logRem_one hb)

-- ─────────────────────────────────────────────────────────────────
-- Especificación: n = b^log_b(n) + logRem_b(n)
-- ─────────────────────────────────────────────────────────────────

theorem vN_logMod_spec {b n : ℕ₀} (hb : Peano.StrictOrder.lt₀ 𝟙 b) (hn : n ≠ 𝟘) :
    vN n = vN (add (Peano.Pow.pow b (log b n)) (logRem b n)) :=
  congrArg vN (logMod_spec hb hn)

-- ─────────────────────────────────────────────────────────────────
-- Logaritmo superior (clog)
-- ─────────────────────────────────────────────────────────────────

theorem vN_clog_zero (b : ℕ₀) : vN (clog b 𝟘) = vN 𝟘 :=
  congrArg vN (clog_zero b)

theorem vN_clog_one {b : ℕ₀} (hb : Peano.StrictOrder.lt₀ 𝟙 b) : vN (clog b 𝟙) = vN 𝟘 :=
  congrArg vN (clog_one hb)

end VN
