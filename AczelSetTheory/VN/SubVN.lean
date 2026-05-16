/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/SubVN.lean
-- Transporte de la sustracción acotada de Peano a HFSet mediante vN.
--
-- La sustracción de Peano es "acotada" (monus): `sub m n = 0` cuando `n ≥ m`.
-- Todos los resultados son imágenes directas de los teoremas de Peano.Sub
-- transportados vía el embedding inyectivo `vN : ℕ₀ → HFSet`.
--
-- Contenido:
--   vN_sub_zero                : vN (sub n 𝟘) = vN n
--   vN_zero_sub                : vN (sub 𝟘 n) = vN 𝟘
--   vN_sub_self                : vN (sub n n) = vN 𝟘
--   vN_succ_sub_one            : vN (sub (σ n) 𝟙) = vN n
--   vN_sub_succ_succ           : vN (sub a b) = vN (sub (σ a) (σ b))
--   vN_add_k_sub_k             : vN (sub (add k n) k) = vN n
--   vN_sub_k_add_k             : k ≤ n → vN (add (sub n k) k) = vN n
--   vN_add_sub_assoc           : k ≤ n → vN (add (sub n k) m) = vN (sub (add n m) k)
--   sub_le_vN_self             : le₀ (sub n m) n
--   sub_pos_of_lt_vN           : lt₀ m n → lt₀ 𝟘 (sub n m)
--   vN_succ_sub                : le₀ (σ m) n → vN (sub n (σ m)) = vN (τ (sub n m))
--   vN_sub_succ_eq             : k ≤ n → vN (sub (σ n) k) = vN (σ (sub n k))

import AczelSetTheory.VN.PeanoArith
open Peano
open Peano.Sub

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Leyes básicas de la sustracción transportadas vía vN
-- ─────────────────────────────────────────────────────────────────

/-- Elemento neutro a la derecha: `vN (sub n 𝟘) = vN n`. -/
theorem vN_sub_zero (n : ℕ₀) : vN (sub n 𝟘) = vN n :=
  congrArg vN (sub_zero n)

/-- Cero a la izquierda: `vN (sub 𝟘 n) = vN 𝟘`. -/
theorem vN_zero_sub (n : ℕ₀) : vN (sub 𝟘 n) = vN 𝟘 :=
  congrArg vN (zero_sub n)

/-- Idempotencia: `vN (sub n n) = vN 𝟘`. -/
theorem vN_sub_self (n : ℕ₀) : vN (sub n n) = vN 𝟘 :=
  congrArg vN (sub_self n)

/-- Predecesor: `vN (sub (σ n) 𝟙) = vN n`. -/
theorem vN_succ_sub_one (n : ℕ₀) : vN (sub (σ n) 𝟙) = vN n := by
  have h : sub (σ n) 𝟙 = n :=
    (sub_succ_succ_eq n 𝟘).symm.trans (sub_zero n)
  exact congrArg vN h

/-- Desplazamiento de sucesor: `vN (sub a b) = vN (sub (σ a) (σ b))`. -/
theorem vN_sub_succ_succ (a b : ℕ₀) : vN (sub a b) = vN (sub (σ a) (σ b)) :=
  congrArg vN (sub_succ_succ_eq a b)

/-- Cancelación suma-resta: `sub (add k n) k = n` transportado a vN. -/
theorem vN_add_k_sub_k (n k : ℕ₀) : vN (sub (add k n) k) = vN n :=
  congrArg vN (add_k_sub_k n k)

/-- Resta-suma (con cota): `k ≤ n → add (sub n k) k = n` transportado a vN. -/
theorem vN_sub_k_add_k (n k : ℕ₀) (h : le₀ k n) : vN (add (sub n k) k) = vN n :=
  congrArg vN (sub_k_add_k n k h)

/-- Asociatividad suma-resta: `le₀ k n → vN (add (sub n k) m) = vN (sub (add n m) k)`. -/
theorem vN_add_sub_assoc (n m k : ℕ₀) (h : le₀ k n) :
    vN (add (sub n k) m) = vN (sub (add n m) k) :=
  congrArg vN (add_sub_assoc n m k h)

/-- La sustracción acotada no excede el minuendo: `le₀ (sub n m) n`. -/
theorem sub_le_vN_self (n m : ℕ₀) : le₀ (sub n m) n :=
  sub_le_self n m

/-- Si `m < n`, la sustracción es estrictamente positiva: `𝟘 < sub n m`. -/
theorem sub_pos_of_lt_vN {n m : ℕ₀} (h : lt₀ m n) : lt₀ 𝟘 (sub n m) :=
  sub_pos_of_lt h

/-- Sustracción de sucesor del subtrahendo (requiere cota):
    `le₀ (σ m) n → vN (sub n (σ m)) = vN (τ (sub n m))`. -/
theorem vN_succ_sub (n m : ℕ₀) (h : le₀ (σ m) n) :
    vN (sub n (σ m)) = vN (τ (sub n m)) :=
  congrArg vN (succ_sub n m h)

/-- Sustracción del minuendo sucesor (requiere cota):
    `le₀ k n → vN (sub (σ n) k) = vN (σ (sub n k))`. -/
theorem vN_sub_succ_left (n k : ℕ₀) (h : le₀ k n) :
    vN (sub (σ n) k) = vN (σ (sub n k)) :=
  congrArg vN (sub_succ n k h)

end VN
