/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Bijection.lean
-- Biyección ℤ₀ ↔ ℕ₀ vía codificación de Cantor.
--
-- Público:
--   ℤ₀.encode           : ℤ₀ → ℕ₀
--   ℤ₀.decode           : ℕ₀ → ℤ₀
--   ℤ₀.decode_encode    : decode (encode z) = z
--   ℤ₀.encode_injective : encode a = encode b → a = b

import AczelSetTheory.Integers.Functions
import Peano.PeanoNat.Pairing

namespace ℤ₀

open Peano Peano.Add Peano.Sub Peano.Mul

-- ─────────────────────────────────────────────────────────────────────────────
-- Helper privado: reconstrucción desde el representante canónico
-- ─────────────────────────────────────────────────────────────────────────────

/-- Todo entero z es igual a repr.1 − repr.2 (interpretado en ℤ₀). -/
private theorem ofNat_sub_repr (z : ℤ₀) :
    Add.add (ofNat z.repr.1) (Neg.neg (ofNat z.repr.2)) = z := by
  apply repr_inj
  -- Componentes del representante de −(ofNat z.repr.2)
  have htn1 : (Neg.neg (ofNat z.repr.2)).repr.1 = 𝟘 := toNat_neg z.repr.2
  have htn2 : (Neg.neg (ofNat z.repr.2)).repr.2 = z.repr.2 := by
    have h := repr_neg_intEq (ofNat z.repr.2)
    simp only [repr_ofNat] at h
    rw [htn1] at h; omega₀
  -- Ecuación para la suma, forzada a usar Add.add (no HAdd.hAdd) para que
  -- omega₀ unifique los átomos con repr_normalized.
  have hadd : add (Add.add (ofNat z.repr.1) (Neg.neg (ofNat z.repr.2))).repr.1
                  (add 𝟘 z.repr.2) =
              add (Add.add (ofNat z.repr.1) (Neg.neg (ofNat z.repr.2))).repr.2
                  (add z.repr.1 𝟘) := by
    have h := repr_add_intEq (ofNat z.repr.1) (Neg.neg (ofNat z.repr.2))
    simp only [repr_ofNat] at h
    rw [htn1, htn2] at h
    exact h
  -- Cuatro casos normalizados
  rcases repr_normalized (Add.add (ofNat z.repr.1) (Neg.neg (ofNat z.repr.2))) with hs | hs <;>
  rcases repr_normalized z with hz | hz <;>
  exact Prod.ext (by omega₀) (by omega₀)

-- ─────────────────────────────────────────────────────────────────────────────
-- encode / decode
-- ─────────────────────────────────────────────────────────────────────────────

/-- Codifica un entero como número natural vía el par de Cantor de su representante. -/
def encode (z : ℤ₀) : ℕ₀ := Peano.Pairing.cantorPair z.repr.1 z.repr.2

/-- Decodifica un natural como entero usando el desempaquetado de Cantor. -/
def decode (n : ℕ₀) : ℤ₀ :=
  Add.add (ofNat (Peano.Pairing.cantorUnpair n).1)
          (Neg.neg (ofNat (Peano.Pairing.cantorUnpair n).2))

theorem decode_encode (z : ℤ₀) : decode (encode z) = z := by
  simp only [decode, encode, Peano.Pairing.cantorUnpair_cantorPair]
  exact ofNat_sub_repr z

theorem encode_injective {a b : ℤ₀} (h : encode a = encode b) : a = b := by
  unfold encode at h
  have heq := Peano.Pairing.cantorPair_injective _ _ _ _ h
  exact repr_inj (Prod.ext heq.1 heq.2)

end ℤ₀
