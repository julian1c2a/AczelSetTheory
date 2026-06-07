/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/ZModN.lean
-- Anillo ℤ/nℤ como HFRing finito (n ≠ 𝟘).
--
-- ESTADO: M5B (2026-06-06). Anillo unitario `ZModN n hn : HFRing`.
--
-- Diseño (ADR-016): como `HFSet` es hereditariamente finito, ℤ/nℤ NO se construye
-- como cociente de ℤ₀ (infinito), sino como un HFRing finito cuyo PORTADOR es el
-- ordinal de von Neumann `vN n = {vN 0, …, vN (n−1)}`. Cada residuo es el HFSet
-- `vN k` con `k < n`. Las operaciones usan el puente `card`/`vN`:
--     add x y := vN ((card x + card y) mod n)
--     mul x y := vN ((card x · card y) mod n)
--     neg x   := vN ((n − card x) mod n)
--     zero    := vN 𝟘,   one := vN (𝟙 mod n)
-- Los axiomas de anillo se reducen a la aritmética modular de ℕ₀ (peanolib ModEq).
--
-- Público:
--   HFAlgebra.ZModN (n : ℕ₀) (hn : n ≠ 𝟘) : HFRing
--
-- Dependencies: AczelSetTheory.Algebra.Ring, AczelSetTheory.VN.{Arithmetic,IsNat,CardVN},
--               Peano.PeanoNat.NumberTheory.ModEq
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Algebra.Ring
import AczelSetTheory.VN.Arithmetic
import AczelSetTheory.VN.IsNat
import AczelSetTheory.VN.CardVN
import Peano.PeanoNat.NumberTheory.ModEq

open Peano
open Peano.Add Peano.Mul Peano.Div Peano.Sub Peano.ModEq Peano.StrictOrder Peano.Order
open VN

namespace HFAlgebra

-- ============================================================
-- Sección 0: Lemas auxiliares de aritmética modular en ℕ₀
-- ============================================================

/-- `mod` absorbe a la izquierda de una suma: `(a%n + c) % n = (a + c) % n`. -/
private theorem zmod_add_left (a c n : ℕ₀) :
    mod (add (mod a n) c) n = mod (add a c) n := by
  rw [add_mod (mod a n) c n, mod_mod, ← add_mod a c n]

/-- `mod` absorbe a la derecha de una suma: `(a + c%n) % n = (a + c) % n`. -/
private theorem zmod_add_right (a c n : ℕ₀) :
    mod (add a (mod c n)) n = mod (add a c) n := by
  rw [add_mod a (mod c n) n, mod_mod, ← add_mod a c n]

/-- `mod` absorbe a la izquierda de un producto: `(a%n · c) % n = (a · c) % n`. -/
private theorem zmod_mul_left (a c n : ℕ₀) :
    mod (mul (mod a n) c) n = mod (mul a c) n := by
  rw [mul_mod (mod a n) c n, mod_mod, ← mul_mod a c n]

/-- `mod` absorbe a la derecha de un producto: `(a · c%n) % n = (a · c) % n`. -/
private theorem zmod_mul_right (a c n : ℕ₀) :
    mod (mul a (mod c n)) n = mod (mul a c) n := by
  rw [mul_mod a (mod c n) n, mod_mod, ← mul_mod a c n]

-- ============================================================
-- Sección 1: Lemas puente vN ↔ card sobre el ordinal vN n
-- ============================================================

/-- Todo residuo `vN (k mod n)` pertenece al portador `vN n` (cuando `n ≠ 𝟘`). -/
private theorem zmod_mem {n : ℕ₀} (hn : n ≠ 𝟘) (k : ℕ₀) :
    vN (mod k n) ∈ vN n :=
  (mem_vN_iff_lt (mod k n) n).mpr (mod_lt k n hn)

/-- Todo elemento del ordinal `vN n` es el von-Neumann de su cardinal. -/
private theorem zmod_eq_vN_card {n : ℕ₀} {x : HFSet} (hx : x ∈ vN n) :
    x = vN (HFSet.card x) := by
  have hisNat : HFSet.isNat x := HFSet.isNat_mem_isNat (isNat_vN n) hx
  obtain ⟨m, hm⟩ := vN_mem_range hisNat
  rw [← hm, card_vN]

/-- El cardinal de un elemento del ordinal `vN n` es menor que `n`. -/
private theorem zmod_card_lt {n : ℕ₀} {x : HFSet} (hx : x ∈ vN n) :
    lt₀ (HFSet.card x) n := by
  have h := hx
  rw [zmod_eq_vN_card hx] at h
  exact (mem_vN_iff_lt (HFSet.card x) n).mp h

/-- Forma reducida: todo elemento de `vN n` es `vN (card x mod n)`. -/
private theorem zmod_eq_vN_mod {n : ℕ₀} {x : HFSet} (hx : x ∈ vN n) :
    x = vN (mod (HFSet.card x) n) := by
  have hmod : mod (HFSet.card x) n = HFSet.card x :=
    mod_of_lt (HFSet.card x) n (zmod_card_lt hx)
  rw [hmod]
  exact zmod_eq_vN_card hx

-- ============================================================
-- Sección 2: El anillo ℤ/nℤ
-- ============================================================

/-- **Anillo ℤ/nℤ** como `HFRing` finito sobre el ordinal `vN n` (`n ≠ 𝟘`).
    Portador `vN n`; suma, producto y opuesto definidos módulo `n` vía el
    puente `card`/`vN`. -/
def ZModN (n : ℕ₀) (hn : n ≠ 𝟘) : HFRing where
  R    := vN n
  add  := fun x y => vN (mod (add (HFSet.card x) (HFSet.card y)) n)
  mul  := fun x y => vN (mod (mul (HFSet.card x) (HFSet.card y)) n)
  zero := vN 𝟘
  one  := vN (mod 𝟙 n)
  neg  := fun x => vN (mod (sub n (HFSet.card x)) n)
  -- pertenencias
  zero_mem := (mem_vN_iff_lt 𝟘 n).mpr (pos_of_ne_zero n hn)
  one_mem  := zmod_mem hn 𝟙
  add_closed := fun _ _ => zmod_mem hn _
  mul_closed := fun _ _ => zmod_mem hn _
  neg_closed := fun _ => zmod_mem hn _
  -- grupo aditivo abeliano
  add_assoc := by
    intro a b c _ _ _
    show vN (mod (add (HFSet.card (vN (mod (add (HFSet.card a) (HFSet.card b)) n)))
                      (HFSet.card c)) n)
       = vN (mod (add (HFSet.card a)
                      (HFSet.card (vN (mod (add (HFSet.card b) (HFSet.card c)) n)))) n)
    simp only [card_vN]
    rw [zmod_add_left, zmod_add_right, add_assoc]
  add_comm := by
    intro a b _ _
    show vN (mod (add (HFSet.card a) (HFSet.card b)) n)
       = vN (mod (add (HFSet.card b) (HFSet.card a)) n)
    rw [add_comm (HFSet.card a) (HFSet.card b)]
  zero_add := by
    intro a ha
    show vN (mod (add (HFSet.card (vN 𝟘)) (HFSet.card a)) n) = a
    rw [card_vN, zero_add]
    exact (zmod_eq_vN_mod ha).symm
  neg_add := by
    intro a ha
    show vN (mod (add (HFSet.card (vN (mod (sub n (HFSet.card a)) n))) (HFSet.card a)) n)
       = vN 𝟘
    rw [card_vN, zmod_add_left,
        sub_k_add_k n (HFSet.card a) (lt_imp_le_wp (zmod_card_lt ha)), mod_self]
  -- monoide multiplicativo unitario
  mul_assoc := by
    intro a b c _ _ _
    show vN (mod (mul (HFSet.card (vN (mod (mul (HFSet.card a) (HFSet.card b)) n)))
                      (HFSet.card c)) n)
       = vN (mod (mul (HFSet.card a)
                      (HFSet.card (vN (mod (mul (HFSet.card b) (HFSet.card c)) n)))) n)
    simp only [card_vN]
    rw [zmod_mul_left, zmod_mul_right, mul_assoc]
  mul_one := by
    intro a ha
    show vN (mod (mul (HFSet.card a) (HFSet.card (vN (mod 𝟙 n)))) n) = a
    rw [card_vN, zmod_mul_right, mul_one]
    exact (zmod_eq_vN_mod ha).symm
  one_mul := by
    intro a ha
    show vN (mod (mul (HFSet.card (vN (mod 𝟙 n))) (HFSet.card a)) n) = a
    rw [card_vN, zmod_mul_left, one_mul]
    exact (zmod_eq_vN_mod ha).symm
  -- distributividad
  left_distrib := by
    intro a b c _ _ _
    show vN (mod (mul (HFSet.card a)
                      (HFSet.card (vN (mod (add (HFSet.card b) (HFSet.card c)) n)))) n)
       = vN (mod (add (HFSet.card (vN (mod (mul (HFSet.card a) (HFSet.card b)) n)))
                      (HFSet.card (vN (mod (mul (HFSet.card a) (HFSet.card c)) n)))) n)
    simp only [card_vN]
    rw [zmod_mul_right, mul_add,
        ← add_mod (mul (HFSet.card a) (HFSet.card b))
                  (mul (HFSet.card a) (HFSet.card c)) n]
  right_distrib := by
    intro a b c _ _ _
    show vN (mod (mul (HFSet.card (vN (mod (add (HFSet.card a) (HFSet.card b)) n)))
                      (HFSet.card c)) n)
       = vN (mod (add (HFSet.card (vN (mod (mul (HFSet.card a) (HFSet.card c)) n)))
                      (HFSet.card (vN (mod (mul (HFSet.card b) (HFSet.card c)) n)))) n)
    simp only [card_vN]
    rw [zmod_mul_left, add_mul,
        ← add_mod (mul (HFSet.card a) (HFSet.card c))
                  (mul (HFSet.card b) (HFSet.card c)) n]

-- ============================================================
-- Sección 3: Conmutatividad multiplicativa explícita
-- ============================================================

/-- El producto de `ZModN n hn` es conmutativo: `ℤ/nℤ` es un anillo conmutativo.
    (HFRing no rastrea `mul_comm`; se expone como teorema independiente.) -/
theorem ZModN_mul_comm (n : ℕ₀) (hn : n ≠ 𝟘) (x y : HFSet) :
    (ZModN n hn).mul x y = (ZModN n hn).mul y x := by
  show vN (mod (mul (HFSet.card x) (HFSet.card y)) n)
     = vN (mod (mul (HFSet.card y) (HFSet.card x)) n)
  rw [mul_comm (HFSet.card x) (HFSet.card y)]

end HFAlgebra
