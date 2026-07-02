/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/PeanoAxioms.lean

import Peano.PeanoNat.Div
import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.Functions

open Peano.Axioms
open Peano.StrictOrder
open Peano.Order
open Peano.Lattice
open Peano.WellFounded
open Peano.Add
open Peano.Sub
open Peano.Mul
open Peano.Div

namespace AczelSetTheory.PeanoAxioms

/-- 
  Unicidad de la división entera en ℕ₀.
  Temporalmente como axioma para evitar romper PeanoNat
  mientras se añaden los lemas estructurales.
-/
axiom peano_divMod_unique (a b q1 r1 q2 r2 : ℕ₀) (hb : b ≠ 𝟘)
    (h1 : a = add (mul q1 b) r1) (hr1 : lt₀ r1 b)
    (h2 : a = add (mul q2 b) r2) (hr2 : lt₀ r2 b) :
    q1 = q2

/--
  Igualdad de división dados múltiplos cruzados.
  Si a*d = c*b, entonces a/b = c/d.
-/
axiom peano_div_eq_of_mul_eq (a b c d : ℕ₀) (hb : b ≠ 𝟘) (hd : d ≠ 𝟘)
    (h : mul a d = mul c b) :
    div a b = div c d

/--
  Propiedad distributiva de abs y toNat sobre la igualdad de racionales cruzados.
  Esta propiedad requiere la fundamentación completa de Integers.
-/
axiom peano_bound_eq (a c : ℤ₀) (b d : ℕ₁)
    (h : Mul.mul a (ℤ₀.ofNat d.val) = Mul.mul c (ℤ₀.ofNat b.val)) :
    div (ℤ₀.toNat (ℤ₀.abs a)) b.val = div (ℤ₀.toNat (ℤ₀.abs c)) d.val

end AczelSetTheory.PeanoAxioms
