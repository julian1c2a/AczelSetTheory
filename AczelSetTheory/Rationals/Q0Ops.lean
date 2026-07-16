/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Q0
import AczelSetTheory.Rationals.Inv
import AczelSetTheory.Rationals.AbsVal
import AczelSetTheory.Rationals.Roots

open Peano

-- Definición de Inverso
instance : Inv ℚ₀ where
  inv a :=
    { cls  := a.cls⁻¹
      pair := ℚ₀can.ofCls (a.cls⁻¹)
      hEq  := by rw [ℚ₀can.toCls_ofCls] }

-- Definición de División
instance : Div ℚ₀ where
  div a b :=
    { cls  := a.cls / b.cls
      pair := ℚ₀can.ofCls (a.cls / b.cls)
      hEq  := by rw [ℚ₀can.toCls_ofCls] }



-- Definición de Potencia Natural
def ℚ₀.pow (a : ℚ₀) (n : ℕ₀) : ℚ₀ :=
  { cls  := ℚ₀cls.pow a.cls n
    pair := ℚ₀can.ofCls (ℚ₀cls.pow a.cls n)
    hEq  := by rw [ℚ₀can.toCls_ofCls] }

def ℚ₀.ofNat₀ (n : ℕ₀) : ℚ₀ :=
  { cls  := ℚ₀cls.ofNat₀ n
    pair := ℚ₀can.ofCls (ℚ₀cls.ofNat₀ n)
    hEq  := by rw [ℚ₀can.toCls_ofCls] }

def ℚ₀.ofInt (z : ℤ₀) : ℚ₀ :=
  { cls  := ℚ₀cls.ofInt z.cls
    pair := ℚ₀can.ofCls (ℚ₀cls.ofInt z.cls)
    hEq  := by rw [ℚ₀can.toCls_ofCls] }
