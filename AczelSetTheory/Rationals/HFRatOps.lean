import AczelSetTheory.Rationals.HFRat
import AczelSetTheory.Rationals.Inv
import AczelSetTheory.Rationals.AbsVal
import AczelSetTheory.Rationals.Roots

open Peano

-- Definición de Inverso
instance : Inv HFRat where
  inv a :=
    { cls  := a.cls⁻¹
      pair := ℚ₀'.ofQ0 (a.cls⁻¹)
      hEq  := by rw [ℚ₀'.toQ0_ofQ0] }

-- Definición de División
instance : Div HFRat where
  div a b :=
    { cls  := a.cls / b.cls
      pair := ℚ₀'.ofQ0 (a.cls / b.cls)
      hEq  := by rw [ℚ₀'.toQ0_ofQ0] }



-- Definición de Potencia Natural
def HFRat.pow (a : HFRat) (n : ℕ₀) : HFRat :=
  { cls  := ℚ₀.pow a.cls n
    pair := ℚ₀'.ofQ0 (ℚ₀.pow a.cls n)
    hEq  := by rw [ℚ₀'.toQ0_ofQ0] }

def HFRat.ofNat₀ (n : ℕ₀) : HFRat :=
  { cls  := ℚ₀.ofNat₀ n
    pair := ℚ₀'.ofQ0 (ℚ₀.ofNat₀ n)
    hEq  := by rw [ℚ₀'.toQ0_ofQ0] }

def HFRat.ofInt (z : HFInt) : HFRat :=
  { cls  := ℚ₀.ofInt z.cls
    pair := ℚ₀'.ofQ0 (ℚ₀.ofInt z.cls)
    hEq  := by rw [ℚ₀'.toQ0_ofQ0] }
