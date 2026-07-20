/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Q0
import AczelSetTheory.Rationals.Inv
import AczelSetTheory.Rationals.AbsVal
import AczelSetTheory.Rationals.Roots
import AczelSetTheory.Rationals.PowOrder

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

-- ─────────────────────────────────────────────────────────────────────────────
-- API BRIDGE de las operaciones de cuerpo (ADR-023, migración de tipos)
--
-- Todas las operaciones de arriba fijan `cls := (op sobre cls)`, así que `.cls` conmuta
-- con ellas por `rfl`. Con eso + `@[ext]`, cada lema de `ℚ₀cls` (Inv.lean, PowOrder.lean,
-- Roots.lean) se transfiere a `ℚ₀` en una línea. Esto completa el lado «cuerpo» de la capa
-- núcleo: sin estos lemas un consumidor podía USAR `ℚ₀` pero no RAZONAR sobre ⁻¹ / / / pow.
-- Se usa `Mul.mul`/`Add.add`/`Sub.sub` explícito (el elaborador de `+`/`*` choca con las
-- coerciones en juego), como el resto de la teoría de ℚ₀.
-- ─────────────────────────────────────────────────────────────────────────────

namespace ℚ₀

-- ── Homomorfismo `.cls` de las operaciones de cuerpo (todas rfl) ──
@[simp] theorem cls_inv (a : ℚ₀)   : (a⁻¹).cls = (a.cls)⁻¹ := rfl
@[simp] theorem cls_div (a b : ℚ₀) : (a / b).cls = a.cls / b.cls := rfl
@[simp] theorem cls_pow (a : ℚ₀) (n : ℕ₀) : (a.pow n).cls = ℚ₀cls.pow a.cls n := rfl
@[simp] theorem cls_ofNat₀ (n : ℕ₀) : (ofNat₀ n).cls = ℚ₀cls.ofNat₀ n := rfl
@[simp] theorem cls_ofInt (z : ℤ₀)  : (ofInt z).cls = ℚ₀cls.ofInt z.cls := rfl

-- ── Puente de igualdad/desigualdad struct ↔ clase ──
-- (la igualdad del struct NO es definicionalmente la de la clase: hace falta `ext` en un
--  sentido y `congrArg .cls` en el otro; de ahí que los lemas con hipótesis `≠ 0` lo usen)

/-- Dos racionales empaquetados son iguales exactamente cuando lo son sus clases. -/
theorem eq_iff_cls {a b : ℚ₀} : a = b ↔ a.cls = b.cls :=
  ⟨congrArg ℚ₀.cls, ext a b⟩

theorem ne_zero_iff_cls {q : ℚ₀} : q ≠ 0 ↔ q.cls ≠ 0 := by
  constructor
  · intro h hc; exact h (ext q 0 hc)
  · intro h hq; exact h (congrArg ℚ₀.cls hq)

-- ── Cuerpo: inverso multiplicativo ──
theorem one_ne_zero : (1 : ℚ₀) ≠ 0 := ne_zero_iff_cls.mpr ℚ₀cls.one_ne_zero

theorem mul_inv_cancel {q : ℚ₀} (h : q ≠ 0) : Mul.mul q q⁻¹ = 1 :=
  ext _ _ (ℚ₀cls.mul_inv_cancel (ne_zero_iff_cls.mp h))

theorem inv_mul_cancel {q : ℚ₀} (h : q ≠ 0) : Mul.mul q⁻¹ q = 1 :=
  ext _ _ (ℚ₀cls.inv_mul_cancel (ne_zero_iff_cls.mp h))

theorem inv_unique {x y : ℚ₀} (hx : x ≠ 0) (h : Mul.mul x y = 1) : y = x⁻¹ :=
  ext _ _ (ℚ₀cls.inv_unique (ne_zero_iff_cls.mp hx) (congrArg ℚ₀.cls h))

theorem inv_mul_inv (x y : ℚ₀) (hx : x ≠ 0) (hy : y ≠ 0) :
    (Mul.mul x y)⁻¹ = Mul.mul x⁻¹ y⁻¹ :=
  ext _ _ (ℚ₀cls.inv_mul_inv x.cls y.cls (ne_zero_iff_cls.mp hx) (ne_zero_iff_cls.mp hy))

theorem inv_sub_inv_eq (x y : ℚ₀) (hx : x ≠ 0) (hy : y ≠ 0) :
    Sub.sub x⁻¹ y⁻¹ = Mul.mul (Sub.sub y x) (Mul.mul x y)⁻¹ :=
  ext _ _ (ℚ₀cls.inv_sub_inv_eq x.cls y.cls (ne_zero_iff_cls.mp hx) (ne_zero_iff_cls.mp hy))

theorem inv_nonneg {x : ℚ₀} (hx : 0 ≤ x) (h_ne : x ≠ 0) : 0 ≤ x⁻¹ :=
  ℚ₀cls.inv_nonneg hx (ne_zero_iff_cls.mp h_ne)

theorem inv_le_one {q : ℚ₀} (hq : 1 ≤ q) : q⁻¹ ≤ 1 := ℚ₀cls.inv_le_one hq

-- ── Potencia natural ──
theorem pow_zero (a : ℚ₀) : a.pow 𝟘 = 1 := ext _ _ (ℚ₀cls.pow_zero a.cls)
theorem pow_succ (a : ℚ₀) (n : ℕ₀) : a.pow (σ n) = Mul.mul a (a.pow n) :=
  ext _ _ (ℚ₀cls.pow_succ a.cls n)
theorem pow_one (a : ℚ₀) : a.pow 𝟙 = a := ext _ _ (ℚ₀cls.pow_one a.cls)
theorem pow_add (a : ℚ₀) (m n : ℕ₀) :
    a.pow (Peano.Add.add m n) = Mul.mul (a.pow m) (a.pow n) :=
  ext _ _ (ℚ₀cls.pow_add a.cls m n)
theorem pow_nonneg {a : ℚ₀} (ha : 0 ≤ a) (n : ℕ₀) : 0 ≤ a.pow n := ℚ₀cls.pow_nonneg ha n
theorem pow_le_pow_left {a b : ℚ₀} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ₀) : a.pow n ≤ b.pow n :=
  ℚ₀cls.pow_le_pow_left ha hab n
theorem one_le_pow {a : ℚ₀} (ha : 1 ≤ a) (n : ℕ₀) : 1 ≤ a.pow n := ℚ₀cls.one_le_pow ha n
theorem absVal_pow (a : ℚ₀) (n : ℕ₀) : absVal (a.pow n) = (absVal a).pow n :=
  ext _ _ (ℚ₀cls.absVal_pow a.cls n)

-- ── Inclusiones ℕ₀ ↪ ℚ₀ ──
theorem ofNat₀_add (n m : ℕ₀) :
    ofNat₀ (Peano.Add.add n m) = Add.add (ofNat₀ n) (ofNat₀ m) :=
  ext _ _ (ℚ₀cls.ofNat₀_add n m)
theorem ofNat₀_mul (n m : ℕ₀) :
    ofNat₀ (Peano.Mul.mul n m) = Mul.mul (ofNat₀ n) (ofNat₀ m) :=
  ext _ _ (ℚ₀cls.ofNat₀_mul n m)
theorem ofNat₀_nonneg (n : ℕ₀) : 0 ≤ ofNat₀ n := ℚ₀cls.ofNat₀_nonneg n
theorem ofNat₀_pos {k : ℕ₀} (hk : k ≠ 𝟘) : 0 < ofNat₀ k := ℚ₀cls.ofNat₀_pos hk

end ℚ₀
