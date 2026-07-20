/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Q0Roots.lean
-- Extracción de raíces (Newton–Raphson) y lemas de potencia/orden sobre ℚ₀ (ADR-023).
--
-- Migra al struct la teoría de `Rationals/Roots.lean` (que vive en ℚ₀cls). Las definiciones
-- nuevas (`newton_raphson_step`/`_seq`) son `ofCls (ℚ₀cls.f …)`, así que `.cls` conmuta por
-- `rfl`; el resto son bridges `ext`/directos. `pow` ya vive en `Q0Ops` (§6.108m).

import AczelSetTheory.Rationals.Q0Ops
import AczelSetTheory.Rationals.Q0Order
import AczelSetTheory.Rationals.Roots

namespace ℚ₀

-- ── Definiciones de Newton–Raphson ──

/-- Un paso de Newton–Raphson hacia `ⁿ√q`. -/
def newton_raphson_step (q : ℚ₀) (n : Peano.ℕ₂) (x : ℚ₀) : ℚ₀ :=
  ofCls (ℚ₀cls.newton_raphson_step q.cls n x.cls)

/-- La sucesión de Newton–Raphson (semilla `x₀ = q`) que aproxima `ⁿ√q`. -/
def newton_raphson_seq (q : ℚ₀) (n : Peano.ℕ₂) : ℕ₀ → ℚ₀ :=
  fun k => ofCls (ℚ₀cls.newton_raphson_seq q.cls n k)

@[simp] theorem cls_newton_raphson_step (q : ℚ₀) (n : Peano.ℕ₂) (x : ℚ₀) :
    (newton_raphson_step q n x).cls = ℚ₀cls.newton_raphson_step q.cls n x.cls := rfl
@[simp] theorem cls_newton_raphson_seq (q : ℚ₀) (n : Peano.ℕ₂) (k : ℕ₀) :
    (newton_raphson_seq q n k).cls = ℚ₀cls.newton_raphson_seq q.cls n k := rfl

-- ── Lemas de potencia que faltaban (Q0Ops ya tiene pow_zero/succ/one/add/nonneg/…) ──

theorem one_pow (n : ℕ₀) : (1 : ℚ₀).pow n = 1 := ext _ _ (ℚ₀cls.one_pow n)
theorem pow_pos {x : ℚ₀} (k : ℕ₀) (hx : 0 < x) : 0 < x.pow k := ℚ₀cls.pow_pos k hx
theorem pow_ne_zero_of_pos {x : ℚ₀} (hx : 0 < x) (n : ℕ₀) : x.pow n ≠ 0 :=
  ne_zero_iff_cls.mpr (ℚ₀cls.pow_ne_zero_of_pos hx n)
theorem pow_mul_distrib (a b : ℚ₀) (n : ℕ₀) :
    (Mul.mul a b).pow n = Mul.mul (a.pow n) (b.pow n) :=
  ext _ _ (ℚ₀cls.pow_mul_distrib a.cls b.cls n)
theorem pow_inv (b : ℚ₀) (hb : 0 < b) (n : ℕ₀) : (b⁻¹).pow n = (b.pow n)⁻¹ :=
  ext _ _ (ℚ₀cls.pow_inv b.cls hb n)

-- ── Lemas de orden/aritmética que faltaban ──

theorem square_nonneg (x : ℚ₀) : (0:ℚ₀) ≤ Mul.mul x x := ℚ₀cls.square_nonneg x.cls
theorem zero_lt_one : (0:ℚ₀) < 1 := ℚ₀cls.zero_lt_one
theorem add_nonneg {a b : ℚ₀} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Add.add a b :=
  ℚ₀cls.add_nonneg ha hb
theorem add_pos {a b : ℚ₀} (ha : 0 < a) (hb : 0 < b) : 0 < Add.add a b := ℚ₀cls.add_pos ha hb
theorem mul_pos {a b : ℚ₀} (ha : 0 < a) (hb : 0 < b) : 0 < Mul.mul a b := ℚ₀cls.mul_pos_pub ha hb
theorem le_of_lt {a b : ℚ₀} (h : a < b) : a ≤ b := ℚ₀cls.le_of_lt h
theorem lt_of_le_of_ne {a b : ℚ₀} (h_le : a ≤ b) (h_ne : a ≠ b) : a < b :=
  ℚ₀cls.lt_of_le_of_ne h_le (fun hc => h_ne (ext a b hc))
theorem inv_pos {a : ℚ₀} (h : 0 < a) : 0 < a⁻¹ := ℚ₀cls.inv_pos h
theorem inv_ne_zero {a : ℚ₀} (h : a ≠ 0) : a⁻¹ ≠ 0 :=
  ne_zero_iff_cls.mpr (ℚ₀cls.inv_ne_zero (ne_zero_iff_cls.mp h))
theorem eq_zero_of_mul_eq_zero {a b : ℚ₀} (h : Mul.mul a b = 0) (hb : b ≠ 0) : a = 0 :=
  ext a 0 (ℚ₀cls.eq_zero_of_mul_eq_zero (congrArg ℚ₀.cls h) (ne_zero_iff_cls.mp hb))

-- ── Lemas específicos de la sucesión de Newton–Raphson ──

theorem newton_seq_pos (q : ℚ₀) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) :
    0 < newton_raphson_seq q n k := ℚ₀cls.newton_seq_pos q.cls n hq k
theorem newton_seq_pow_ge (q : ℚ₀) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) :
    q ≤ (newton_raphson_seq q n (σ k)).pow n.val.val :=
  ℚ₀cls.newton_seq_pow_ge q.cls n hq k
theorem newton_seq_monotone (q : ℚ₀) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) :
    newton_raphson_seq q n (σ (σ k)) ≤ newton_raphson_seq q n (σ k) :=
  ℚ₀cls.newton_seq_monotone q.cls n hq k
theorem newton_seq_le_x1 (q : ℚ₀) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) :
    newton_raphson_seq q n (σ k) ≤ newton_raphson_seq q n 1 :=
  ℚ₀cls.newton_seq_le_x1 q.cls n hq k

end ℚ₀
