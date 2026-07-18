/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Q0Order.lean
-- API de orden y valor absoluto del racional empaquetado ℚ₀ (cuerpo ordenado).
--
-- Bridges sobre la teoría de ℚ₀cls (Rationals/Basic.lean orden, Rationals/AbsVal.lean).
-- El orden, las operaciones y `absVal` del struct son DEFINICIONALMENTE los de su campo
-- `.cls` (instancias `LE`/`LT`, `@[simp] cls_*` de Q0.lean, y `absVal q := ofCls (…q.cls)`),
-- así que cada lema es term-mode directo — o `ext` para las igualdades. La teoría de
-- ℚ₀cls no se toca (ADR-023, migración de tipos). Se usa `Add.add`/`Mul.mul`/`Neg.neg`
-- explícito, como el resto de la teoría de ℚ₀ (el elaborador de `+` se confunde con la
-- coerción `ℤ₀ → ℚ₀`/literales en juego).

import AczelSetTheory.Rationals.Q0

namespace ℚ₀

-- ── Orden parcial y total ──
theorem le_refl (a : ℚ₀) : a ≤ a := ℚ₀cls.le_refl a.cls
theorem le_antisymm {a b : ℚ₀} (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  ext a b (ℚ₀cls.le_antisymm h1 h2)
theorem le_trans {a b c : ℚ₀} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := ℚ₀cls.le_trans h1 h2
theorem le_total (a b : ℚ₀) : a ≤ b ∨ b ≤ a := ℚ₀cls.le_total a.cls b.cls

-- ── Compatibilidad con la suma ──
theorem add_le_add_left {a b : ℚ₀} (h : a ≤ b) (c : ℚ₀) : Add.add c a ≤ Add.add c b :=
  ℚ₀cls.add_le_add_left h c.cls
theorem add_le_add_right {a b : ℚ₀} (h : a ≤ b) (c : ℚ₀) : Add.add a c ≤ Add.add b c :=
  ℚ₀cls.add_le_add_right h c.cls
theorem add_le_add {a b c d : ℚ₀} (h1 : a ≤ b) (h2 : c ≤ d) : Add.add a c ≤ Add.add b d :=
  ℚ₀cls.add_le_add h1 h2
theorem neg_le_neg {a b : ℚ₀} (h : a ≤ b) : Neg.neg b ≤ Neg.neg a := ℚ₀cls.neg_le_neg h

-- ── Compatibilidad con el producto ──
theorem mul_nonneg {a b : ℚ₀} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Mul.mul a b :=
  ℚ₀cls.mul_nonneg ha hb
theorem mul_le_mul_right_of_nonneg {a b c : ℚ₀} (h1 : a ≤ b) (h2 : 0 ≤ c) :
    Mul.mul a c ≤ Mul.mul b c := ℚ₀cls.mul_le_mul_right_of_nonneg h1 h2
theorem mul_le_mul_left_of_nonneg {a b c : ℚ₀} (h1 : a ≤ b) (h2 : 0 ≤ c) :
    Mul.mul c a ≤ Mul.mul c b := ℚ₀cls.mul_le_mul_left_of_nonneg h1 h2
theorem mul_le_mul {a b c d : ℚ₀} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ a) (h4 : 0 ≤ c) :
    Mul.mul a c ≤ Mul.mul b d := ℚ₀cls.mul_le_mul h1 h2 h3 h4

-- ── Valor absoluto (cuerpo ordenado con módulo) ──
theorem absVal_of_nonneg {q : ℚ₀} (h : 0 ≤ q) : absVal q = q :=
  ext _ _ (ℚ₀cls.absVal_of_nonneg h)
theorem absVal_of_nonpos {q : ℚ₀} (h : q ≤ 0) : absVal q = Neg.neg q :=
  ext _ _ (ℚ₀cls.absVal_of_nonpos h)
theorem absVal_zero : absVal (0 : ℚ₀) = 0 := ext _ _ ℚ₀cls.absVal_zero
theorem absVal_nonneg (q : ℚ₀) : 0 ≤ absVal q := ℚ₀cls.absVal_nonneg q.cls
theorem absVal_neg (q : ℚ₀) : absVal (Neg.neg q) = absVal q :=
  ext _ _ (ℚ₀cls.absVal_neg q.cls)
theorem absVal_zero_iff (q : ℚ₀) : absVal q = 0 ↔ q = 0 := by
  constructor
  · intro h; exact ext _ _ ((ℚ₀cls.absVal_zero_iff q.cls).mp (congrArg ℚ₀.cls h))
  · intro h; exact ext _ _ ((ℚ₀cls.absVal_zero_iff q.cls).mpr (congrArg ℚ₀.cls h))
theorem absVal_sub_comm (a b : ℚ₀) : absVal (Sub.sub a b) = absVal (Sub.sub b a) :=
  ext _ _ (ℚ₀cls.absVal_sub_comm a.cls b.cls)
theorem absVal_mul (a b : ℚ₀) : absVal (Mul.mul a b) = Mul.mul (absVal a) (absVal b) :=
  ext _ _ (ℚ₀cls.absVal_mul a.cls b.cls)
theorem le_absVal (q : ℚ₀) : q ≤ absVal q := ℚ₀cls.le_absVal q.cls
theorem neg_le_absVal (q : ℚ₀) : Neg.neg q ≤ absVal q := ℚ₀cls.neg_le_absVal q.cls
theorem absVal_add_le (a b : ℚ₀) : absVal (Add.add a b) ≤ Add.add (absVal a) (absVal b) :=
  ℚ₀cls.absVal_add_le a.cls b.cls

end ℚ₀
