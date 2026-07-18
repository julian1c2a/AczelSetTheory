/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Z0Order.lean
-- API de orden del entero empaquetado ℤ₀ (anillo conmutativo ordenado).
--
-- Bridges sobre la teoría de orden de ℤ₀cls (Integers/Order.lean). El orden y las
-- operaciones del struct son DEFINICIONALMENTE los de su campo `.cls` (ver las
-- instancias `LE`/`LT` y los `@[simp] cls_*` de Z0.lean), así que cada lema es
-- term-mode directo — la clase de equivalencia hace todo el trabajo (ADR-023,
-- migración de tipos). La teoría de ℤ₀cls no se toca.

import AczelSetTheory.Integers.Z0
import AczelSetTheory.Integers.Order

namespace ℤ₀

-- ── Orden parcial y total ──
theorem le_refl (a : ℤ₀) : a ≤ a := ℤ₀cls.le_refl a.cls
theorem le_antisymm {a b : ℤ₀} (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  ext a b (ℤ₀cls.le_antisymm h1 h2)
theorem le_trans {a b c : ℤ₀} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := ℤ₀cls.le_trans h1 h2
theorem le_total (a b : ℤ₀) : a ≤ b ∨ b ≤ a := ℤ₀cls.le_total a.cls b.cls

-- ── Orden estricto ──
theorem lt_iff_le_not_le (a b : ℤ₀) : a < b ↔ a ≤ b ∧ ¬ b ≤ a :=
  ℤ₀cls.lt_iff_le_not_le a.cls b.cls
theorem le_of_lt {a b : ℤ₀} (h : a < b) : a ≤ b := ℤ₀cls.le_of_lt h
theorem lt_of_le_of_lt {a b c : ℤ₀} (h1 : a ≤ b) (h2 : b < c) : a < c :=
  ℤ₀cls.lt_of_le_of_lt h1 h2
theorem lt_of_lt_of_le {a b c : ℤ₀} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  ℤ₀cls.lt_of_lt_of_le h1 h2

-- ── Compatibilidad con la suma ──
-- (se usa `Add.add` explícito, como el resto de la teoría de ℤ₀: el elaborador de `+`
--  se confunde con la coerción `ℕ₀ → ℤ₀` en juego.)
theorem add_le_add_left (a b c : ℤ₀) (h : b ≤ c) : Add.add a b ≤ Add.add a c :=
  ℤ₀cls.add_le_add_left a.cls b.cls c.cls h
theorem add_le_add_right {b c : ℤ₀} (h : b ≤ c) (a : ℤ₀) : Add.add b a ≤ Add.add c a :=
  ℤ₀cls.add_le_add_right h a.cls
theorem add_lt_add_left (a b c : ℤ₀) (h : b < c) : Add.add a b < Add.add a c :=
  ℤ₀cls.add_lt_add_left a.cls b.cls c.cls h
theorem add_lt_add_right {b c : ℤ₀} (h : b < c) (a : ℤ₀) : Add.add b a < Add.add c a :=
  ℤ₀cls.add_lt_add_right h a.cls
theorem neg_le_neg {a b : ℤ₀} (h : a ≤ b) : Neg.neg b ≤ Neg.neg a := ℤ₀cls.neg_le_neg h

-- ── Compatibilidad con el producto ──
theorem mul_pos {a b : ℤ₀} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := ℤ₀cls.mul_pos ha hb
theorem mul_nonneg {a b : ℤ₀} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := ℤ₀cls.mul_nonneg ha hb
theorem mul_le_mul_right_of_nonneg {a b c : ℤ₀} (h1 : a ≤ b) (h2 : 0 ≤ c) : a * c ≤ b * c :=
  ℤ₀cls.mul_le_mul_right_of_nonneg h1 h2
theorem mul_le_mul_left_of_nonneg {a b c : ℤ₀} (h1 : a ≤ b) (h2 : 0 ≤ c) : c * a ≤ c * b :=
  ℤ₀cls.mul_le_mul_left_of_nonneg h1 h2

end ℤ₀
