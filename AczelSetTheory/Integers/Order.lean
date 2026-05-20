/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Order.lean
-- Orden total en ℤ₀: a ≤ b ↔ a.repr.1 + b.repr.2 ≤ a.repr.2 + b.repr.1 (en ℕ₀).
--
-- Público:
--   instance : LE ℤ₀, LT ℤ₀
--   instDecidableLE, instDecidableLT
--   ℤ₀.le_refl, le_antisymm, le_trans, le_total
--   ℤ₀.lt_iff_le_not_le
--   ℤ₀.ofNat_le, ofNat_lt, zero_le_ofNat
--   ℤ₀.add_le_add_left
--   ℤ₀.neg_le_neg

import AczelSetTheory.Integers.Basic
import Peano.PeanoNat.Decidable

namespace ℤ₀

open Peano Peano.Add Peano.Sub Peano.Mul Peano.Order

-- ─────────────────────────────────────────────────────────────────────────────
-- Instancias de orden
-- a ≤ b se define via le₀ en los representantes canónicos
-- ─────────────────────────────────────────────────────────────────────────────

instance : LE ℤ₀ where
  le a b := le₀ (add a.repr.1 b.repr.2) (add a.repr.2 b.repr.1)

instance : LT ℤ₀ where
  lt a b := a ≤ b ∧ ¬ b ≤ a

-- ─────────────────────────────────────────────────────────────────────────────
-- Lema auxiliar de despliegue
-- omega₀ requires @LE.le ℕ₀ (not le₀) so helpers expose ≤ notation.
-- ─────────────────────────────────────────────────────────────────────────────

private theorem le_iff (a b : ℤ₀) :
    a ≤ b ↔ (add a.repr.1 b.repr.2 : ℕ₀) ≤ add a.repr.2 b.repr.1 :=
  Iff.rfl

private theorem le_iff_mp {a b : ℤ₀} (h : a ≤ b) :
    (add a.repr.1 b.repr.2 : ℕ₀) ≤ add a.repr.2 b.repr.1 := h

private theorem le_iff_mpr {a b : ℤ₀}
    (h : (add a.repr.1 b.repr.2 : ℕ₀) ≤ add a.repr.2 b.repr.1) : a ≤ b := h

-- ─────────────────────────────────────────────────────────────────────────────
-- Decidibilidad
-- ─────────────────────────────────────────────────────────────────────────────

instance instDecidableLE (a b : ℤ₀) : Decidable (a ≤ b) :=
  show Decidable ((add a.repr.1 b.repr.2 : ℕ₀) ≤ add a.repr.2 b.repr.1) from
    inferInstance

instance instDecidableLT (a b : ℤ₀) : Decidable (a < b) :=
  show Decidable (a ≤ b ∧ ¬ b ≤ a) from inferInstance

-- ─────────────────────────────────────────────────────────────────────────────
-- Propiedades de orden
-- ─────────────────────────────────────────────────────────────────────────────

theorem le_refl (a : ℤ₀) : a ≤ a :=
  le_iff_mpr (by omega₀)

theorem le_antisymm {a b : ℤ₀} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  have h1' := le_iff_mp h1
  have h2' := le_iff_mp h2
  have heq : add a.repr.1 b.repr.2 = add a.repr.2 b.repr.1 := by omega₀
  apply repr_inj
  rcases repr_normalized a with ha | ha <;> rcases repr_normalized b with hb | hb
  · exact Prod.ext (ha.trans hb.symm) (by omega₀)
  · exact Prod.ext (ha.trans (by omega₀ : b.repr.1 = 𝟘).symm)
                   ((by omega₀ : a.repr.2 = 𝟘).trans hb.symm)
  · exact Prod.ext ((by omega₀ : a.repr.1 = 𝟘).trans hb.symm)
                   (ha.trans (by omega₀ : b.repr.2 = 𝟘).symm)
  · exact Prod.ext (by omega₀) (ha.trans hb.symm)

theorem le_trans {a b c : ℤ₀} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  have h1' := le_iff_mp h1
  have h2' := le_iff_mp h2
  rcases repr_normalized b with hb | hb
  · exact le_iff_mpr (by omega₀)
  · exact le_iff_mpr (by omega₀)

theorem le_total (a b : ℤ₀) : a ≤ b ∨ b ≤ a := by
  by_cases h : (add a.repr.1 b.repr.2 : ℕ₀) ≤ add a.repr.2 b.repr.1
  · exact Or.inl (le_iff_mpr h)
  · exact Or.inr (le_iff_mpr (by omega₀))

theorem lt_iff_le_not_le (a b : ℤ₀) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := Iff.rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- Compatibilidad con ofNat
-- ─────────────────────────────────────────────────────────────────────────────

theorem zero_le_ofNat (n : ℕ₀) : (0 : ℤ₀) ≤ ofNat n := by
  have h0 : (0 : ℤ₀).repr = (𝟘, 𝟘) := by
    show (ofNat 𝟘).repr = (𝟘, 𝟘); exact repr_ofNat 𝟘
  exact le_iff_mpr (by rw [h0, repr_ofNat]; omega₀)

theorem ofNat_le {m n : ℕ₀} (h : (m : ℕ₀) ≤ n) : ofNat m ≤ ofNat n :=
  le_iff_mpr (by simp only [repr_ofNat]; omega₀)

theorem le_ofNat_iff {m n : ℕ₀} : ofNat m ≤ ofNat n ↔ (m : ℕ₀) ≤ n := by
  constructor
  · intro hle
    have h := le_iff_mp hle
    simp only [repr_ofNat] at h
    omega₀
  · exact ofNat_le

theorem ofNat_lt {m n : ℕ₀} (h : (m : ℕ₀) ≤ n) (hne : m ≠ n) : ofNat m < ofNat n := by
  refine ⟨ofNat_le h, fun hba => ?_⟩
  rw [le_ofNat_iff] at hba
  exact hne (by omega₀)

-- ─────────────────────────────────────────────────────────────────────────────
-- Monotonía de la suma
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_le_add_left (a b c : ℤ₀) (h : b ≤ c) : Add.add a b ≤ Add.add a c := by
  have h' := le_iff_mp h
  have hab := repr_add_intEq a b
  have hac := repr_add_intEq a c
  show HAdd.hAdd a b ≤ HAdd.hAdd a c
  exact le_iff_mpr (by omega₀)

-- ─────────────────────────────────────────────────────────────────────────────
-- Negación invierte el orden
-- ─────────────────────────────────────────────────────────────────────────────

theorem neg_le_neg {a b : ℤ₀} (h : a ≤ b) : -b ≤ -a := by
  have h' := le_iff_mp h
  have ha := repr_neg_intEq a
  have hb := repr_neg_intEq b
  apply le_iff_mpr
  rcases repr_normalized a with ha₀ | ha₀ <;> rcases repr_normalized b with hb₀ | hb₀ <;> omega₀

-- ─────────────────────────────────────────────────────────────────────────────
-- Relaciones ≤ / <
-- ─────────────────────────────────────────────────────────────────────────────

theorem le_of_lt {a b : ℤ₀} (h : a < b) : a ≤ b := h.1

theorem lt_of_le_of_lt {a b c : ℤ₀} (h1 : a ≤ b) (h2 : b < c) : a < c :=
  ⟨le_trans h1 h2.1, fun hca => h2.2 (le_trans hca h1)⟩

theorem lt_of_lt_of_le {a b c : ℤ₀} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  ⟨le_trans h1.1 h2, fun hca => h1.2 (le_trans h2 hca)⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- Monotonía de la suma (derecha)
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_le_add_right {b c : ℤ₀} (h : b ≤ c) (a : ℤ₀) : Add.add b a ≤ Add.add c a := by
  have h' := le_iff_mp h
  have hba := repr_add_intEq b a
  have hca := repr_add_intEq c a
  show HAdd.hAdd b a ≤ HAdd.hAdd c a
  exact le_iff_mpr (by omega₀)

-- ─────────────────────────────────────────────────────────────────────────────
-- Cancelación por la izquierda
-- ─────────────────────────────────────────────────────────────────────────────

private theorem add_left_cancel_le {a b c : ℤ₀} (h : Add.add a b ≤ Add.add a c) : b ≤ c := by
  have h' := le_iff_mp (show HAdd.hAdd a b ≤ HAdd.hAdd a c from h)
  have hab := repr_add_intEq a b
  have hac := repr_add_intEq a c
  rcases repr_normalized (HAdd.hAdd a b) with hn | hn <;>
  rcases repr_normalized (HAdd.hAdd a c) with hm | hm <;>
  simp only [hn, hm] at hab hac h' <;>
  exact le_iff_mpr (by omega₀)

-- ─────────────────────────────────────────────────────────────────────────────
-- Monotonía estricta de la suma
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_lt_add_left (a b c : ℤ₀) (h : b < c) : Add.add a b < Add.add a c :=
  ⟨add_le_add_left a b c h.1, fun hle => h.2 (add_left_cancel_le hle)⟩

theorem add_lt_add_right {b c : ℤ₀} (h : b < c) (a : ℤ₀) : Add.add b a < Add.add c a := by
  refine ⟨add_le_add_right h.1 a, fun hle => h.2 ?_⟩
  apply add_left_cancel_le (a := a)
  rwa [add_comm a c, add_comm a b]

-- ─────────────────────────────────────────────────────────────────────────────
-- Positividad del producto
-- ─────────────────────────────────────────────────────────────────────────────

private theorem pos_repr {a : ℤ₀} (ha : 0 < a) : a.repr.2 = 𝟘 ∧ a.repr.1 ≠ 𝟘 := by
  have h2 : ¬ (add a.repr.1 (0 : ℤ₀).repr.2 ≤ add a.repr.2 (0 : ℤ₀).repr.1) :=
    fun h => ha.2 (le_iff_mpr h)
  have h0 : (0 : ℤ₀).repr = (𝟘, 𝟘) := by
    show (ofNat 𝟘).repr = (𝟘, 𝟘); exact repr_ofNat 𝟘
  simp only [h0] at h2
  rcases repr_normalized a with ha₀ | ha₀
  · exfalso; exact h2 (by rw [ha₀]; omega₀)
  · exact ⟨ha₀, fun heq => h2 (by rw [heq, ha₀]; omega₀)⟩

private theorem eq_ofNat_of_pos {a : ℤ₀} (ha : 0 < a) : a = ofNat a.repr.1 :=
  repr_inj (by rw [repr_ofNat]; exact Prod.ext rfl (pos_repr ha).1)

theorem mul_pos {a b : ℤ₀} (ha : 0 < a) (hb : 0 < b) : 0 < Mul.mul a b := by
  obtain ⟨_, ha1⟩ := pos_repr ha
  obtain ⟨_, hb1⟩ := pos_repr hb
  rw [eq_ofNat_of_pos ha, eq_ofNat_of_pos hb, ← ofNat_mul]
  have hpos := Peano.Mul.mul_pos (pos_of_ne_zero a.repr.1 ha1) (pos_of_ne_zero b.repr.1 hb1)
  have hne : Peano.Mul.mul a.repr.1 b.repr.1 ≠ 𝟘 := lt_0_then_neq_0 hpos
  exact ofNat_lt (Or.inl hpos) (Ne.symm hne)

end ℤ₀
