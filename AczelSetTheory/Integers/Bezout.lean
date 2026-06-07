/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Bezout.lean
-- Identidad de Bézout extendida sobre ℤ₀.
--
-- Público:
--   ℤ₀.bezout_ofNat      : ∀ a b : ℕ₀, ∃ x y : ℤ₀,
--                             Add.add (Mul.mul (ofNat a) x) (Mul.mul (ofNat b) y) = ofNat (gcd a b)
--   ℤ₀.bezout_coprime_ofNat : gcd a b = 𝟙 → ∃ x y : ℤ₀,
--                             Add.add (Mul.mul (ofNat a) x) (Mul.mul (ofNat b) y) = 1
--   ℤ₀.bezout            : ∀ a b : ℤ₀, ∃ x y : ℤ₀,
--                             Add.add (Mul.mul a x) (Mul.mul b y) = gcdZ a b
--   ℤ₀.bezout_coprime     : gcdZ a b = 1 → ∃ x y : ℤ₀,
--                             Add.add (Mul.mul a x) (Mul.mul b y) = 1
--   ℤ₀.bezoutCoeffs      : ℤ₀ → ℤ₀ → ℤ₀ × ℤ₀
--                             función computable; (x,y) := bezoutCoeffs a b satisface
--                             a·x + b·y = gcdZ a b  (spec pendiente)
--
-- Notas de diseño:
-- - peanolib declara `notation a "+" b => Peano.Add.add a b` (global en Add.lean).
--   Esta notación compite con `HAdd.hAdd`, haciendo que `a + b` sea ambiguo cuando
--   a b : ℤ₀.  Solución adoptada en todo el proyecto (ver Basic.lean §295):
--   usar Add.add y Mul.mul explícitamente en los enunciados de teoremas.
-- - La forma substractiva de Bézout en ℕ₀ (bezout_natform) se levanta a ℤ₀
--   vía ofNat_sub_ofNat (puente privado).
-- - El caso general (ℤ₀) se reduce a bezout_ofNat vía descomposición de signo
--   (todo entero es ±ofNat de su valor absoluto): sin sorry.
-- - `bezoutCoeffs` implementa el algoritmo extendido de Euclides directamente sobre ℕ₀
--   (via `extEuclidNat`) y ajusta el signo. `gcd_step` ya es público en peanolib (b7ccbd0).
-- - Prerrequisito de M5B (inverso modular en ZModN p).
--
-- Dependencies: AczelSetTheory.Integers.Basic, AczelSetTheory.Integers.Arithmetic,
--               AczelSetTheory.Integers.Order, Peano.PeanoNat.Arith
-- @axiom_system: ZF (sin elección)
-- @importance: high
-- M5B.0 (2026-06-06): bezout_ofNat y bezout_coprime_ofNat completos.
-- M5B   (2026-06-06): bezout y bezout_coprime generales completos (0 sorry).

import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.Arithmetic
import AczelSetTheory.Integers.Order
import Peano.PeanoNat.Arith

-- Abrimos sub-namespaces de Peano que no tienen conflicto con ℤ₀.
-- NO abrimos Peano ni Peano.Add (causarían la ambigüedad descrita arriba).
open Peano.Sub Peano.Order Peano.Arith

namespace ℤ₀

-- ============================================================
-- Sección 0: Lemas privados de puente ℕ₀ ↔ ℤ₀
-- ============================================================

/-- Si ¬ le₀ m n, entonces sub n m = 𝟘 (sustracción truncada en ℕ₀). -/
private theorem sub_of_not_le {n m : ℕ₀} (h : ¬ le₀ m n) : sub n m = 𝟘 :=
  dif_neg h

/-- ofNat conmuta con sub natural cuando m ≤ n:
    ofNat (sub n m) = Add.add (ofNat n) (Neg.neg (ofNat m)). -/
private theorem ofNat_sub_ofNat {m n : ℕ₀} (h : le₀ m n) :
    ofNat (sub n m) = Add.add (ofNat n) (Neg.neg (ofNat m)) := by
  have key : Add.add (ofNat (sub n m)) (ofNat m) = ofNat n := by
    rw [← ofNat_add]; exact congrArg ofNat (sub_k_add_k n m h)
  calc ofNat (sub n m)
      = Add.add (ofNat (sub n m)) 0 := (add_zero _).symm
    _ = Add.add (ofNat (sub n m)) (Add.add (ofNat m) (Neg.neg (ofNat m))) := by
          rw [add_neg_self]
    _ = Add.add (Add.add (ofNat (sub n m)) (ofNat m)) (Neg.neg (ofNat m)) :=
          (add_assoc _ _ _).symm
    _ = Add.add (ofNat n) (Neg.neg (ofNat m)) := by rw [key]

-- ============================================================
-- Sección 1: Bézout para ℕ₀ (coeficientes en ℤ₀)
-- ============================================================

/-- Identidad de Bézout para naturales (coeficientes en ℤ₀):
    existen `x y : ℤ₀` tales que `ofNat a · x + ofNat b · y = ofNat (gcd a b)`. -/
theorem bezout_ofNat (a b : ℕ₀) :
    ∃ x y : ℤ₀,
      Add.add (Mul.mul (ofNat a) x) (Mul.mul (ofNat b) y) = ofNat (gcd a b) := by
  obtain ⟨n, m, h | h⟩ := bezout_natform a b
  · -- Caso 1: gcd a b = sub (mul n a) (mul m b)
    by_cases hgcd : gcd a b = 𝟘
    · -- gcd = 0 ↔ a = b = 0
      obtain ⟨ha, hb⟩ := (gcd_eq_zero_iff a b).mp hgcd
      refine ⟨0, 0, ?_⟩
      have ha' : ofNat a = 0 := by rw [ha]; exact ofNat_zero
      have hb' : ofNat b = 0 := by rw [hb]; exact ofNat_zero
      have hg' : ofNat (gcd a b) = 0 := by rw [hgcd]; exact ofNat_zero
      rw [ha', hb', mul_zero, hg', add_zero]
    · -- gcd ≠ 0 → le₀ (mul m b) (mul n a)
      have hle : le₀ (Peano.Mul.mul m b) (Peano.Mul.mul n a) :=
        Classical.byContradiction (fun h_nle =>
          absurd (h.trans (sub_of_not_le h_nle)) hgcd)
      have key : Add.add (ofNat (Peano.Mul.mul n a)) (Neg.neg (ofNat (Peano.Mul.mul m b))) =
                 ofNat (gcd a b) := by
        have h1 : ofNat (sub (Peano.Mul.mul n a) (Peano.Mul.mul m b)) =
                  ofNat (gcd a b) := congrArg ofNat h.symm
        rw [ofNat_sub_ofNat hle] at h1; exact h1
      refine ⟨ofNat n, Neg.neg (ofNat m), ?_⟩
      rw [mul_neg, ← ofNat_mul a n, ← ofNat_mul b m,
          show Peano.Mul.mul a n = Peano.Mul.mul n a from Peano.Mul.mul_comm a n,
          show Peano.Mul.mul b m = Peano.Mul.mul m b from Peano.Mul.mul_comm b m]
      exact key
  · -- Caso 2: gcd a b = sub (mul n b) (mul m a)
    by_cases hgcd : gcd a b = 𝟘
    · obtain ⟨ha, hb⟩ := (gcd_eq_zero_iff a b).mp hgcd
      refine ⟨0, 0, ?_⟩
      have ha' : ofNat a = 0 := by rw [ha]; exact ofNat_zero
      have hb' : ofNat b = 0 := by rw [hb]; exact ofNat_zero
      have hg' : ofNat (gcd a b) = 0 := by rw [hgcd]; exact ofNat_zero
      rw [ha', hb', mul_zero, hg', add_zero]
    · have hle : le₀ (Peano.Mul.mul m a) (Peano.Mul.mul n b) :=
        Classical.byContradiction (fun h_nle =>
          absurd (h.trans (sub_of_not_le h_nle)) hgcd)
      have key : Add.add (ofNat (Peano.Mul.mul n b)) (Neg.neg (ofNat (Peano.Mul.mul m a))) =
                 ofNat (gcd a b) := by
        have h1 : ofNat (sub (Peano.Mul.mul n b) (Peano.Mul.mul m a)) =
                  ofNat (gcd a b) := congrArg ofNat h.symm
        rw [ofNat_sub_ofNat hle] at h1; exact h1
      refine ⟨Neg.neg (ofNat m), ofNat n, ?_⟩
      rw [mul_neg, ← ofNat_mul a m, ← ofNat_mul b n,
          show Peano.Mul.mul a m = Peano.Mul.mul m a from Peano.Mul.mul_comm a m,
          show Peano.Mul.mul b n = Peano.Mul.mul n b from Peano.Mul.mul_comm b n,
          add_comm]
      exact key

-- ============================================================
-- Sección 2: Corolarios sobre coprimalidad (ℕ₀)
-- ============================================================

/-- Si `gcd a b = 1`, existen `x y : ℤ₀` con `ofNat a · x + ofNat b · y = 1`. -/
theorem bezout_coprime_ofNat {a b : ℕ₀} (h : gcd a b = 𝟙) :
    ∃ x y : ℤ₀,
      Add.add (Mul.mul (ofNat a) x) (Mul.mul (ofNat b) y) = 1 := by
  obtain ⟨x, y, hxy⟩ := bezout_ofNat a b
  exact ⟨x, y, by rw [hxy, h, ofNat_one]⟩

-- ============================================================
-- Sección 3: Bézout general para ℤ₀
-- ============================================================
-- Reducción a bezout_ofNat vía descomposición de signo
-- (todo entero es ±ofNat de su valor absoluto).

/-- Descomposición de signo: todo entero es `ofNat (toNat |a|)` o su negativo. -/
private theorem self_eq_or_neg_ofNat_toNat_abs (a : ℤ₀) :
    a = ofNat (toNat (abs a)) ∨ a = Neg.neg (ofNat (toNat (abs a))) := by
  have habs : abs a = ofNat (toNat (abs a)) := nonneg_eq_ofNat (abs_nonneg a)
  by_cases h : (0 : ℤ₀) ≤ a
  · left
    have haa : abs a = a := by unfold abs; rw [if_pos h]
    exact haa.symm.trans habs
  · right
    have haa : abs a = Neg.neg a := by unfold abs; rw [if_neg h]
    have key : Neg.neg a = ofNat (toNat (abs a)) := haa.symm.trans habs
    have hneg := congrArg Neg.neg key
    rwa [neg_neg] at hneg

/-- Absorción del signo en un coeficiente de Bézout: para todo `x`, existe `x'`
    tal que `ofNat (toNat |a|) · x = a · x'`. -/
private theorem mul_ofNat_toNat_abs (a x : ℤ₀) :
    ∃ x' : ℤ₀, Mul.mul (ofNat (toNat (abs a))) x = Mul.mul a x' := by
  rcases self_eq_or_neg_ofNat_toNat_abs a with ha | ha
  · exact ⟨x, by rw [← ha]⟩
  · refine ⟨Neg.neg x, ?_⟩
    have heq : ofNat (toNat (abs a)) = Neg.neg a := by
      have hc := congrArg Neg.neg ha
      rw [neg_neg] at hc
      exact hc.symm
    rw [heq, neg_mul, mul_neg]

/-- Identidad de Bézout para enteros: existen `x y : ℤ₀` con `a·x + b·y = gcdZ a b`. -/
theorem bezout (a b : ℤ₀) :
    ∃ x y : ℤ₀, Add.add (Mul.mul a x) (Mul.mul b y) = gcdZ a b := by
  obtain ⟨x, y, hxy⟩ := bezout_ofNat (toNat (abs a)) (toNat (abs b))
  obtain ⟨x', hx'⟩ := mul_ofNat_toNat_abs a x
  obtain ⟨y', hy'⟩ := mul_ofNat_toNat_abs b y
  refine ⟨x', y', ?_⟩
  have hg : gcdZ a b = ofNat (Peano.Arith.gcd (toNat (abs a)) (toNat (abs b))) := rfl
  rw [hg, ← hx', ← hy']
  exact hxy

/-- Si `gcdZ a b = 1`, existen `x y : ℤ₀` con `a·x + b·y = 1`. -/
theorem bezout_coprime {a b : ℤ₀} (h : gcdZ a b = 1) :
    ∃ x y : ℤ₀, Add.add (Mul.mul a x) (Mul.mul b y) = 1 := by
  obtain ⟨x, y, hxy⟩ := bezout a b
  exact ⟨x, y, hxy.trans h⟩

-- ============================================================
-- Sección 4: Función computable de coeficientes de Bézout
-- ============================================================
-- Implementación directa del algoritmo extendido de Euclides.
-- La invariante es: para `(x, y) := extEuclidNat a b`,
--   `ofNat a · x + ofNat b · y = ofNat (gcd a b)`.
-- `extEuclidNat_spec` prueba la correctness usando `Peano.Arith.gcd_step`
-- (público desde peanolib v2.0.0-12-gb7ccbd0).

set_option linter.unusedVariables false in
/-- Algoritmo extendido de Euclides sobre ℕ₀, devolviendo coeficientes en ℤ₀.
    Recurrencia: `extEuclidNat a b = (t, s − (a/b)·t)`
    donde `(s, t) = extEuclidNat b (a % b)`. Termina porque `a % b < b`. -/
def extEuclidNat (a b : ℕ₀) : ℤ₀ × ℤ₀ :=
  if hb : b = 𝟘 then
    (1, 0)    -- gcd(a,0)=a : 1·a + 0·0 = a ✓
  else
    let r := Peano.Div.mod a b     -- r = a % b  (< b)
    let q := Peano.Div.div a b     -- q = a / b
    let (s, t) := extEuclidNat b r
    -- inv(b,r): b·s + r·t = gcd(b,r) = gcd(a,b)
    -- a = q·b + r  →  r = a − q·b
    -- b·s + (a − q·b)·t = gcd(a,b)
    -- a·t + b·(s − q·t) = gcd(a,b)
    (t, Add.add s (Neg.neg (Mul.mul (ofNat q) t)))
termination_by b
decreasing_by exact Peano.Div.mod_lt a b hb

/-- Lema algebraico auxiliar: `(A+C)+(D+(-A)) = D+C` en ℤ₀. -/
private theorem bezout_ring_cancel (A C D : ℤ₀) :
    Add.add (Add.add A C) (Add.add D (Neg.neg A)) = Add.add D C := by
  rw [← add_assoc (Add.add A C) D (Neg.neg A),
      add_assoc A C D,
      add_assoc A (Add.add C D) (Neg.neg A),
      add_comm (Add.add C D) (Neg.neg A),
      ← add_assoc A (Neg.neg A) (Add.add C D),
      add_neg_self A,
      zero_add,
      add_comm C D]

/-- Correctness de `extEuclidNat`: los coeficientes satisfacen la identidad de Bézout. -/
theorem extEuclidNat_spec (a b : ℕ₀) :
    Add.add (Mul.mul (ofNat a) (extEuclidNat a b).1)
            (Mul.mul (ofNat b) (extEuclidNat a b).2) =
    ofNat (Peano.Arith.gcd a b) := by
  induction b using Peano.WellFounded.well_founded_lt.induction generalizing a with
  | h b ih =>
    by_cases hb : b = 𝟘
    · -- Caso base: b = 0 → extEuclidNat a 0 = (1, 0)
      subst hb
      have h_base : extEuclidNat a 𝟘 = (1, 0) := by
        rw [extEuclidNat.eq_1 a 𝟘, dif_pos rfl]
      have h1 : (extEuclidNat a 𝟘).1 = 1 := by rw [h_base]
      have h2 : (extEuclidNat a 𝟘).2 = 0 := by rw [h_base]
      rw [h1, h2, Peano.Arith.gcd_zero_right, mul_one, ofNat_zero, mul_zero, add_zero]
    · -- Caso recursivo: b ≠ 0
      -- Componentes de extEuclidNat a b en función de extEuclidNat b r
      have heq : extEuclidNat a b =
          ((extEuclidNat b (Peano.Div.mod a b)).2,
           Add.add (extEuclidNat b (Peano.Div.mod a b)).1
                   (Neg.neg (Mul.mul (ofNat (Peano.Div.div a b))
                                     (extEuclidNat b (Peano.Div.mod a b)).2))) := by
        rw [extEuclidNat.eq_1 a b, dif_neg hb]
      have hc1 : (extEuclidNat a b).1 = (extEuclidNat b (Peano.Div.mod a b)).2 :=
        congrArg Prod.fst heq
      have hc2 : (extEuclidNat a b).2 =
                 Add.add (extEuclidNat b (Peano.Div.mod a b)).1
                         (Neg.neg (Mul.mul (ofNat (Peano.Div.div a b))
                                           (extEuclidNat b (Peano.Div.mod a b)).2)) :=
        congrArg Prod.snd heq
      -- Hipótesis inductiva: ofNat b · x + ofNat r · y = ofNat (gcd b r)
      have hlt : Peano.Div.mod a b < b := Peano.Div.mod_lt a b hb
      have ih_br := ih (Peano.Div.mod a b) hlt b
      -- Reescribir los coeficientes del objetivo
      -- hgcd_eq expresa gcd_step con Peano.Div.mod para compatibilidad con ih_br
      have hgcd_eq : Peano.Arith.gcd a b = Peano.Arith.gcd b (Peano.Div.mod a b) :=
        Peano.Arith.gcd_step a b hb
      rw [hc1, hc2, hgcd_eq, ← ih_br]
      -- Expandir ofNat a = ofNat q · ofNat b + ofNat r
      have hrw_a : ofNat a = Add.add (Mul.mul (ofNat (Peano.Div.div a b)) (ofNat b))
                                      (ofNat (Peano.Div.mod a b)) := by
        have hd := congrArg ofNat (Peano.Div.divMod_spec a b hb)
        rw [ofNat_add, ofNat_mul] at hd
        exact hd
      rw [hrw_a, right_distrib, left_distrib, mul_neg]
      -- Reescribir (q·b)·y = b·(q·y) para cancelar con -(b·(q·y))
      have hcomm :
          Mul.mul (Mul.mul (ofNat (Peano.Div.div a b)) (ofNat b))
                  (extEuclidNat b (Peano.Div.mod a b)).2 =
          Mul.mul (ofNat b) (Mul.mul (ofNat (Peano.Div.div a b))
                                      (extEuclidNat b (Peano.Div.mod a b)).2) := by
        rw [mul_comm (ofNat (Peano.Div.div a b)) (ofNat b), mul_assoc]
      rw [hcomm]
      -- Ahora la meta tiene la forma (A+C)+(D+(-A)) = D+C
      exact bezout_ring_cancel _ _ _

/-- Coeficientes de Bézout para enteros ℤ₀ vía descomposición por signo.
    Para `(x, y) := bezoutCoeffs a b` se tiene
    `Mul.mul a x + Mul.mul b y = gcdZ a b`.
    La prueba formal de esta propiedad (`bezoutCoeffs_spec`) está pendiente.
    Idea: `|a|·x' + |b|·y' = gcd(|a|,|b|)`  (de `extEuclidNat_spec`)
    →  `a·(x'·sign a) + b·(y'·sign b) = gcdZ a b`
    pues `a·sign(a) = |a|` (lema `mul_sign_eq_abs`, pendiente). -/
def bezoutCoeffs (a b : ℤ₀) : ℤ₀ × ℤ₀ :=
  let (x, y) := extEuclidNat (toNat (abs a)) (toNat (abs b))
  (Mul.mul x (sign a), Mul.mul y (sign b))

end ℤ₀
