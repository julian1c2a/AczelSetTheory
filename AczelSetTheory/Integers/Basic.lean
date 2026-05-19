/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Basic.lean
-- ℤ₀: enteros como cociente de (ℕ₀ × ℕ₀) por (a,b) ~ (c,d) ↔ a+d = b+c.
-- Representante canónico: el primero o el segundo componente es siempre 𝟘.
--
-- Público:
--   ℤ₀                            : tipo de los enteros
--   ℤ₀.repr                       : ℤ₀ → ℕ₀ × ℕ₀  (representante canónico)
--   instances: Zero, One, Add, Neg, Mul, Sub
--   ℤ₀.negOne                     : el entero -1
--   ℤ₀.ofNat                      : ℕ₀ → ℤ₀  (embedding inyectivo)
--   Leyes de anillo conmutativo:
--     ℤ₀.add_comm, add_assoc, zero_add, add_zero
--     ℤ₀.add_neg_self, neg_add_self, neg_neg
--     ℤ₀.mul_comm, mul_assoc, one_mul, mul_one, zero_mul, mul_zero
--     ℤ₀.left_distrib, right_distrib, neg_mul, mul_neg
--   ℤ₀.ofNat_injective, ofNat_add, ofNat_mul

import AczelSetTheory.PList.Omega0
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
-- Provides DecidableRel (@LE.le ℕ₀ _), needed for `if p.2 ≤ p.1` in normalize.
import Peano.PeanoNat.Decidable

-- ─────────────────────────────────────────────────────────────────────────────
-- Sección privada: definiciones y compatibilidad para el cociente.
-- `open Peano ...` permite usar `add`, `mul`, `sub`, `le₀` directamente aquí.
-- ─────────────────────────────────────────────────────────────────────────────

section PrivateDefs

open Peano Peano.Add Peano.Sub Peano.Mul Peano.Order

-- ─────────────────────────────────────────────────────────────────────────────
-- Relación de equivalencia en ℕ₀ × ℕ₀
-- ─────────────────────────────────────────────────────────────────────────────

private def intEq (p q : ℕ₀ × ℕ₀) : Prop :=
  add p.1 q.2 = add p.2 q.1

private theorem intEq_refl (p : ℕ₀ × ℕ₀) : intEq p p :=
  add_comm p.1 p.2

private theorem intEq_symm {p q : ℕ₀ × ℕ₀} (h : intEq p q) : intEq q p :=
  (add_comm q.1 p.2).trans (h.symm.trans (add_comm p.1 q.2))

private theorem intEq_trans {p q r : ℕ₀ × ℕ₀} (h1 : intEq p q) (h2 : intEq q r) :
    intEq p r := by
  unfold intEq at *; omega₀

private instance intSetoid : Setoid (ℕ₀ × ℕ₀) where
  r := intEq
  iseqv := ⟨intEq_refl, intEq_symm, intEq_trans⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- Tipo ℤ₀
-- ─────────────────────────────────────────────────────────────────────────────

/-- Los enteros: pares (positivo, negativo) de naturales módulo equivalencia.
    El representante canónico tiene un componente igual a 𝟘. -/
def ℤ₀ := Quotient intSetoid

namespace ℤ₀

private abbrev mk (p : ℕ₀ × ℕ₀) : ℤ₀ := Quotient.mk intSetoid p

private theorem mk_eq_iff {p q : ℕ₀ × ℕ₀} : mk p = mk q ↔ intEq p q := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

-- ─────────────────────────────────────────────────────────────────────────────
-- Representante canónico
-- ─────────────────────────────────────────────────────────────────────────────

-- Uses `p.2 ≤ p.1` (LE typeclass) so that omega₀ can process it via ψ_le_iff.
-- The `DecidableRel (@LE.le ℕ₀ _)` instance from Peano.PeanoNat.Decidable
-- provides the required `Decidable (p.2 ≤ p.1)`.
private def normalize (p : ℕ₀ × ℕ₀) : ℕ₀ × ℕ₀ :=
  if p.2 ≤ p.1 then (sub p.1 p.2, 𝟘) else (𝟘, sub p.2 p.1)

private theorem normalize_eq_of_equiv {p q : ℕ₀ × ℕ₀} (h : intEq p q) :
    normalize p = normalize q := by
  have h_eq : add p.1 q.2 = add p.2 q.1 := h
  unfold normalize
  by_cases hp : p.2 ≤ p.1
  · by_cases hq : q.2 ≤ q.1
    · rw [if_pos hp, if_pos hq]
      have hp1 := sub_k_add_k p.1 p.2 hp
      have hq1 := sub_k_add_k q.1 q.2 hq
      exact Prod.ext (by omega₀) rfl
    · exfalso; omega₀
  · by_cases hq : q.2 ≤ q.1
    · exfalso; omega₀
    · rw [if_neg hp, if_neg hq]
      have hp' : p.1 ≤ p.2 := lt_imp_le p.1 p.2 (nle_then_gt p.2 p.1 hp)
      have hq' : q.1 ≤ q.2 := lt_imp_le q.1 q.2 (nle_then_gt q.2 q.1 hq)
      have hp1 := sub_k_add_k p.2 p.1 hp'
      have hq1 := sub_k_add_k q.2 q.1 hq'
      exact Prod.ext rfl (by omega₀)

/-- El representante canónico de un ℤ₀ (un componente siempre es 𝟘). -/
def repr (z : ℤ₀) : ℕ₀ × ℕ₀ :=
  Quotient.lift normalize (fun _ _ h => normalize_eq_of_equiv h) z

-- ─────────────────────────────────────────────────────────────────────────────
-- Constantes y embedding
-- ─────────────────────────────────────────────────────────────────────────────

instance : Zero ℤ₀ where zero := mk (𝟘, 𝟘)
instance : One  ℤ₀ where one  := mk (𝟙, 𝟘)

/-- El entero -1. -/
def negOne : ℤ₀ := mk (𝟘, 𝟙)

/-- Embedding inyectivo de ℕ₀ en ℤ₀. -/
def ofNat (n : ℕ₀) : ℤ₀ := mk (n, 𝟘)

-- ─────────────────────────────────────────────────────────────────────────────
-- Operaciones internas (Peano.Add y Peano.Mul en scope aquí)
-- ─────────────────────────────────────────────────────────────────────────────

private def addRaw (p q : ℕ₀ × ℕ₀) : ℕ₀ × ℕ₀ := (add p.1 q.1, add p.2 q.2)
private def negRaw (p : ℕ₀ × ℕ₀)   : ℕ₀ × ℕ₀ := (p.2, p.1)
private def mulRaw (p q : ℕ₀ × ℕ₀) : ℕ₀ × ℕ₀ :=
  (add (mul p.1 q.1) (mul p.2 q.2), add (mul p.1 q.2) (mul p.2 q.1))

-- ─────────────────────────────────────────────────────────────────────────────
-- Compatibilidad con intEq
-- ─────────────────────────────────────────────────────────────────────────────

private theorem addRaw_respects (p₁ q₁ p₂ q₂ : ℕ₀ × ℕ₀)
    (h1 : intEq p₁ p₂) (h2 : intEq q₁ q₂) : intEq (addRaw p₁ q₁) (addRaw p₂ q₂) := by
  unfold intEq addRaw at *; omega₀

private theorem negRaw_respects (p q : ℕ₀ × ℕ₀) (h : intEq p q) :
    intEq (negRaw p) (negRaw q) := h.symm

private theorem mulRaw_left_compat (p₁ p₂ q : ℕ₀ × ℕ₀) (h : intEq p₁ p₂) :
    intEq (mulRaw p₁ q) (mulRaw p₂ q) := by
  unfold intEq mulRaw at *
  have h1 : add (mul p₁.1 q.1) (mul p₂.2 q.1) = add (mul p₁.2 q.1) (mul p₂.1 q.1) := by
    have := congrArg (fun x => mul x q.1) h; simp only [add_mul] at this; exact this
  have h2 : add (mul p₁.1 q.2) (mul p₂.2 q.2) = add (mul p₁.2 q.2) (mul p₂.1 q.2) := by
    have := congrArg (fun x => mul x q.2) h; simp only [add_mul] at this; exact this
  omega₀

private theorem mulRaw_right_compat (p q₁ q₂ : ℕ₀ × ℕ₀) (h : intEq q₁ q₂) :
    intEq (mulRaw p q₁) (mulRaw p q₂) := by
  unfold intEq mulRaw at *
  have h1 : add (mul p.1 q₁.1) (mul p.1 q₂.2) = add (mul p.1 q₁.2) (mul p.1 q₂.1) := by
    have := congrArg (fun x => mul p.1 x) h; simp only [mul_add] at this; exact this
  have h2 : add (mul p.2 q₁.1) (mul p.2 q₂.2) = add (mul p.2 q₁.2) (mul p.2 q₂.1) := by
    have := congrArg (fun x => mul p.2 x) h; simp only [mul_add] at this; exact this
  omega₀

private theorem mulRaw_respects (p₁ q₁ p₂ q₂ : ℕ₀ × ℕ₀)
    (h1 : intEq p₁ p₂) (h2 : intEq q₁ q₂) : intEq (mulRaw p₁ q₁) (mulRaw p₂ q₂) := by
  have hl := mulRaw_left_compat p₁ p₂ q₁ h1
  have hr := mulRaw_right_compat p₂ q₁ q₂ h2
  unfold intEq mulRaw at *; omega₀

-- ─────────────────────────────────────────────────────────────────────────────
-- Instancias de operación
-- ─────────────────────────────────────────────────────────────────────────────

instance : Add ℤ₀ where
  add a b := Quotient.liftOn₂ a b (fun p q => mk (addRaw p q))
    (fun p₁ q₁ p₂ q₂ h1 h2 => Quotient.sound (addRaw_respects p₁ q₁ p₂ q₂ h1 h2))

instance : Neg ℤ₀ where
  neg a := Quotient.liftOn a (fun p => mk (negRaw p))
    (fun p q h => Quotient.sound (negRaw_respects p q h))

instance : Mul ℤ₀ where
  mul a b := Quotient.liftOn₂ a b (fun p q => mk (mulRaw p q))
    (fun p₁ q₁ p₂ q₂ h1 h2 => Quotient.sound (mulRaw_respects p₁ q₁ p₂ q₂ h1 h2))

instance : Sub ℤ₀ where sub a b := HAdd.hAdd a (Neg.neg b)

-- ─────────────────────────────────────────────────────────────────────────────
-- Lemas de cómputo
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_mk (p q : ℕ₀ × ℕ₀) : HAdd.hAdd (mk p) (mk q) = mk (addRaw p q) := rfl
theorem neg_mk (p : ℕ₀ × ℕ₀) : Neg.neg (mk p) = mk (negRaw p) := rfl
theorem mul_mk (p q : ℕ₀ × ℕ₀) : HMul.hMul (mk p) (mk q) = mk (mulRaw p q) := rfl

end ℤ₀

end PrivateDefs

-- ─────────────────────────────────────────────────────────────────────────────
-- Leyes de anillo.
-- Note: the ring law theorem types use `+`, `*`, `-` (unary) from the standard
-- Lean 4 instances (HAdd.hAdd, HMul.hMul, Neg.neg) via our Add/Mul/Neg ℤ₀
-- instances. We do NOT open Peano here, because opening Peano causes the global
-- Peano `+` notation to take precedence over the built-in infixl, giving type
-- errors when `a b : ℤ₀`. Without `open Peano`, the built-in `infixl:65 " + "
-- => HAdd.hAdd` correctly resolves to our Add ℤ₀ instance.
-- ─────────────────────────────────────────────────────────────────────────────

namespace ℤ₀

-- ─────────────────────────────────────────────────────────────────────────────
-- Leyes de adición
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_comm (a b : ℤ₀) : Add.add a b = Add.add b a := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  rcases Quotient.exists_rep b with ⟨q, rfl⟩
  show HAdd.hAdd (mk p) (mk q) = HAdd.hAdd (mk q) (mk p)
  rw [add_mk, add_mk, mk_eq_iff]; unfold intEq addRaw; omega₀

theorem add_assoc (a b c : ℤ₀) : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  rcases Quotient.exists_rep b with ⟨q, rfl⟩
  rcases Quotient.exists_rep c with ⟨r, rfl⟩
  show HAdd.hAdd (HAdd.hAdd (mk p) (mk q)) (mk r) =
       HAdd.hAdd (mk p) (HAdd.hAdd (mk q) (mk r))
  rw [add_mk, add_mk, add_mk, add_mk, mk_eq_iff]; unfold intEq addRaw; omega₀

theorem zero_add (a : ℤ₀) : Add.add 0 a = a := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  show HAdd.hAdd (mk (𝟘, 𝟘)) (mk p) = mk p
  rw [add_mk, mk_eq_iff]; unfold intEq addRaw; omega₀

theorem add_zero (a : ℤ₀) : Add.add a 0 = a := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  show HAdd.hAdd (mk p) (mk (𝟘, 𝟘)) = mk p
  rw [add_mk, mk_eq_iff]; unfold intEq addRaw; omega₀

theorem add_neg_self (a : ℤ₀) : Add.add a (Neg.neg a) = 0 := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  show HAdd.hAdd (mk p) (Neg.neg (mk p)) = mk (𝟘, 𝟘)
  rw [neg_mk, add_mk, mk_eq_iff]; unfold intEq addRaw negRaw; omega₀

theorem neg_add_self (a : ℤ₀) : Add.add (Neg.neg a) a = 0 := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  show HAdd.hAdd (Neg.neg (mk p)) (mk p) = mk (𝟘, 𝟘)
  rw [neg_mk, add_mk, mk_eq_iff]; unfold intEq addRaw negRaw; omega₀

theorem neg_neg (a : ℤ₀) : Neg.neg (Neg.neg a) = a := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  show Neg.neg (Neg.neg (mk p)) = mk p
  rw [neg_mk, neg_mk, mk_eq_iff]; unfold intEq negRaw; omega₀

-- ─────────────────────────────────────────────────────────────────────────────
-- Leyes de multiplicación
-- ─────────────────────────────────────────────────────────────────────────────

theorem mul_comm (a b : ℤ₀) : Mul.mul a b = Mul.mul b a := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  rcases Quotient.exists_rep b with ⟨q, rfl⟩
  show HMul.hMul (mk p) (mk q) = HMul.hMul (mk q) (mk p)
  rw [mul_mk, mul_mk, mk_eq_iff]
  simp only [intEq, mulRaw,
    Peano.Mul.mul_comm p.1 q.1, Peano.Mul.mul_comm p.1 q.2,
    Peano.Mul.mul_comm p.2 q.1, Peano.Mul.mul_comm p.2 q.2]
  omega₀

theorem mul_assoc (a b c : ℤ₀) : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c) := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  rcases Quotient.exists_rep b with ⟨q, rfl⟩
  rcases Quotient.exists_rep c with ⟨r, rfl⟩
  show HMul.hMul (HMul.hMul (mk p) (mk q)) (mk r) =
       HMul.hMul (mk p) (HMul.hMul (mk q) (mk r))
  rw [mul_mk, mul_mk, mul_mk, mul_mk, mk_eq_iff]
  simp only [intEq, mulRaw,
    Peano.Mul.add_mul, Peano.Mul.mul_add, Peano.Mul.mul_assoc]
  omega₀

theorem one_mul (a : ℤ₀) : Mul.mul 1 a = a := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  show HMul.hMul (mk (𝟙, 𝟘)) (mk p) = mk p
  rw [mul_mk, mk_eq_iff]
  simp only [intEq, mulRaw, Peano.Mul.one_mul, Peano.Mul.zero_mul, Peano.Add.add_zero]
  omega₀

theorem mul_one (a : ℤ₀) : Mul.mul a 1 = a := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  show HMul.hMul (mk p) (mk (𝟙, 𝟘)) = mk p
  rw [mul_mk, mk_eq_iff]
  simp only [intEq, mulRaw,
    Peano.Mul.mul_one, Peano.Mul.mul_zero, Peano.Add.add_zero, Peano.Add.zero_add]
  omega₀

theorem zero_mul (a : ℤ₀) : Mul.mul 0 a = 0 := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  show HMul.hMul (mk (𝟘, 𝟘)) (mk p) = mk (𝟘, 𝟘)
  rw [mul_mk, mk_eq_iff]
  simp only [intEq, mulRaw, Peano.Mul.zero_mul, Peano.Add.add_zero]

theorem mul_zero (a : ℤ₀) : Mul.mul a 0 = 0 := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  show HMul.hMul (mk p) (mk (𝟘, 𝟘)) = mk (𝟘, 𝟘)
  rw [mul_mk, mk_eq_iff]
  simp only [intEq, mulRaw, Peano.Mul.mul_zero, Peano.Add.add_zero]

-- ─────────────────────────────────────────────────────────────────────────────
-- Distributividad
-- ─────────────────────────────────────────────────────────────────────────────

theorem left_distrib (a b c : ℤ₀) : Mul.mul a (Add.add b c) = Add.add (Mul.mul a b) (Mul.mul a c) := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  rcases Quotient.exists_rep b with ⟨q, rfl⟩
  rcases Quotient.exists_rep c with ⟨r, rfl⟩
  show HMul.hMul (mk p) (HAdd.hAdd (mk q) (mk r)) =
       HAdd.hAdd (HMul.hMul (mk p) (mk q)) (HMul.hMul (mk p) (mk r))
  rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk, mk_eq_iff]
  simp only [intEq, mulRaw, addRaw, Peano.Mul.mul_add]
  omega₀

theorem right_distrib (a b c : ℤ₀) : Mul.mul (Add.add a b) c = Add.add (Mul.mul a c) (Mul.mul b c) := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  rcases Quotient.exists_rep b with ⟨q, rfl⟩
  rcases Quotient.exists_rep c with ⟨r, rfl⟩
  show HMul.hMul (HAdd.hAdd (mk p) (mk q)) (mk r) =
       HAdd.hAdd (HMul.hMul (mk p) (mk r)) (HMul.hMul (mk q) (mk r))
  rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk, mk_eq_iff]
  simp only [intEq, mulRaw, addRaw, Peano.Mul.add_mul]
  omega₀

-- ─────────────────────────────────────────────────────────────────────────────
-- Signo y multiplicación
-- ─────────────────────────────────────────────────────────────────────────────

theorem neg_mul (a b : ℤ₀) : Mul.mul (Neg.neg a) b = Neg.neg (Mul.mul a b) := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  rcases Quotient.exists_rep b with ⟨q, rfl⟩
  show HMul.hMul (Neg.neg (mk p)) (mk q) = Neg.neg (HMul.hMul (mk p) (mk q))
  rw [neg_mk, mul_mk, mul_mk, neg_mk, mk_eq_iff]
  simp only [intEq, mulRaw, negRaw]
  omega₀

theorem mul_neg (a b : ℤ₀) : Mul.mul a (Neg.neg b) = Neg.neg (Mul.mul a b) := by
  rcases Quotient.exists_rep a with ⟨p, rfl⟩
  rcases Quotient.exists_rep b with ⟨q, rfl⟩
  show HMul.hMul (mk p) (Neg.neg (mk q)) = Neg.neg (HMul.hMul (mk p) (mk q))
  rw [neg_mk, mul_mk, mul_mk, neg_mk, mk_eq_iff]
  simp only [intEq, mulRaw, negRaw]
  omega₀

-- ─────────────────────────────────────────────────────────────────────────────
-- Embedding ofNat
-- ─────────────────────────────────────────────────────────────────────────────

theorem ofNat_zero : ofNat 𝟘 = 0 := rfl
theorem ofNat_one  : ofNat 𝟙 = 1 := rfl

theorem ofNat_add (m n : ℕ₀) : ofNat (Peano.Add.add m n) = Add.add (ofNat m) (ofNat n) := by
  show mk (Peano.Add.add m n, 𝟘) = HAdd.hAdd (mk (m, 𝟘)) (mk (n, 𝟘))
  rw [add_mk]; rfl

theorem ofNat_mul (m n : ℕ₀) : ofNat (Peano.Mul.mul m n) = Mul.mul (ofNat m) (ofNat n) := by
  show mk (Peano.Mul.mul m n, 𝟘) = HMul.hMul (mk (m, 𝟘)) (mk (n, 𝟘))
  rw [mul_mk, mk_eq_iff]
  simp only [intEq, mulRaw,
    Peano.Mul.mul_zero, Peano.Mul.zero_mul,
    Peano.Add.add_zero, Peano.Add.zero_add]

theorem ofNat_injective {m n : ℕ₀} (h : ofNat m = ofNat n) : m = n := by
  have heq := mk_eq_iff.mp h
  unfold intEq at heq
  omega₀

end ℤ₀
