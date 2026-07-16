/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Polynomial.lean

import AczelSetTheory.PList.Basic
import AczelSetTheory.Rationals.Q0
import AczelSetTheory.Axioms.OrdinalNat

open Peano

namespace ℚ₀

-- ─────────────────────────────────────────────────────────────────
-- Polinomios sobre ℚ₀
-- ─────────────────────────────────────────────────────────────────

/-- Elimina los ceros a la derecha (los coeficientes de mayor grado nulos) -/
def trimZeros (l : PList ℚ₀) : PList ℚ₀ :=
  match l with
  | PList.nil => PList.nil
  | PList.cons h t =>
      let t' := trimZeros t
      if h.pair = (0 : ℚ₀).pair ∧ t'.isEmpty then PList.nil
      else PList.cons h t'

/-- Un polinomio sobre ℚ₀ es una lista de coeficientes, donde el último (si existe) no es cero. -/
def Polynomial := { l : PList ℚ₀ // trimZeros l = l }

namespace Polynomial

def zero : Polynomial := ⟨PList.nil, rfl⟩

instance : Zero Polynomial := ⟨zero⟩

/-- Grado del polinomio. Si es el polinomio nulo, devuelve 0 (o Option.none, pero usamos 0 para simplicidad) -/
def degree (p : Polynomial) : ℕ₀ :=
  match p.val with
  | PList.nil => 𝟘
  | PList.cons _ _ => Sub.sub p.val.length 𝟙

-- ─────────────────────────────────────────────────────────────────
-- Aritmética Polinómica
-- ─────────────────────────────────────────────────────────────────

/-- Suma de listas de coeficientes (componente a componente) -/
def addList (l1 l2 : PList ℚ₀) : PList ℚ₀ :=
  match l1, l2 with
  | PList.nil, l => l
  | l, PList.nil => l
  | PList.cons h1 t1, PList.cons h2 t2 =>
      PList.cons (h1 + h2) (addList t1 t2)

def add (p1 p2 : Polynomial) : Polynomial :=
  let sumList := addList p1.val p2.val
  ⟨trimZeros sumList, sorry⟩ -- Canonicalización

instance : Add Polynomial := ⟨add⟩

/-- Multiplicación por escalar -/
def smulList (c : ℚ₀) (l : PList ℚ₀) : PList ℚ₀ :=
  match l with
  | PList.nil => PList.nil
  | PList.cons h t => PList.cons (c * h) (smulList c t)

def smul (c : ℚ₀) (p : Polynomial) : Polynomial :=
  if c.pair = (0 : ℚ₀).pair then zero
  else ⟨trimZeros (smulList c p.val), sorry⟩

/-- Convolución de listas de coeficientes (multiplicación polinómica) -/
def mulList (l1 l2 : PList ℚ₀) : PList ℚ₀ :=
  match l1 with
  | PList.nil => PList.nil
  | PList.cons h1 t1 =>
      addList (smulList h1 l2) (PList.cons 0 (mulList t1 l2))

def mul (p1 p2 : Polynomial) : Polynomial :=
  ⟨trimZeros (mulList p1.val p2.val), sorry⟩

instance : Mul Polynomial := ⟨mul⟩

-- ─────────────────────────────────────────────────────────────────
-- Evaluación
-- ─────────────────────────────────────────────────────────────────

/-- Evaluación de Horner para una lista de coeficientes -/
def evalList (l : PList ℚ₀) (x : ℚ₀) : ℚ₀ :=
  match l with
  | PList.nil => 0
  | PList.cons h t => h + x * evalList t x

/-- Evalúa el polinomio en el punto `x` -/
def eval (p : Polynomial) (x : ℚ₀) : ℚ₀ :=
  evalList p.val x

-- ─────────────────────────────────────────────────────────────────
-- Monomios
-- ─────────────────────────────────────────────────────────────────

/-- Lista auxiliar para crear un monomio -/
def monomialList (c : ℚ₀) (k : ℕ₀) : PList ℚ₀ :=
  match k with
  | 𝟘 => PList.cons c PList.nil
  | σ n => PList.cons 0 (monomialList c n)

/-- Crea el monomio `c * x^k` -/
def monomial (c : ℚ₀) (k : ℕ₀) : Polynomial :=
  if c.pair = (0 : ℚ₀).pair then zero
  else ⟨trimZeros (monomialList c k), sorry⟩

end Polynomial

end ℚ₀
