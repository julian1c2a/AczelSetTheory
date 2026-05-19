/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Operations/Order.lean
-- Predicados de orden para relaciones sobre HFSets.
--
-- Predicados básicos (propiedades de una relación R en un conjunto A):
--   isReflexive, isIrreflexive, isSymmetric, isAntisymmetric,
--   isTransitive, isConnected, isTotal, isTrichotomous
--
-- Predicados compuestos (clases de órdenes):
--   isPreorder, isEquivRel, isPartialOrder, isStrictOrder,
--   isTotalOrder, isStrictTotalOrder
--
-- Predicados de elementos:
--   isMinimum, isMaximum, isMinimal, isMaximal
--
-- Cotas:
--   isLowerBound, isUpperBound, isInfimum, isSupremum
--
-- Bien fundada y buen orden:
--   isWellFounded, isStrictlyWellFounded, isWellOrder

import AczelSetTheory.Axioms.Subset
import AczelSetTheory.Axioms.Relation

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- Propiedades básicas de una relación R sobre un conjunto A
-- ─────────────────────────────────────────────────────────────────

/-- R es reflexiva en A: ∀ x ∈ A, ⟪x, x⟫ ∈ R. -/
def isReflexive (R A : HFSet) : Prop :=
  ∀ x ∈ A, ⟪x, x⟫ ∈ R

/-- R es irreflexiva en A: ∀ x ∈ A, ⟪x, x⟫ ∉ R. -/
def isIrreflexive (R A : HFSet) : Prop :=
  ∀ x ∈ A, ⟪x, x⟫ ∉ R

/-- R es simétrica en A: ∀ x y ∈ A, ⟪x, y⟫ ∈ R → ⟪y, x⟫ ∈ R. -/
def isSymmetric (R A : HFSet) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ⟪x, y⟫ ∈ R → ⟪y, x⟫ ∈ R

/-- R es antisimétrica en A: ⟪x, y⟫ ∈ R ∧ ⟪y, x⟫ ∈ R → x = y. -/
def isAntisymmetric (R A : HFSet) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ⟪x, y⟫ ∈ R → ⟪y, x⟫ ∈ R → x = y

/-- R es transitiva en A: ⟪x, y⟫ ∈ R ∧ ⟪y, z⟫ ∈ R → ⟪x, z⟫ ∈ R. -/
def isTransitive (R A : HFSet) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
    ⟪x, y⟫ ∈ R → ⟪y, z⟫ ∈ R → ⟪x, z⟫ ∈ R

/-- R es conexa en A: ∀ x y ∈ A con x ≠ y, ⟪x, y⟫ ∈ R ∨ ⟪y, x⟫ ∈ R. -/
def isConnected (R A : HFSet) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ⟪x, y⟫ ∈ R ∨ ⟪y, x⟫ ∈ R

/-- R es total (completa) en A: ∀ x y ∈ A, ⟪x, y⟫ ∈ R ∨ ⟪y, x⟫ ∈ R. -/
def isTotal (R A : HFSet) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ⟪x, y⟫ ∈ R ∨ ⟪y, x⟫ ∈ R

/-- R es tricotómica en A: ∀ x y ∈ A, ⟪x, y⟫ ∈ R ∨ x = y ∨ ⟪y, x⟫ ∈ R. -/
def isTrichotomous (R A : HFSet) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ⟪x, y⟫ ∈ R ∨ x = y ∨ ⟪y, x⟫ ∈ R

-- ─────────────────────────────────────────────────────────────────
-- Clases de órdenes (predicados compuestos)
-- ─────────────────────────────────────────────────────────────────

/-- R es un preorden en A: reflexiva y transitiva. -/
def isPreorder (R A : HFSet) : Prop :=
  isReflexive R A ∧ isTransitive R A

/-- R es una relación de equivalencia en A: reflexiva, simétrica y transitiva. -/
def isEquivRel (R A : HFSet) : Prop :=
  isReflexive R A ∧ isSymmetric R A ∧ isTransitive R A

/-- R es un orden parcial (no estricto) en A: reflexiva, antisimétrica y transitiva. -/
def isPartialOrder (R A : HFSet) : Prop :=
  isReflexive R A ∧ isAntisymmetric R A ∧ isTransitive R A

/-- R es un orden estricto en A: irreflexiva y transitiva. -/
def isStrictOrder (R A : HFSet) : Prop :=
  isIrreflexive R A ∧ isTransitive R A

/-- R es un orden total (no estricto) en A: orden parcial y total. -/
def isTotalOrder (R A : HFSet) : Prop :=
  isPartialOrder R A ∧ isTotal R A

/-- R es un orden total estricto en A: orden estricto y tricotómico. -/
def isStrictTotalOrder (R A : HFSet) : Prop :=
  isStrictOrder R A ∧ isTrichotomous R A

-- ─────────────────────────────────────────────────────────────────
-- Predicados de elementos (mínimo, máximo, minimal, maximal)
-- ─────────────────────────────────────────────────────────────────

/-- x es el mínimo de A respecto a R: x ∈ A y ∀ y ∈ A, ⟪x, y⟫ ∈ R. -/
def isMinimum (R A x : HFSet) : Prop :=
  x ∈ A ∧ ∀ y ∈ A, ⟪x, y⟫ ∈ R

/-- x es el máximo de A respecto a R: x ∈ A y ∀ y ∈ A, ⟪y, x⟫ ∈ R. -/
def isMaximum (R A x : HFSet) : Prop :=
  x ∈ A ∧ ∀ y ∈ A, ⟪y, x⟫ ∈ R

/-- x es minimal en A respecto a R: x ∈ A y nada en A es estrictamente menor.
    Para órdenes no estrictos: si ⟪y, x⟫ ∈ R entonces y = x (antisimetría local). -/
def isMinimal (R A x : HFSet) : Prop :=
  x ∈ A ∧ ∀ y ∈ A, ⟪y, x⟫ ∈ R → y = x

/-- x es maximal en A respecto a R: x ∈ A y nada en A es estrictamente mayor.
    Para órdenes no estrictos: si ⟪x, y⟫ ∈ R entonces y = x. -/
def isMaximal (R A x : HFSet) : Prop :=
  x ∈ A ∧ ∀ y ∈ A, ⟪x, y⟫ ∈ R → y = x

-- ─────────────────────────────────────────────────────────────────
-- Cotas e ínfimo/supremo
-- ─────────────────────────────────────────────────────────────────

/-- b es una cota inferior de A respecto a R: ∀ y ∈ A, ⟪b, y⟫ ∈ R. -/
def isLowerBound (R A b : HFSet) : Prop :=
  ∀ y ∈ A, ⟪b, y⟫ ∈ R

/-- b es una cota superior de A respecto a R: ∀ y ∈ A, ⟪y, b⟫ ∈ R. -/
def isUpperBound (R A b : HFSet) : Prop :=
  ∀ y ∈ A, ⟪y, b⟫ ∈ R

/-- b es el ínfimo (mayor cota inferior) de A respecto a R. -/
def isInfimum (R A b : HFSet) : Prop :=
  isLowerBound R A b ∧ ∀ c, isLowerBound R A c → ⟪c, b⟫ ∈ R

/-- b es el supremo (menor cota superior) de A respecto a R. -/
def isSupremum (R A b : HFSet) : Prop :=
  isUpperBound R A b ∧ ∀ c, isUpperBound R A c → ⟪b, c⟫ ∈ R

-- ─────────────────────────────────────────────────────────────────
-- Bien fundada y buen orden
-- ─────────────────────────────────────────────────────────────────

/-- R es bien fundada en A (no estricta): todo S ⊆ A no vacío tiene un mínimo.
    Adecuada para órdenes totales no estrictos (tipo ≤). -/
def isWellFounded (R A : HFSet) : Prop :=
  ∀ S, S ⊆ A → S ≠ empty → ∃ m, isMinimum R S m

/-- R es estrictamente bien fundada en A: todo S ⊆ A no vacío tiene un elemento
    en S sin predecesor en S respecto a R. Adecuada para órdenes estrictos (tipo <). -/
def isStrictlyWellFounded (R A : HFSet) : Prop :=
  ∀ S, S ⊆ A → S ≠ empty → ∃ m ∈ S, ∀ y ∈ S, ⟪y, m⟫ ∉ R

/-- R es un buen orden en A: orden total bien fundado. -/
def isWellOrder (R A : HFSet) : Prop :=
  isTotalOrder R A ∧ isWellFounded R A

end HFSet
