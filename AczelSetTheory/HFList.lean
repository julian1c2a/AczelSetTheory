/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/HFList.lean
-- HFList: secuencias finitas ordenadas de HFSets (listas, no conjuntos).
-- FinList: n-tuplas de HFSets (listas de longitud fija en ℕ₀).
--
-- Contraste con HFSet:
--   HFSet  = cociente extensional de CList  → sin orden, sin repetición
--   HFList = PList HFSet                    → con orden, con repetición
--   FinList n = {l : HFList // l.length = n} → n-tupla de HFSets

import AczelSetTheory.HFSets
import AczelSetTheory.PList.Fin0

open Peano

-- ─────────────────────────────────────────────────────────────────
-- HFList
-- ─────────────────────────────────────────────────────────────────

/-- Una secuencia finita ordenada de `HFSet`s.  A diferencia de `HFSet`,
    conserva el **orden** de los elementos y admite **repeticiones**. -/
abbrev HFList := PList HFSet

namespace HFList

-- ─────────────────────────────────────────────────────────────────
-- Longitud y vacuidad
-- ─────────────────────────────────────────────────────────────────

/-- Longitud de una `HFList`, medida en ℕ₀. -/
def length (l : HFList) : ℕ₀ := PList.length l

@[simp] theorem length_nil : length PList.nil = 𝟘 := rfl

@[simp] theorem length_cons (h : HFSet) (t : HFList) :
    length (PList.cons h t) = σ (length t) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Acceso: get? (parcial) y get (total via Fin₀)
-- ─────────────────────────────────────────────────────────────────

/-- Acceso por índice ℕ₀; devuelve `Option HFSet`. -/
def get? (l : HFList) (i : ℕ₀) : Option HFSet := PList.get? l i

/-- Acceso total garantizado por un índice acotado `Fin₀ (l.length)`. -/
def get (l : HFList) (i : Fin₀ (l.length)) : HFSet := PList.get l i

-- ─────────────────────────────────────────────────────────────────
-- Constructores y operaciones básicas
-- ─────────────────────────────────────────────────────────────────

/-- HFList vacía. -/
def nil : HFList := PList.nil

/-- Antepone un `HFSet` a una `HFList`. -/
def cons (x : HFSet) (l : HFList) : HFList := PList.cons x l

/-- Concatenación de dos `HFList`s. -/
def append (l₁ l₂ : HFList) : HFList := PList.append l₁ l₂

instance : Append HFList := ⟨append⟩

/-- Longitud de la concatenación. -/
theorem length_append (l₁ l₂ : HFList) :
    length (l₁ ++ l₂) = add (length l₁) (length l₂) := by
  unfold length append
  induction l₁ with
  | nil => simp [PList.append, PList.length, Peano.Add.zero_add]
  | cons h t ih =>
    simp only [PList.length_cons, PList.append]
    rw [ih]
    simp [Peano.Add.succ_add]

-- ─────────────────────────────────────────────────────────────────
-- Membresía
-- ─────────────────────────────────────────────────────────────────

/-- Pertenencia proposicional en `HFList` (por posición, no extensional). -/
def Mem (x : HFSet) (l : HFList) : Prop := PList.Mem x l

instance : Membership HFSet HFList := ⟨fun l x => Mem x l⟩

-- ─────────────────────────────────────────────────────────────────
-- Conversión HFList → HFSet (olvida el orden, elimina dups)
-- ─────────────────────────────────────────────────────────────────

-- No definimos esta conversión aquí para no necesitar los axiomas
-- de unión/inserción; se hará en Operations cuando estén disponibles.

end HFList

-- ─────────────────────────────────────────────────────────────────
-- FinList: n-tupla de HFSets
-- ─────────────────────────────────────────────────────────────────

/-- Una n-tupla de `HFSet`s: lista de longitud exactamente `n` en ℕ₀.
    Generaliza el par ordenado a aridad arbitraria. -/
def FinList (n : ℕ₀) : Type := { l : HFList // l.length = n }

namespace FinList

variable {n m : ℕ₀}

-- ─────────────────────────────────────────────────────────────────
-- Constructor y acceso
-- ─────────────────────────────────────────────────────────────────

/-- Extrae la `HFList` subyacente. -/
def toHFList (t : FinList n) : HFList := t.val

/-- Acceso total al i-ésimo componente de la n-tupla. -/
def get (t : FinList n) (i : Fin₀ n) : HFSet :=
  t.val.get (t.prop ▸ i)

/-- La longitud de una `FinList n` es siempre `n`. -/
theorem length_eq (t : FinList n) : t.val.length = n := t.prop

-- ─────────────────────────────────────────────────────────────────
-- n-tupla vacía y singleton
-- ─────────────────────────────────────────────────────────────────

/-- La 0-tupla (tupla vacía). -/
def empty : FinList 𝟘 := ⟨HFList.nil, rfl⟩

/-- Singleton: 1-tupla con un solo elemento. -/
def singleton (x : HFSet) : FinList (σ 𝟘) :=
  ⟨HFList.cons x HFList.nil, rfl⟩

-- ─────────────────────────────────────────────────────────────────
-- Consing: anteponer un elemento sube la aridad en 1
-- ─────────────────────────────────────────────────────────────────

/-- Antepone un `HFSet` a una n-tupla produciendo una (σ n)-tupla. -/
def cons (x : HFSet) (t : FinList n) : FinList (σ n) :=
  ⟨HFList.cons x t.val, by simp [HFList.length_cons, t.prop]⟩

-- ─────────────────────────────────────────────────────────────────
-- Igualdad extensional (componente a componente)
-- ─────────────────────────────────────────────────────────────────

theorem ext {t s : FinList n} (h : t.val = s.val) : t = s :=
  Subtype.ext h

end FinList
