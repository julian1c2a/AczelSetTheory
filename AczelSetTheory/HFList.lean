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
    length (l₁ ++ l₂) = add (length l₁) (length l₂) :=
  PList.length_append l₁ l₂

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

-- ─────────────────────────────────────────────────────────────────
-- Lemas de membresía
-- ─────────────────────────────────────────────────────────────────

theorem not_mem_nil (x : HFSet) : ¬ x ∈ (nil : HFList) :=
  PList.not_mem_nil x

theorem mem_cons_iff (x h : HFSet) (t : HFList) :
    x ∈ HFList.cons h t ↔ x = h ∨ x ∈ t :=
  PList.Mem_cons_iff x h t

-- ─────────────────────────────────────────────────────────────────
-- get? simp lemmas
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem get?_nil (i : ℕ₀) : (nil : HFList).get? i = none := rfl

@[simp] theorem get?_cons_zero (h : HFSet) (t : HFList) :
    (cons h t).get? 𝟘 = some h := rfl

@[simp] theorem get?_cons_succ (h : HFSet) (t : HFList) (i : ℕ₀) :
    (cons h t).get? (σ i) = (get? t i) := rfl

-- ─────────────────────────────────────────────────────────────────
-- take / drop
-- ─────────────────────────────────────────────────────────────────

/-- Primeros `k` elementos de una `HFList`. -/
def take (k : ℕ₀) (l : HFList) : HFList := PList.take k l

/-- Descarta los primeros `k` elementos de una `HFList`. -/
def drop (k : ℕ₀) (l : HFList) : HFList := PList.drop k l

theorem length_take_le (k : ℕ₀) (l : HFList) (h : k ≤ length l) :
    length (take k l) = k :=
  PList.length_take_le k l h

theorem add_length_drop (k : ℕ₀) (l : HFList) (h : k ≤ length l) :
    Peano.Add.add k (length (drop k l)) = length l :=
  PList.add_length_drop k l h

theorem length_drop_le (k : ℕ₀) (l : HFList) (h : k ≤ length l) :
    length (drop k l) = Peano.Sub.sub (length l) k :=
  PList.length_drop_le k l h

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
  t.val.get ⟨i.val, by rw [t.property]; exact i.isLt⟩

/-- La longitud de una `FinList n` es siempre `n`. -/
theorem length_eq (t : FinList n) : t.val.length = n := t.property

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
  ⟨HFList.cons x t.val, congrArg (σ ·) t.property⟩

-- ─────────────────────────────────────────────────────────────────
-- Igualdad extensional (componente a componente)
-- ─────────────────────────────────────────────────────────────────

theorem ext {t s : FinList n} (h : t.val = s.val) : t = s :=
  Subtype.ext h

theorem ext_iff {t s : FinList n} : t = s ↔ t.val = s.val :=
  Subtype.ext_iff

-- ─────────────────────────────────────────────────────────────────
-- Concatenación: (add n m)-tupla desde n-tupla y m-tupla
-- ─────────────────────────────────────────────────────────────────

/-- Concatena una n-tupla con una m-tupla produciendo una (n+m)-tupla. -/
def append (t : FinList n) (s : FinList m) : FinList (add n m) :=
  ⟨t.val ++ s.val, by rw [HFList.length_append, t.property, s.property]⟩

/-- Longitud de la concatenación. -/
theorem length_append (t : FinList n) (s : FinList m) :
    (t.append s).val.length = add n m :=
  (t.append s).property

-- ─────────────────────────────────────────────────────────────────
-- Map: aplicar una función a cada componente
-- ─────────────────────────────────────────────────────────────────

/-- Aplica una función a cada componente, preservando la aridad. -/
def map (f : HFSet → HFSet) (t : FinList n) : FinList n :=
  ⟨PList.map f t.val, by
    show PList.length (PList.map f t.val) = n
    rw [PList.length_map]; exact t.property⟩

-- ─────────────────────────────────────────────────────────────────
-- ZipWith: combinar dos n-tuplas componente a componente
-- ─────────────────────────────────────────────────────────────────

/-- Aplica una función binaria componente a componente a dos n-tuplas. -/
def zipWith (f : HFSet → HFSet → HFSet) (t s : FinList n) : FinList n :=
  ⟨PList.zipWith f t.val s.val, by
    show PList.length (PList.zipWith f t.val s.val) = n
    exact (PList.length_zipWith_same f t.val s.val
      (t.property.trans s.property.symm)).trans t.property⟩

@[simp] theorem zipWith_nil (f : HFSet → HFSet → HFSet) :
    zipWith f (empty : FinList 𝟘) empty = empty := rfl

@[simp] theorem zipWith_cons (f : HFSet → HFSet → HFSet)
    (x y : HFSet) (t s : FinList n) :
    zipWith f (cons x t) (cons y s) = cons (f x y) (zipWith f t s) := by
  apply FinList.ext; rfl

-- ─────────────────────────────────────────────────────────────────
-- Head y Tail: primer componente y resto de una (σ n)-tupla
-- ─────────────────────────────────────────────────────────────────

/-- Primer componente de una (σ n)-tupla. -/
def head (t : FinList (σ n)) : HFSet :=
  match h : t.val with
  | PList.nil => by
      exfalso
      have := t.property; rw [h, HFList.length_nil] at this; omega₀
  | PList.cons x _ => x

/-- Resto (n-tupla) de una (σ n)-tupla. -/
def tail (t : FinList (σ n)) : FinList n :=
  match h : t.val with
  | PList.nil => by
      exfalso
      have := t.property; rw [h, HFList.length_nil] at this; omega₀
  | PList.cons _ rest =>
    ⟨rest, by
      have := t.property
      simp only [h, HFList.length_cons] at this
      omega₀⟩

-- ─────────────────────────────────────────────────────────────────
-- Lemas de reducción para head y tail
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem head_cons (x : HFSet) (t : FinList n) : head (cons x t) = x := rfl

@[simp] theorem tail_cons (x : HFSet) (t : FinList n) : tail (cons x t) = t :=
  FinList.ext rfl

/-- Descomposición: toda (σ n)-tupla es `cons (head t) (tail t)`. -/
theorem cons_head_tail (t : FinList (σ n)) : cons (head t) (tail t) = t := by
  rcases t with ⟨l, hl⟩
  cases l with
  | nil =>
      exfalso
      simp only [HFList.length_nil] at hl; omega₀
  | cons x rest =>
      apply FinList.ext; rfl

-- ─────────────────────────────────────────────────────────────────
-- Igualdad extensional componente a componente
-- ─────────────────────────────────────────────────────────────────

/-- Dos n-tuplas son iguales si y solo si coinciden en cada índice. -/
theorem extEq {t s : FinList n}
    (h : ∀ i : Fin₀ n, t.get i = s.get i) : t = s := by
  apply FinList.ext
  apply PList.plist_ext_get?
  intro i
  by_cases hlt : i < n
  · have htl : i < t.val.length := by rw [t.property]; exact hlt
    have hsl : i < s.val.length := by rw [s.property]; exact hlt
    have h' := h ⟨i, hlt⟩
    simp only [FinList.get, HFList.get] at h'
    rw [PList.get_eq_get? t.val ⟨i, htl⟩, PList.get_eq_get? s.val ⟨i, hsl⟩]
    exact congrArg some h'
  · have hge : n ≤ i := by
      simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_le_iff] at *; omega
    have tp : PList.length t.val = n := t.property
    have sp : PList.length s.val = n := s.property
    rw [PList.get?_none_of_ge t.val i (by rw [tp]; exact hge),
        PList.get?_none_of_ge s.val i (by rw [sp]; exact hge)]

-- ─────────────────────────────────────────────────────────────────
-- take / drop en FinList
-- ─────────────────────────────────────────────────────────────────

/-- Primeros `k` componentes de una n-tupla (requiere `k ≤ n`). -/
def take (k : ℕ₀) (t : FinList n) (h : k ≤ n) : FinList k :=
  ⟨HFList.take k t.val,
    HFList.length_take_le k t.val (by rw [t.property]; exact h)⟩

/-- Descarta los primeros `k` componentes de una n-tupla (requiere `k ≤ n`). -/
def drop (k : ℕ₀) (t : FinList n) (h : k ≤ n) : FinList (Peano.Sub.sub n k) :=
  ⟨HFList.drop k t.val, by
    rw [HFList.length_drop_le k t.val (by rw [t.property]; exact h), t.property]⟩

end FinList
