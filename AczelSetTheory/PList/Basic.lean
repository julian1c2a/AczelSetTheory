/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/PList/Basic.lean
-- Lista polimórfica propia con indexación en ℕ₀ (tipo de Peano).

import Peano.PeanoNat
import Peano.PeanoNat.Add

open Peano

/-- Lista polimórfica propia; todas las medidas de longitud viven en ℕ₀. -/
inductive PList (α : Type) : Type where
  | nil  : PList α
  | cons : α → PList α → PList α
  deriving Repr, Inhabited

namespace PList

variable {α β γ : Type}

-- ─────────────────────────────────────────────────────────────────
-- Longitud y comprobación de vacuidad
-- ─────────────────────────────────────────────────────────────────

def length : PList α → ℕ₀
  | nil      => 𝟘
  | cons _ t => σ (length t)

def isEmpty : PList α → Bool
  | nil      => true
  | cons _ _ => false

-- ─────────────────────────────────────────────────────────────────
-- Cabeza, cola y acceso por índice en ℕ₀
-- ─────────────────────────────────────────────────────────────────

def head? : PList α → Option α
  | nil      => none
  | cons h _ => some h

def tail : PList α → PList α
  | nil      => nil
  | cons _ t => t

def get? : PList α → ℕ₀ → Option α
  | nil,      _           => none
  | cons h _, .zero       => some h
  | cons _ t, .succ i     => get? t i

def getD (dflt : α) : PList α → ℕ₀ → α
  | nil,      _           => dflt
  | cons h _, .zero       => h
  | cons _ t, .succ i     => getD dflt t i

-- ─────────────────────────────────────────────────────────────────
-- Funciones de orden superior
-- ─────────────────────────────────────────────────────────────────

def map (f : α → β) : PList α → PList β
  | nil      => nil
  | cons h t => cons (f h) (map f t)

def foldl (f : β → α → β) (init : β) : PList α → β
  | nil      => init
  | cons h t => foldl f (f init h) t

def foldr (f : α → β → β) (init : β) : PList α → β
  | nil      => init
  | cons h t => f h (foldr f init t)

def any (p : α → Bool) : PList α → Bool
  | nil      => false
  | cons h t => p h || any p t

def all (p : α → Bool) : PList α → Bool
  | nil      => true
  | cons h t => p h && all p t

def filter (p : α → Bool) : PList α → PList α
  | nil      => nil
  | cons h t => if p h then cons h (filter p t) else filter p t

def append : PList α → PList α → PList α
  | nil,      ys => ys
  | cons h t, ys => cons h (append t ys)

instance : Append (PList α) := ⟨append⟩

def flatMap (f : α → PList β) : PList α → PList β
  | nil      => nil
  | cons h t => (f h).append (flatMap f t)

def reverse : PList α → PList α
  | nil      => nil
  | cons h t => (reverse t).append (cons h nil)

def zipWith (f : α → β → γ) : PList α → PList β → PList γ
  | nil,      _          => nil
  | _,        nil        => nil
  | cons a as, cons b bs => cons (f a b) (zipWith f as bs)

-- ─────────────────────────────────────────────────────────────────
-- take y drop
-- ─────────────────────────────────────────────────────────────────

/-- Primeros `k` elementos de la lista (o toda si `k ≥ length l`). -/
def take : ℕ₀ → PList α → PList α
  | 𝟘,    _          => nil
  | σ _,  nil        => nil
  | σ k,  cons h t   => cons h (take k t)

/-- Descarta los primeros `k` elementos.
    Si `k ≥ length l` devuelve `nil`; si `k = 𝟘` devuelve `l`. -/
def drop : ℕ₀ → PList α → PList α
  | 𝟘,    l          => l
  | σ _,  nil        => nil
  | σ k,  cons _ t   => drop k t

-- ─────────────────────────────────────────────────────────────────
-- Membresía (Bool y Prop)
-- ─────────────────────────────────────────────────────────────────

def mem [DecidableEq α] (x : α) : PList α → Bool
  | nil      => false
  | cons h t => if x = h then true else mem x t

inductive Mem (a : α) : PList α → Prop where
  | head : Mem a (cons a t)
  | tail : Mem a t → Mem a (cons b t)

instance : Membership α (PList α) := ⟨fun l a => Mem a l⟩

-- ─────────────────────────────────────────────────────────────────
-- Puentes con List (para la transición de Fase 2)
-- ─────────────────────────────────────────────────────────────────

def toList : PList α → List α
  | nil      => []
  | cons h t => h :: toList t

def ofList : List α → PList α
  | []      => nil
  | h :: t  => cons h (ofList t)

end PList
