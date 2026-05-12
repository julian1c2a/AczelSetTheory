/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/CList/Basic.lean
-- CList: pre-conjuntos hereditariamente finitos.
-- Fase 2: constructor mk : PList CList → CList; cSize : CList → ℕ₀.

import AczelSetTheory.PList

open Peano

/-- Pre-conjunto hereditariamente finito: árbol enraizado con hijos en PList. -/
inductive CList : Type where
  | mk : PList CList → CList
  deriving Repr, Inhabited

namespace CList

-- ─────────────────────────────────────────────────────────────────
-- Tamaño en ℕ₀
-- ─────────────────────────────────────────────────────────────────

mutual
  def cSize : CList → ℕ₀
    | mk xs => σ (cSizePList xs)
  def cSizePList : PList CList → ℕ₀
    | .nil      => 𝟘
    | .cons x t => σ (add (cSize x) (cSizePList t))
end

-- Ecuaciones @[simp] para controlar el desplegado en pruebas.
@[simp] theorem cSize_mk (xs : PList CList) :
    cSize (mk xs) = σ (cSizePList xs) := rfl

@[simp] theorem cSizePList_nil :
    cSizePList (.nil : PList CList) = 𝟘 := rfl

@[simp] theorem cSizePList_cons (x : CList) (t : PList CList) :
    cSizePList (.cons x t) = σ (add (cSize x) (cSizePList t)) := rfl

theorem cSize_lt_of_mem {x : CList} {xs : PList CList}
    (h : x ∈ xs) : cSize x < cSize (mk xs) := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [cSize_mk, cSizePList_cons]
    cases h with
    | head => omega₀
    | tail hys =>
        have hlt := ih hys
        simp only [cSize_mk] at hlt
        omega₀

/-- El conjunto vacío computacional -/
def empty : CList := mk .nil

-- ─────────────────────────────────────────────────────────────────
-- Motor de comparación (membresía, subconjunto, igualdad extensional)
-- ─────────────────────────────────────────────────────────────────

inductive CListOp
| mem
| subset
| eq

@[simp]
def opWeight : CListOp → Nat
| .mem    => 0
| .subset => 1
| .eq     => 2

set_option linter.unusedSimpArgs false in
/-- Motor lógico para igualdad extensional.
    Terminación por medida ponderada sobre sizeOf. -/
def evalOp (op : CListOp) (A B : CList) : Bool :=
  match op, A, B with
  | .mem, _, mk .nil            => false
  | .mem, x, mk (.cons y ys)   =>
      evalOp .eq x y || evalOp .mem x (mk ys)

  | .subset, mk .nil, _             => true
  | .subset, mk (.cons x xs), B    =>
      evalOp .mem x B && evalOp .subset (mk xs) B

  | .eq, A, B =>
      evalOp .subset A B && evalOp .subset B A
termination_by ((((sizeOf A + sizeOf B : Nat) * 3) + opWeight op) : Nat)
decreasing_by
  all_goals simp_wf
  all_goals try simp [opWeight, sizeOf]
  all_goals try simp_arith
  all_goals try omega

def mem    (x A : CList) : Bool := evalOp .mem x A
def subset (A B : CList) : Bool := evalOp .subset A B
def extEq  (A B : CList) : Bool := evalOp .eq A B

instance : BEq CList where beq := extEq

-- ─────────────────────────────────────────────────────────────────
-- Orden total (para canonización)
-- ─────────────────────────────────────────────────────────────────

def lt (A B : CList) : Bool :=
  match A, B with
  | mk .nil,         mk .nil          => false
  | mk .nil,         mk (.cons _ _)   => true
  | mk (.cons _ _),  mk .nil          => false
  | mk (.cons x xs), mk (.cons y ys)  =>
      if lt x y then true
      else if lt y x then false
      else lt (mk xs) (mk ys)
termination_by (sizeOf A + sizeOf B : Nat)
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

-- ─────────────────────────────────────────────────────────────────
-- Deduplicación
-- ─────────────────────────────────────────────────────────────────

def dedupAux (l vistos : PList CList) : PList CList :=
  match l with
  | .nil      => .nil
  | .cons x t =>
      if PList.any (fun y => extEq x y) vistos then
        dedupAux t vistos
      else
        .cons x (dedupAux t (.cons x vistos))

def dedup (l : PList CList) : PList CList := dedupAux l .nil

-- ─────────────────────────────────────────────────────────────────
-- Insertion sort sobre PList CList
-- ─────────────────────────────────────────────────────────────────

def orderedInsert (x : CList) : PList CList → PList CList
  | .nil      => .cons x .nil
  | .cons y ys =>
      if lt x y then .cons x (.cons y ys)
      else if extEq x y then .cons y ys
      else .cons y (orderedInsert x ys)

def insertionSort : PList CList → PList CList
  | .nil      => .nil
  | .cons x t => orderedInsert x (insertionSort t)

-- ─────────────────────────────────────────────────────────────────
-- Normalización canónica (mutual estructural)
-- ─────────────────────────────────────────────────────────────────

mutual
  def normalize : CList → CList
    | mk xs => mk (insertionSort (dedup (normalizePList xs)))
  def normalizePList : PList CList → PList CList
    | .nil      => .nil
    | .cons x t => .cons (normalize x) (normalizePList t)
end

-- ─────────────────────────────────────────────────────────────────
-- Constantes de prueba (von Neumann 0–9)
-- ─────────────────────────────────────────────────────────────────

def zero  := empty
def one   := mk (.cons zero .nil)
def two   := mk (.cons zero (.cons one .nil))
def three := mk (.cons zero (.cons one (.cons two .nil)))
def four  := mk (.cons zero (.cons one (.cons two (.cons three .nil))))
def five  := mk (.cons zero (.cons one (.cons two (.cons three (.cons four .nil)))))
def six   := mk (.cons zero (.cons one (.cons two (.cons three (.cons four (.cons five .nil))))))
def seven := mk (.cons zero (.cons one (.cons two (.cons three (.cons four (.cons five (.cons six .nil)))))))
def eight := mk (.cons zero (.cons one (.cons two (.cons three (.cons four (.cons five (.cons six (.cons seven .nil))))))))
def nine  := mk (.cons zero (.cons one (.cons two (.cons three (.cons four (.cons five (.cons six (.cons seven (.cons eight .nil)))))))))
def dirty := mk (PList.ofList [one, two, zero, three, one, zero, zero, two, three, two])

end CList
