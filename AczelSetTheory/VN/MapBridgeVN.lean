/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/MapBridgeVN.lean
-- Bridge: MapOn A B (función Peano entre FSet ℕ₀) → HFSet como grafo.
--
-- mapBridge f := { ⟪vN n, vN (f n)⟫ | n ∈ A }
--
-- Público:
--   mapBridge              : MapOn A B → HFSet
--   mem_mapBridge          : x ∈ mapBridge f ↔ ∃ n ∈ A, x = ⟪vN n, vN (f n)⟫
--   mem_mapBridge_pair     : ⟪vN n, vN m⟫ ∈ mapBridge f ↔ n ∈ A ∧ f n = m
--   mapBridge_isFunction   : isFunction (mapBridge f)
--   mapBridge_domain       : n ∈ A ↔ ∃ m, ⟪vN n, m⟫ ∈ mapBridge f

import AczelSetTheory.VN.FSet
import AczelSetTheory.Axioms.LinearOrder
import AczelSetTheory.Axioms.OrderedPair
import AczelSetTheory.Axioms.Function
import Peano.PeanoNat.ListsAndSets.FSetFunction

open Peano Peano.FSet Peano.FSetFunction VN

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- Auxiliar: foldl con insert sobre pares ordenados
-- ─────────────────────────────────────────────────────────────────

private theorem mem_foldl_insert_pair (g : ℕ₀ → ℕ₀) (x : HFSet)
    (l : List ℕ₀) (acc : HFSet) :
    x ∈ l.foldl (fun a n => HFSet.insert ⟪vN n, vN (g n)⟫ a) acc ↔
    x ∈ acc ∨ ∃ n ∈ l, x = ⟪vN n, vN (g n)⟫ := by
  induction l generalizing acc with
  | nil => simp
  | cons h t ih =>
    rw [List.foldl_cons, ih]
    rw [mem_insert]
    constructor
    · rintro ((hhead | hacc) | ⟨n, hn, hx⟩)
      · exact Or.inr ⟨h, List.mem_cons_self h t, hhead.symm⟩
      · exact Or.inl hacc
      · exact Or.inr ⟨n, List.mem_cons_of_mem h hn, hx⟩
    · rintro (hacc | ⟨n, hn, hx⟩)
      · exact Or.inl (Or.inr hacc)
      · rcases List.mem_cons.mp hn with rfl | hn'
        · exact Or.inl (Or.inl hx.symm)
        · exact Or.inr ⟨n, hn', hx⟩

-- ─────────────────────────────────────────────────────────────────
-- Definición
-- ─────────────────────────────────────────────────────────────────

/-- Encoda una función Peano `f : MapOn A B` como grafo en HFSet:
    `mapBridge f = { ⟪vN n, vN (f n)⟫ | n ∈ A }`. -/
def mapBridge {A B : FSet ℕ₀} (f : MapOn A B) : HFSet :=
  A.elems.foldl (fun acc n => HFSet.insert ⟪vN n, vN (f.toFun n)⟫ acc) ∅

-- ─────────────────────────────────────────────────────────────────
-- Pertenencia
-- ─────────────────────────────────────────────────────────────────

theorem mem_mapBridge {A B : FSet ℕ₀} (f : MapOn A B) (x : HFSet) :
    x ∈ mapBridge f ↔ ∃ n ∈ A.elems, x = ⟪vN n, vN (f.toFun n)⟫ := by
  simp only [mapBridge, mem_foldl_insert_pair, not_mem_empty, false_or]

theorem mem_mapBridge_pair {A B : FSet ℕ₀} (f : MapOn A B) (n m : ℕ₀) :
    ⟪vN n, vN m⟫ ∈ mapBridge f ↔ n ∈ A.elems ∧ f.toFun n = m := by
  rw [mem_mapBridge]
  constructor
  · rintro ⟨k, hk, heq⟩
    rw [orderedPair_eq_iff] at heq
    exact ⟨(vN_injective heq.1) ▸ hk, vN_injective heq.2.symm⟩
  · rintro ⟨hn, rfl⟩
    exact ⟨n, hn, rfl⟩

-- ─────────────────────────────────────────────────────────────────
-- Estructura de función en HFSet
-- ─────────────────────────────────────────────────────────────────

theorem mapBridge_isFunction {A B : FSet ℕ₀} (f : MapOn A B) :
    isFunction (mapBridge f) := by
  constructor
  · intro x hx
    rw [mem_mapBridge] at hx
    obtain ⟨n, _, rfl⟩ := hx
    exact ⟨vN n, vN (f.toFun n), rfl⟩
  · intro a b₁ b₂ h₁ h₂
    rw [mem_mapBridge] at h₁ h₂
    obtain ⟨n₁, _, heq₁⟩ := h₁
    obtain ⟨n₂, _, heq₂⟩ := h₂
    rw [orderedPair_eq_iff] at heq₁ heq₂
    have hn : n₁ = n₂ := vN_injective (heq₁.1.symm.trans heq₂.1)
    rw [heq₁.2, heq₂.2, hn]

-- ─────────────────────────────────────────────────────────────────
-- Dominio
-- ─────────────────────────────────────────────────────────────────

theorem mapBridge_domain {A B : FSet ℕ₀} (f : MapOn A B) (n : ℕ₀) :
    n ∈ A.elems ↔ ∃ m : HFSet, ⟪vN n, m⟫ ∈ mapBridge f := by
  constructor
  · intro hn
    exact ⟨vN (f.toFun n), (mem_mapBridge_pair f n (f.toFun n)).mpr ⟨hn, rfl⟩⟩
  · rintro ⟨m, hm⟩
    rw [mem_mapBridge] at hm
    obtain ⟨k, hk, heq⟩ := hm
    rw [orderedPair_eq_iff] at heq
    exact (vN_injective heq.1) ▸ hk

end HFSet
