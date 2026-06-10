/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/HFMatrix.lean
-- Matrices n×n sobre HFRing como HFSet (portador nPow rng.R (n²)).
--
-- Representación fila-mayor: entrada (i,j) = componente n*i+j.
-- Portador: nPow rng.R (n²) — computable, definido en Axioms/OrdinalNat.
-- 0 sorry, 0 noncomputable def.
--
-- Públicos:
--   finSumRing rng n f        : suma de n términos en rng
--   matrixCarrier n rng       : HFSet = nPow rng.R (n²)
--   matAdd / matNeg / matZero / matOne / matMul
--   HFMatrixRing n rng        : HFRing — anillo de matrices n×n
--
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.HFList
import AczelSetTheory.Algebra.Ring
import AczelSetTheory.Axioms.NPow
import AczelSetTheory.Axioms.OrdinalNat
import AczelSetTheory.Axioms.Function
import AczelSetTheory.Axioms.CartProd
import Peano.PeanoNat.Div

namespace HFAlgebra

open Peano Peano.Add Peano.Mul Peano.Div Peano.Sub
open Peano.StrictOrder Peano.Order Peano.Axioms
open HFSet

-- ══════════════════════════════════════════════════════════════════
-- §1. Suma finita en un HFRing
-- ══════════════════════════════════════════════════════════════════

/-- Suma `f 0 + f 1 + ... + f (n-1)` en el anillo `rng`. -/
def finSumRing (rng : HFRing) : ℕ₀ → (ℕ₀ → HFSet) → HFSet
  | .zero,   _ => rng.zero
  | .succ k, f => rng.add (finSumRing rng k f) (f k)

@[simp] theorem finSumRing_zero (rng : HFRing) (f : ℕ₀ → HFSet) :
    finSumRing rng 𝟘 f = rng.zero := rfl

@[simp] theorem finSumRing_succ (rng : HFRing) (k : ℕ₀) (f : ℕ₀ → HFSet) :
    finSumRing rng (σ k) f = rng.add (finSumRing rng k f) (f k) := rfl

theorem finSumRing_congr {rng : HFRing} {n : ℕ₀} {f g : ℕ₀ → HFSet}
    (h : ∀ i, i < n → f i = g i) : finSumRing rng n f = finSumRing rng n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumRing_succ]
    rw [ih (fun i hi => h i (lt_trans _ _ _ hi (lt_succ_self k))),
        h k (lt_succ_self k)]

theorem finSumRing_mem {rng : HFRing} {n : ℕ₀} {f : ℕ₀ → HFSet}
    (hf : ∀ i, i < n → f i ∈ rng.R) : finSumRing rng n f ∈ rng.R := by
  induction n with
  | zero => exact rng.zero_mem
  | succ k ih =>
    exact rng.add_closed
      (ih (fun i hi => hf i (lt_trans _ _ _ hi (lt_succ_self k))))
      (hf k (lt_succ_self k))

-- ══════════════════════════════════════════════════════════════════
-- §2. finSumRing avanzado
-- ══════════════════════════════════════════════════════════════════

private theorem finSumRing_zero_fn {rng : HFRing} {n : ℕ₀} :
    finSumRing rng n (fun _ => rng.zero) = rng.zero := by
  induction n with
  | zero => rfl
  | succ k ih => simp [finSumRing_succ, ih, rng.add_zero rng.zero_mem]

private theorem finSumRing_add {rng : HFRing} {n : ℕ₀} {f g : ℕ₀ → HFSet}
    (hf : ∀ i, i < n → f i ∈ rng.R) (hg : ∀ i, i < n → g i ∈ rng.R) :
    finSumRing rng n (fun i => rng.add (f i) (g i)) =
    rng.add (finSumRing rng n f) (finSumRing rng n g) := by
  induction n with
  | zero =>
    simp only [finSumRing_zero]
    exact (rng.zero_add rng.zero_mem).symm
  | succ k ih =>
    have hf' := fun i hi => hf i (lt_trans _ _ _ hi (lt_succ_self k))
    have hg' := fun i hi => hg i (lt_trans _ _ _ hi (lt_succ_self k))
    simp only [finSumRing_succ, ih hf' hg']
    have hSf := finSumRing_mem hf'
    have hSg := finSumRing_mem hg'
    have hfk := hf k (lt_succ_self k)
    have hgk := hg k (lt_succ_self k)
    -- Goal: (Sf + Sg) + (fk + gk) = (Sf + fk) + (Sg + gk)
    rw [rng.add_assoc hSf hSg (rng.add_closed hfk hgk)]
    rw [← rng.add_assoc hSg hfk hgk]
    rw [rng.add_comm hSg hfk]
    rw [rng.add_assoc hfk hSg hgk]
    rw [← rng.add_assoc hSf hfk (rng.add_closed hSg hgk)]

theorem mul_finSumRing {rng : HFRing} {n : ℕ₀} {a : HFSet} {f : ℕ₀ → HFSet}
    (ha : a ∈ rng.R) (hf : ∀ i, i < n → f i ∈ rng.R) :
    rng.mul a (finSumRing rng n f) = finSumRing rng n (fun i => rng.mul a (f i)) := by
  induction n with
  | zero => simp [rng.mul_zero ha]
  | succ k ih =>
    have hf' := fun i hi => hf i (lt_trans _ _ _ hi (lt_succ_self k))
    simp only [finSumRing_succ]
    rw [rng.left_distrib ha (finSumRing_mem hf') (hf k (lt_succ_self k)), ih hf']

theorem finSumRing_mul {rng : HFRing} {n : ℕ₀} {a : HFSet} {f : ℕ₀ → HFSet}
    (ha : a ∈ rng.R) (hf : ∀ i, i < n → f i ∈ rng.R) :
    rng.mul (finSumRing rng n f) a = finSumRing rng n (fun i => rng.mul (f i) a) := by
  induction n with
  | zero => simp [rng.zero_mul ha]
  | succ k ih =>
    have hf' := fun i hi => hf i (lt_trans _ _ _ hi (lt_succ_self k))
    simp only [finSumRing_succ]
    rw [rng.right_distrib (finSumRing_mem hf') (hf k (lt_succ_self k)) ha, ih hf']

private theorem finSumRing_swap {rng : HFRing} {m n : ℕ₀} {f : ℕ₀ → ℕ₀ → HFSet}
    (hf : ∀ i j, i < m → j < n → f i j ∈ rng.R) :
    finSumRing rng m (fun i => finSumRing rng n (fun j => f i j)) =
    finSumRing rng n (fun j => finSumRing rng m (fun i => f i j)) := by
  induction n with
  | zero => simp [finSumRing_zero_fn]
  | succ l ih =>
    have hfl : ∀ i j, i < m → j < l → f i j ∈ rng.R :=
      fun i j hi hj => hf i j hi (lt_trans _ _ _ hj (lt_succ_self l))
    simp only [finSumRing_succ]
    rw [finSumRing_add
        (fun i hi => finSumRing_mem (fun j hj => hfl i j hi hj))
        (fun i hi => hf i l hi (lt_succ_self l)),
        ih hfl]

-- sum-if: Σ_k (if k=j then v else 0) = v  when j < n
private theorem finSumRing_if_eq {rng : HFRing} {n j : ℕ₀}
    (hj : j < n) {v : HFSet} (hv : v ∈ rng.R) :
    finSumRing rng n (fun k => if k = j then v else rng.zero) = v := by
  induction n with
  | zero => exact absurd hj (nlt_n_0 j)
  | succ m ih =>
    simp only [finSumRing_succ]
    rcases (lt_succ_iff_lt_or_eq j m).mp hj with hjm | rfl
    · rw [if_neg (ne_of_lt j m hjm).symm,
          rng.add_zero (finSumRing_mem (fun k hk => by
            by_cases h : k = j
            · rw [if_pos h]; exact hv
            · rw [if_neg h]; exact rng.zero_mem))]
      exact ih hjm
    · have hsum : finSumRing rng j (fun k => if k = j then v else rng.zero) = rng.zero :=
        (finSumRing_congr (fun k hk => if_neg (ne_of_lt k j hk))).trans finSumRing_zero_fn
      rw [if_pos rfl, hsum, rng.zero_add hv]

-- Kronecker: Σ_k f(k) * (if k=j then 1 else 0) = f(j)
private theorem finSumRing_Kronecker {rng : HFRing} {n j : ℕ₀}
    (hj : j < n) {f : ℕ₀ → HFSet} (hf : ∀ k, k < n → f k ∈ rng.R) :
    finSumRing rng n (fun k => rng.mul (f k) (if k = j then rng.one else rng.zero)) = f j := by
  have step : finSumRing rng n (fun k => rng.mul (f k) (if k = j then rng.one else rng.zero)) =
              finSumRing rng n (fun k => if k = j then f j else rng.zero) :=
    finSumRing_congr (fun k hk => by
      by_cases h : k = j
      · rw [if_pos h, rng.mul_one (hf k hk), if_pos h, h]
      · rw [if_neg h, rng.mul_zero (hf k hk), if_neg h])
  rw [step]; exact finSumRing_if_eq hj (hf j hj)

-- Left Kronecker: Σ_k (if j=k then 1 else 0) * f(k) = f(j)
private theorem finSumRing_Kronecker_left {rng : HFRing} {n j : ℕ₀}
    (hj : j < n) {f : ℕ₀ → HFSet} (hf : ∀ k, k < n → f k ∈ rng.R) :
    finSumRing rng n (fun k => rng.mul (if j = k then rng.one else rng.zero) (f k)) = f j := by
  have step : finSumRing rng n (fun k => rng.mul (if j = k then rng.one else rng.zero) (f k)) =
              finSumRing rng n (fun k => if k = j then f j else rng.zero) :=
    finSumRing_congr (fun k hk => by
      by_cases h : k = j
      · rw [if_pos h, if_pos h.symm, rng.one_mul (hf k hk), h]
      · rw [if_neg h, if_neg (Ne.symm h), rng.zero_mul (hf k hk)])
  rw [step]; exact finSumRing_if_eq hj (hf j hj)

-- ══════════════════════════════════════════════════════════════════
-- §3. Aritmética de índices matriciales
-- ══════════════════════════════════════════════════════════════════

private theorem Ψ_pos {n : ℕ₀} (hn : n ≠ (𝟘 : ℕ₀)) : 0 < Ψ n := by
  have h : Ψ n ≠ 0 := fun heq =>
    hn ((PList.Omega0.ψ_eq_iff n (𝟘 : ℕ₀)).mpr (heq.trans PList.Omega0.ψ_zero.symm))
  omega

private theorem n_ne_zero_of_lt_mul {n k : ℕ₀} (hk : k < mul n n) : n ≠ (𝟘 : ℕ₀) := by
  intro rfl; simp [zero_mul] at hk; exact absurd hk (nlt_n_0 k)

private theorem div_of_add_mul {j i n : ℕ₀} (hn : n ≠ (𝟘 : ℕ₀)) (hj : j < n) :
    div (add (mul n i) j) n = i := by
  apply (PList.Omega0.ψ_eq_iff _ _).mpr
  rw [isomorph_Ψ_div, isomorph_Ψ_add, isomorph_Ψ_mul]
  simp only [Nat.add_eq, Nat.mul_eq]
  have hpos : 0 < Ψ n := Ψ_pos hn
  have hjn : Ψ j < Ψ n := (PList.Omega0.ψ_lt_iff j n).mp hj
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm]; exact Nat.le_add_right _ _
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (Ψ i) (Ψ n)]; omega

private theorem mod_of_add_mul {j i n : ℕ₀} (hn : n ≠ (𝟘 : ℕ₀)) (hj : j < n) :
    mod (add (mul n i) j) n = j := by
  have hdiv : div (add (mul n i) j) n = i := div_of_add_mul hn hj
  have hspec := divMod_spec (add (mul n i) j) n hn
  simp only [show (divMod (add (mul n i) j) n).1 = div (add (mul n i) j) n from rfl,
             show (divMod (add (mul n i) j) n).2 = mod (add (mul n i) j) n from rfl] at hspec
  rw [hdiv, mul_comm i n] at hspec
  exact (add_cancel (mul n i) j (mod (add (mul n i) j) n) hspec).symm

private theorem lt_mul_of_lt_lt {i t n : ℕ₀} (hi : i < n) (ht : t < n) :
    add (mul n i) t < mul n n := by
  simp only [PList.Omega0.ψ_lt_iff, isomorph_Ψ_add, isomorph_Ψ_mul]
  have h1 : Ψ i < Ψ n := (PList.Omega0.ψ_lt_iff i n).mp hi
  have h2 : Ψ t < Ψ n := (PList.Omega0.ψ_lt_iff t n).mp ht
  have h3 : Nat.add (Nat.mul (Ψ n) (Ψ i)) (Ψ t) < Nat.add (Nat.mul (Ψ n) (Ψ i)) (Ψ n) :=
    Nat.add_lt_add_left h2 (Nat.mul (Ψ n) (Ψ i))
  have h4 : Nat.mul (Ψ n) (Nat.succ (Ψ i)) ≤ Nat.mul (Ψ n) (Ψ n) :=
    Nat.mul_le_mul_left _ (by omega)
  have h5 : Nat.mul (Ψ n) (Nat.succ (Ψ i)) = Nat.add (Nat.mul (Ψ n) (Ψ i)) (Ψ n) := rfl
  omega

private theorem lt_mul_of_mul_lt {i t n : ℕ₀} (hi : i < n) (ht : t < n) :
    add (mul i n) t < mul n n := by
  rw [mul_comm i n]; exact lt_mul_of_lt_lt hi ht

private theorem div_of_mul_add {j i n : ℕ₀} (hn : n ≠ (𝟘 : ℕ₀)) (hj : j < n) :
    div (add (mul i n) j) n = i := by
  rw [mul_comm i n]; exact div_of_add_mul hn hj

private theorem mod_of_mul_add {j i n : ℕ₀} (hn : n ≠ (𝟘 : ℕ₀)) (hj : j < n) :
    mod (add (mul i n) j) n = j := by
  rw [mul_comm i n]; exact mod_of_add_mul hn hj

private theorem lt_mul_decompose {n k : ℕ₀} (hk : k < mul n n) :
    div k n < n ∧ mod k n < n ∧ add (mul n (div k n)) (mod k n) = k := by
  have hn := n_ne_zero_of_lt_mul hk
  refine ⟨?_, mod_lt k n hn, ?_⟩
  · apply (PList.Omega0.ψ_lt_iff (div k n) n).mpr
    rw [isomorph_Ψ_div]
    show Ψ k / Ψ n < Ψ n
    rw [Nat.div_lt_iff_lt_mul (Ψ_pos hn)]
    have := (PList.Omega0.ψ_lt_iff k (mul n n)).mp hk
    simpa [isomorph_Ψ_mul] using this
  · have h := divMod_spec k n hn
    simp only [show (divMod k n).1 = div k n from rfl,
               show (divMod k n).2 = mod k n from rfl] at h
    rw [mul_comm (div k n) n] at h
    exact h.symm

-- ══════════════════════════════════════════════════════════════════
-- §4. Puente FinList ↔ nPow
-- ══════════════════════════════════════════════════════════════════

private def nthEntry : ℕ₀ → HFSet → HFSet
  | .zero,   t => snd t
  | .succ j, t => nthEntry j (fst t)

private def buildNPow : {k : ℕ₀} → FinList k → HFSet
  | .zero,   _ => empty
  | .succ _, l => ⟪buildNPow l.tail, l.head⟫

private def deconNPow : (k : ℕ₀) → HFSet → FinList k
  | .zero,   _ => FinList.empty
  | .succ m, t => FinList.cons (snd t) (deconNPow m (fst t))

private def constList : (k : ℕ₀) → HFSet → FinList k
  | .zero,   _ => FinList.empty
  | .succ m, v => FinList.cons v (constList m v)

private def buildEntries : (k start : ℕ₀) → (f : ℕ₀ → HFSet) → FinList k
  | .zero,   _,     _ => FinList.empty
  | .succ m, start, f => FinList.cons (f start) (buildEntries m (σ start) f)

@[simp] private theorem nthEntry_pair_zero (a b : HFSet) :
    nthEntry 𝟘 ⟪a, b⟫ = b := by simp [nthEntry, snd_orderedPair_eq']

@[simp] private theorem nthEntry_pair_succ (k : ℕ₀) (a b : HFSet) :
    nthEntry (σ k) ⟪a, b⟫ = nthEntry k a := by simp [nthEntry, fst_orderedPair_eq']

private theorem nthEntry_buildNPow {k : ℕ₀} (l : FinList k) (i : Fin₀ k) :
    nthEntry i.val (buildNPow l) = l.get i := by
  induction k with
  | zero => exact (Fin₀.elim_zero i).elim
  | succ m ih =>
    cases i with | mk j hj =>
    cases j with
    | zero =>
      simp [buildNPow, nthEntry_pair_zero, FinList.get_zero_eq_head]
    | succ j' =>
      simp [buildNPow, nthEntry_pair_succ]
      rw [← FinList.get_tail_succ l j' (by
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hj
        simp only [PList.Omega0.ψ_lt_iff]; omega)]
      exact ih l.tail ⟨j', by
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hj
        simp only [PList.Omega0.ψ_lt_iff]; omega⟩

private theorem buildNPow_decon {k : ℕ₀} {R : HFSet} {t : HFSet}
    (ht : t ∈ nPow R k) : buildNPow (deconNPow k t) = t := by
  induction k generalizing t with
  | zero => rw [(mem_nPow_zero t R).mp ht]; rfl
  | succ m ih =>
    obtain ⟨s, hs, _, _, heq⟩ := (mem_nPow_succ t R m).mp ht
    rw [heq]; simp [deconNPow, snd_orderedPair_eq', fst_orderedPair_eq', buildNPow]
    rw [ih hs]

private theorem mem_buildNPow {k : ℕ₀} {R : HFSet} {l : FinList k}
    (hl : ∀ i : Fin₀ k, l.get i ∈ R) : buildNPow l ∈ nPow R k := by
  induction k with
  | zero => exact (mem_nPow_zero _ R).mpr rfl
  | succ m ih =>
    rw [mem_nPow_succ]
    refine ⟨buildNPow l.tail, ih (fun i => ?_), l.head,
            FinList.get_zero_eq_head l (lt_zero_succ m) ▸ hl ⟨𝟘, lt_zero_succ m⟩,
            by simp [buildNPow]⟩
    exact FinList.get_tail_succ l i.val i.isLt ▸ hl ⟨σ i.val, by
      have hi := i.isLt
      simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hi ⊢; omega⟩

private theorem nPow_ext {k : ℕ₀} {R M N : HFSet}
    (hM : M ∈ nPow R k) (hN : N ∈ nPow R k)
    (h : ∀ j, j < k → nthEntry j M = nthEntry j N) : M = N := by
  rw [← buildNPow_decon hM, ← buildNPow_decon hN]
  apply congrArg buildNPow; apply FinList.extEq; intro i
  rw [← nthEntry_buildNPow _ i, ← nthEntry_buildNPow _ i,
      buildNPow_decon hM, buildNPow_decon hN]
  exact h i.val i.isLt

private theorem nthEntry_mem {k : ℕ₀} {R : HFSet} {t : HFSet} (ht : t ∈ nPow R k) :
    ∀ j, j < k → nthEntry j t ∈ R := by
  induction k generalizing t with
  | zero => intro j hj; exact absurd hj (nlt_n_0 j)
  | succ m ih =>
    intro j hj
    obtain ⟨s, hs, v, hv, heq⟩ := (mem_nPow_succ t R m).mp ht
    cases j with
    | zero => rw [heq, nthEntry_pair_zero]; exact hv
    | succ j' =>
      rw [heq, nthEntry_pair_succ]
      exact ih hs j' (by
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hj
        simp only [PList.Omega0.ψ_lt_iff]; omega)

-- ══════════════════════════════════════════════════════════════════
-- §5. Portador y operaciones matriciales
-- ══════════════════════════════════════════════════════════════════

def matrixCarrier (n : ℕ₀) (rng : HFRing) : HFSet := nPow rng.R (mul n n)

def matAdd (n : ℕ₀) (rng : HFRing) (M N : HFSet) : HFSet :=
  buildNPow (FinList.zipWith rng.add (deconNPow (mul n n) M) (deconNPow (mul n n) N))

def matNeg (n : ℕ₀) (rng : HFRing) (M : HFSet) : HFSet :=
  buildNPow (FinList.map rng.neg (deconNPow (mul n n) M))

def matZero (n : ℕ₀) (rng : HFRing) : HFSet :=
  buildNPow (constList (mul n n) rng.zero)

def matOne (n : ℕ₀) (rng : HFRing) : HFSet :=
  buildNPow (buildEntries (mul n n) 𝟘
    (fun k => if div k n = mod k n then rng.one else rng.zero))

def matMul (n : ℕ₀) (rng : HFRing) (M N : HFSet) : HFSet :=
  buildNPow (buildEntries (mul n n) 𝟘 (fun k =>
    finSumRing rng n (fun t =>
      rng.mul (nthEntry (add (mul (div k n) n) t) M)
              (nthEntry (add (mul t n) (mod k n)) N))))

-- ══════════════════════════════════════════════════════════════════
-- §6. FinList helper lemmas (get)
-- ══════════════════════════════════════════════════════════════════

private theorem zipWith_get {n : ℕ₀} (f : HFSet → HFSet → HFSet)
    (l₁ l₂ : FinList n) (i : Fin₀ n) :
    (FinList.zipWith f l₁ l₂).get i = f (l₁.get i) (l₂.get i) := by
  induction n with
  | zero => exact (Fin₀.elim_zero i).elim
  | succ m ih =>
    rw [← FinList.cons_head_tail l₁, ← FinList.cons_head_tail l₂,
        FinList.zipWith_cons]
    cases i with | mk j hj =>
    cases j with
    | zero => rfl
    | succ j' =>
      exact ih l₁.tail l₂.tail ⟨j', by
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hj
        simp only [PList.Omega0.ψ_lt_iff]; omega⟩

private theorem map_get {n : ℕ₀} (f : HFSet → HFSet) (l : FinList n) (i : Fin₀ n) :
    (FinList.map f l).get i = f (l.get i) := by
  induction n with
  | zero => exact (Fin₀.elim_zero i).elim
  | succ m ih =>
    rw [← FinList.cons_head_tail l,
        show FinList.map f (FinList.cons l.head l.tail) =
             FinList.cons (f l.head) (FinList.map f l.tail) from
          FinList.ext rfl]
    cases i with | mk j hj =>
    cases j with
    | zero => rfl
    | succ j' =>
      exact ih l.tail ⟨j', by
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hj
        simp only [PList.Omega0.ψ_lt_iff]; omega⟩

private theorem constList_get {n : ℕ₀} (v : HFSet) (i : Fin₀ n) :
    (constList n v).get i = v := by
  induction n with
  | zero => exact (Fin₀.elim_zero i).elim
  | succ m ih =>
    cases i with | mk j hj =>
    cases j with
    | zero => simp [constList, FinList.get_cons_zero]
    | succ j' =>
      simp [constList, FinList.get_cons_succ]
      exact ih ⟨j', by
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hj
        simp only [PList.Omega0.ψ_lt_iff]; omega⟩

private theorem deconNPow_get (k : ℕ₀) (t : HFSet) (i : Fin₀ k) :
    (deconNPow k t).get i = nthEntry i.val t := by
  revert i
  induction k generalizing t with
  | zero => intro i; exact (Fin₀.elim_zero i).elim
  | succ m ih =>
    intro ⟨j, hj⟩
    cases j with
    | zero => simp [deconNPow, FinList.get_cons_zero, nthEntry]
    | succ j' =>
      simp only [deconNPow, FinList.get_cons_succ, nthEntry]
      exact ih (fst t) ⟨j', by
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hj
        simp only [PList.Omega0.ψ_lt_iff]; omega⟩

private theorem buildEntries_get {n start : ℕ₀} {f : ℕ₀ → HFSet} (i : Fin₀ n) :
    (buildEntries n start f).get i = f (add start i.val) := by
  revert i
  induction n generalizing start with
  | zero => intro i; exact (Fin₀.elim_zero i).elim
  | succ m ih =>
    intro ⟨j, hj⟩
    cases j with
    | zero => simp [buildEntries, FinList.get_cons_zero, add_zero]
    | succ j' =>
      simp only [buildEntries, FinList.get_cons_succ]
      rw [ih (start := σ start) ⟨j', by
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hj
        simp only [PList.Omega0.ψ_lt_iff]; omega⟩]
      simp [add_succ, succ_add]

-- ══════════════════════════════════════════════════════════════════
-- §7. nthEntry de las operaciones
-- ══════════════════════════════════════════════════════════════════

private theorem nthEntry_matAdd {n : ℕ₀} (rng : HFRing) (M N : HFSet)
    {j : ℕ₀} (hj : j < mul n n) :
    nthEntry j (matAdd n rng M N) = rng.add (nthEntry j M) (nthEntry j N) := by
  simp only [matAdd]
  rw [nthEntry_buildNPow _ ⟨j, hj⟩, zipWith_get, deconNPow_get, deconNPow_get]

private theorem nthEntry_matNeg {n : ℕ₀} (rng : HFRing) (M : HFSet)
    {j : ℕ₀} (hj : j < mul n n) :
    nthEntry j (matNeg n rng M) = rng.neg (nthEntry j M) := by
  simp only [matNeg]
  rw [nthEntry_buildNPow _ ⟨j, hj⟩, map_get, deconNPow_get]

private theorem nthEntry_matZero {n : ℕ₀} (rng : HFRing)
    {j : ℕ₀} (hj : j < mul n n) :
    nthEntry j (matZero n rng) = rng.zero := by
  simp only [matZero]; rw [nthEntry_buildNPow _ ⟨j, hj⟩, constList_get]

private theorem nthEntry_matOne {n : ℕ₀} (rng : HFRing)
    {k : ℕ₀} (hk : k < mul n n) :
    nthEntry k (matOne n rng) = if div k n = mod k n then rng.one else rng.zero := by
  simp only [matOne]
  rw [nthEntry_buildNPow _ ⟨k, hk⟩, buildEntries_get]; simp [zero_add]

private theorem nthEntry_matMul {n : ℕ₀} (rng : HFRing) (M N : HFSet)
    {i j : ℕ₀} (hi : i < n) (hj : j < n) :
    nthEntry (add (mul n i) j) (matMul n rng M N) =
    finSumRing rng n (fun t =>
      rng.mul (nthEntry (add (mul i n) t) M)
              (nthEntry (add (mul t n) j) N)) := by
  have hn := n_ne_zero_of_lt_mul (lt_mul_of_lt_lt hi hj)
  simp only [matMul]
  rw [nthEntry_buildNPow _ ⟨_, lt_mul_of_lt_lt hi hj⟩, buildEntries_get]
  simp only [zero_add]
  apply finSumRing_congr; intro t _
  rw [div_of_add_mul hn hj, mod_of_add_mul hn hj]

private theorem nthEntry_matMul' {n : ℕ₀} (rng : HFRing) (M N : HFSet)
    {i j : ℕ₀} (hi : i < n) (hj : j < n) :
    nthEntry (add (mul i n) j) (matMul n rng M N) =
    finSumRing rng n (fun t =>
      rng.mul (nthEntry (add (mul i n) t) M)
              (nthEntry (add (mul t n) j) N)) := by
  have h := nthEntry_matMul rng M N hi hj
  rw [mul_comm n i] at h; exact h

-- ══════════════════════════════════════════════════════════════════
-- §8. Clausuras
-- ══════════════════════════════════════════════════════════════════

private theorem matAdd_mem {n : ℕ₀} (rng : HFRing) {M N : HFSet}
    (hM : M ∈ matrixCarrier n rng) (hN : N ∈ matrixCarrier n rng) :
    matAdd n rng M N ∈ matrixCarrier n rng := by
  apply mem_buildNPow; intro i
  rw [zipWith_get, deconNPow_get, deconNPow_get]
  exact rng.add_closed (nthEntry_mem hM _ i.isLt) (nthEntry_mem hN _ i.isLt)

private theorem matNeg_mem {n : ℕ₀} (rng : HFRing) {M : HFSet}
    (hM : M ∈ matrixCarrier n rng) : matNeg n rng M ∈ matrixCarrier n rng := by
  apply mem_buildNPow; intro i
  rw [map_get, deconNPow_get]; exact rng.neg_closed (nthEntry_mem hM _ i.isLt)

private theorem matZero_mem (n : ℕ₀) (rng : HFRing) :
    matZero n rng ∈ matrixCarrier n rng := by
  apply mem_buildNPow; intro i; rw [constList_get]; exact rng.zero_mem

private theorem matOne_mem (n : ℕ₀) (rng : HFRing) :
    matOne n rng ∈ matrixCarrier n rng := by
  apply mem_buildNPow; intro i; rw [buildEntries_get]; simp only [zero_add]
  split
  · exact rng.one_mem
  · exact rng.zero_mem

private theorem matMul_mem {n : ℕ₀} (rng : HFRing) {M N : HFSet}
    (hM : M ∈ matrixCarrier n rng) (hN : N ∈ matrixCarrier n rng) :
    matMul n rng M N ∈ matrixCarrier n rng := by
  apply mem_buildNPow; intro ⟨k, hk⟩
  rw [buildEntries_get]; simp only [zero_add]
  obtain ⟨hdi, hmo, _⟩ := lt_mul_decompose hk
  apply finSumRing_mem; intro t ht
  exact rng.mul_closed
    (nthEntry_mem hM _ (lt_mul_of_mul_lt hdi ht))
    (nthEntry_mem hN _ (lt_mul_of_mul_lt ht hmo))

-- ══════════════════════════════════════════════════════════════════
-- §9. Axiomas de anillo
-- ══════════════════════════════════════════════════════════════════

private theorem mat_add_assoc {n : ℕ₀} (rng : HFRing) {A B C : HFSet}
    (hA : A ∈ matrixCarrier n rng) (hB : B ∈ matrixCarrier n rng)
    (hC : C ∈ matrixCarrier n rng) :
    matAdd n rng A (matAdd n rng B C) = matAdd n rng (matAdd n rng A B) C := by
  apply nPow_ext (matAdd_mem rng hA (matAdd_mem rng hB hC))
                 (matAdd_mem rng (matAdd_mem rng hA hB) hC)
  intro j hj
  rw [nthEntry_matAdd rng _ _ hj, nthEntry_matAdd rng B C hj,
      nthEntry_matAdd rng _ _ hj, nthEntry_matAdd rng A B hj]
  exact (rng.add_assoc (nthEntry_mem hA _ hj) (nthEntry_mem hB _ hj) (nthEntry_mem hC _ hj)).symm

private theorem mat_add_comm {n : ℕ₀} (rng : HFRing) {A B : HFSet}
    (hA : A ∈ matrixCarrier n rng) (hB : B ∈ matrixCarrier n rng) :
    matAdd n rng A B = matAdd n rng B A := by
  apply nPow_ext (matAdd_mem rng hA hB) (matAdd_mem rng hB hA)
  intro j hj
  rw [nthEntry_matAdd rng _ _ hj, nthEntry_matAdd rng _ _ hj]
  exact rng.add_comm (nthEntry_mem hA _ hj) (nthEntry_mem hB _ hj)

private theorem mat_zero_add {n : ℕ₀} (rng : HFRing) {A : HFSet}
    (hA : A ∈ matrixCarrier n rng) : matAdd n rng (matZero n rng) A = A := by
  apply nPow_ext (matAdd_mem rng (matZero_mem n rng) hA) hA
  intro j hj
  rw [nthEntry_matAdd rng _ _ hj, nthEntry_matZero rng hj]
  exact rng.zero_add (nthEntry_mem hA _ hj)

private theorem mat_neg_add {n : ℕ₀} (rng : HFRing) {A : HFSet}
    (hA : A ∈ matrixCarrier n rng) : matAdd n rng (matNeg n rng A) A = matZero n rng := by
  apply nPow_ext (matAdd_mem rng (matNeg_mem rng hA) hA) (matZero_mem n rng)
  intro j hj
  rw [nthEntry_matAdd rng _ _ hj, nthEntry_matNeg rng _ hj, nthEntry_matZero rng hj]
  exact rng.neg_add (nthEntry_mem hA _ hj)

-- unpack k = n*(k/n) + (k%n) with bounds
private theorem unpack {n k : ℕ₀} (hk : k < mul n n) :
    add (mul n (div k n)) (mod k n) = k ∧ div k n < n ∧ mod k n < n :=
  ⟨(lt_mul_decompose hk).2.2, (lt_mul_decompose hk).1, (lt_mul_decompose hk).2.1⟩

private theorem mat_mul_one {n : ℕ₀} (rng : HFRing) {A : HFSet}
    (hA : A ∈ matrixCarrier n rng) : matMul n rng A (matOne n rng) = A := by
  apply nPow_ext (matMul_mem rng hA (matOne_mem n rng)) hA
  intro k hk
  obtain ⟨hspec, hdi, hmo⟩ := unpack hk
  have hn := n_ne_zero_of_lt_mul hk
  rw [← hspec, nthEntry_matMul rng A (matOne n rng) hdi hmo]
  rw [finSumRing_congr (fun t ht => by
    rw [nthEntry_matOne rng (lt_mul_of_mul_lt ht hmo),
        div_of_mul_add hn hmo, mod_of_mul_add hn hmo])]
  rw [finSumRing_Kronecker hmo (fun t ht => nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))]
  rw [mul_comm (div k n) n, hspec]

private theorem mat_one_mul {n : ℕ₀} (rng : HFRing) {A : HFSet}
    (hA : A ∈ matrixCarrier n rng) : matMul n rng (matOne n rng) A = A := by
  apply nPow_ext (matMul_mem rng (matOne_mem n rng) hA) hA
  intro k hk
  obtain ⟨hspec, hdi, hmo⟩ := unpack hk
  have hn := n_ne_zero_of_lt_mul hk
  rw [← hspec, nthEntry_matMul rng (matOne n rng) A hdi hmo]
  rw [finSumRing_congr (fun t ht => by
    rw [nthEntry_matOne rng (lt_mul_of_mul_lt hdi ht),
        div_of_mul_add hn ht, mod_of_mul_add hn ht])]
  rw [finSumRing_Kronecker_left hdi (fun t ht => nthEntry_mem hA _ (lt_mul_of_mul_lt ht hmo))]
  rw [mul_comm (div k n) n, hspec]

private theorem mat_left_distrib {n : ℕ₀} (rng : HFRing) {A B C : HFSet}
    (hA : A ∈ matrixCarrier n rng) (hB : B ∈ matrixCarrier n rng)
    (hC : C ∈ matrixCarrier n rng) :
    matMul n rng A (matAdd n rng B C) =
    matAdd n rng (matMul n rng A B) (matMul n rng A C) := by
  apply nPow_ext (matMul_mem rng hA (matAdd_mem rng hB hC))
                 (matAdd_mem rng (matMul_mem rng hA hB) (matMul_mem rng hA hC))
  intro k hk
  obtain ⟨hspec, hdi, hmo⟩ := unpack hk
  rw [← hspec]
  rw [nthEntry_matMul rng A (matAdd n rng B C) hdi hmo,
      nthEntry_matAdd rng _ _ (lt_mul_of_lt_lt hdi hmo),
      nthEntry_matMul rng A B hdi hmo, nthEntry_matMul rng A C hdi hmo]
  rw [finSumRing_congr (fun t ht => by
    rw [nthEntry_matAdd rng _ _ (lt_mul_of_mul_lt ht hmo),
        rng.left_distrib (nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))
          (nthEntry_mem hB _ (lt_mul_of_mul_lt ht hmo))
          (nthEntry_mem hC _ (lt_mul_of_mul_lt ht hmo))])]
  exact finSumRing_add
    (fun t ht => rng.mul_closed (nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))
                                (nthEntry_mem hB _ (lt_mul_of_mul_lt ht hmo)))
    (fun t ht => rng.mul_closed (nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))
                                (nthEntry_mem hC _ (lt_mul_of_mul_lt ht hmo)))

private theorem mat_right_distrib {n : ℕ₀} (rng : HFRing) {A B C : HFSet}
    (hA : A ∈ matrixCarrier n rng) (hB : B ∈ matrixCarrier n rng)
    (hC : C ∈ matrixCarrier n rng) :
    matMul n rng (matAdd n rng A B) C =
    matAdd n rng (matMul n rng A C) (matMul n rng B C) := by
  apply nPow_ext (matMul_mem rng (matAdd_mem rng hA hB) hC)
                 (matAdd_mem rng (matMul_mem rng hA hC) (matMul_mem rng hB hC))
  intro k hk
  obtain ⟨hspec, hdi, hmo⟩ := unpack hk
  rw [← hspec]
  rw [nthEntry_matMul rng (matAdd n rng A B) C hdi hmo,
      nthEntry_matAdd rng _ _ (lt_mul_of_lt_lt hdi hmo),
      nthEntry_matMul rng A C hdi hmo, nthEntry_matMul rng B C hdi hmo]
  rw [finSumRing_congr (fun t ht => by
    rw [nthEntry_matAdd rng _ _ (lt_mul_of_mul_lt hdi ht),
        rng.right_distrib (nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))
          (nthEntry_mem hB _ (lt_mul_of_mul_lt hdi ht))
          (nthEntry_mem hC _ (lt_mul_of_mul_lt ht hmo))])]
  exact finSumRing_add
    (fun t ht => rng.mul_closed (nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))
                                (nthEntry_mem hC _ (lt_mul_of_mul_lt ht hmo)))
    (fun t ht => rng.mul_closed (nthEntry_mem hB _ (lt_mul_of_mul_lt hdi ht))
                                (nthEntry_mem hC _ (lt_mul_of_mul_lt ht hmo)))

private theorem mat_mul_assoc {n : ℕ₀} (rng : HFRing) {A B C : HFSet}
    (hA : A ∈ matrixCarrier n rng) (hB : B ∈ matrixCarrier n rng)
    (hC : C ∈ matrixCarrier n rng) :
    matMul n rng A (matMul n rng B C) = matMul n rng (matMul n rng A B) C := by
  apply nPow_ext (matMul_mem rng hA (matMul_mem rng hB hC))
                 (matMul_mem rng (matMul_mem rng hA hB) hC)
  intro k hk
  obtain ⟨hspec, hdi, hmo⟩ := unpack hk
  rw [← hspec]
  rw [nthEntry_matMul rng A (matMul n rng B C) hdi hmo,
      nthEntry_matMul rng (matMul n rng A B) C hdi hmo]
  -- LHS: Σ_t A[i,t] * (Σ_s B[t,s]*C[s,j])  →  Σ_t Σ_s A[i,t]*(B[t,s]*C[s,j])
  rw [finSumRing_congr (fun t ht => by
    rw [nthEntry_matMul' rng B C ht hmo,
        mul_finSumRing (nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))
          (fun s hs => rng.mul_closed (nthEntry_mem hB _ (lt_mul_of_mul_lt ht hs))
                                      (nthEntry_mem hC _ (lt_mul_of_mul_lt hs hmo)))])]
  -- Swap: Σ_t Σ_s  →  Σ_s Σ_t
  rw [finSumRing_swap (fun t s (ht : t < n) (hs : s < n) =>
    rng.mul_closed
      (nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))
      (rng.mul_closed (nthEntry_mem hB _ (lt_mul_of_mul_lt ht hs))
                      (nthEntry_mem hC _ (lt_mul_of_mul_lt hs hmo))))]
  -- Point-wise: A[i,t]*(B[t,s]*C[s,j])  →  (A[i,t]*B[t,s])*C[s,j]
  rw [finSumRing_congr (fun s hs => finSumRing_congr (fun t ht =>
    (rng.mul_assoc (nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))
                   (nthEntry_mem hB _ (lt_mul_of_mul_lt ht hs))
                   (nthEntry_mem hC _ (lt_mul_of_mul_lt hs hmo))).symm))]
  -- Now LHS = Σ_s Σ_t (A[i,t]*B[t,s])*C[s,j]; flip and expand RHS
  symm
  rw [finSumRing_congr (fun s hs => by
    rw [nthEntry_matMul' rng A B hdi hs,
        finSumRing_mul (nthEntry_mem hC _ (lt_mul_of_mul_lt hs hmo))
          (fun t ht => rng.mul_closed (nthEntry_mem hA _ (lt_mul_of_mul_lt hdi ht))
                                      (nthEntry_mem hB _ (lt_mul_of_mul_lt ht hs)))])]

-- ══════════════════════════════════════════════════════════════════
-- §10. HFMatrixRing
-- ══════════════════════════════════════════════════════════════════

/-- El anillo de matrices n×n sobre `rng` con portador `nPow rng.R (n²)`. -/
def HFMatrixRing (n : ℕ₀) (rng : HFRing) : HFRing where
  R    := matrixCarrier n rng
  add  := matAdd n rng
  mul  := matMul n rng
  zero := matZero n rng
  one  := matOne n rng
  neg  := matNeg n rng
  zero_mem     := matZero_mem n rng
  one_mem      := matOne_mem n rng
  add_closed   := fun hM hN => matAdd_mem rng hM hN
  mul_closed   := fun hM hN => matMul_mem rng hM hN
  neg_closed   := fun hM => matNeg_mem rng hM
  add_assoc    := fun hA hB hC => (mat_add_assoc rng hA hB hC).symm
  add_comm     := mat_add_comm rng
  zero_add     := mat_zero_add rng
  neg_add      := mat_neg_add rng
  mul_assoc    := fun hA hB hC => (mat_mul_assoc rng hA hB hC).symm
  mul_one      := mat_mul_one rng
  one_mul      := mat_one_mul rng
  left_distrib  := mat_left_distrib rng
  right_distrib := mat_right_distrib rng

end HFAlgebra
