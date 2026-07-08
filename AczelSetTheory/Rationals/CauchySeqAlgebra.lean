/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/CauchySeqAlgebra.lean
-- Álgebra general de sucesiones de Cauchy en ℚ₀.

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.AbsVal
import AczelSetTheory.Rationals.IsCauchy
import AczelSetTheory.Rationals.Inv
import AczelSetTheory.Rationals.MinAdd
import Peano.PeanoNat.Arith

namespace ℚ₀

/-- El tipo de sucesiones de Cauchy en ℚ₀, base para los números computables. -/
def CauchySeq := { f : ℕ₀ → ℚ₀ // ℚ₀.IsCauchy f }

/-- Relación de equivalencia diádica: f ∼ g si el límite de f - g es 0.
En formato constructivo: ∀ k, ∃ N, ∀ m ≥ N, |f(m) - g(m)| ≤ 1/2^k. -/
def CauchySeq.Equiv (f g : CauchySeq) : Prop :=
  ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, le₀ N m → ℚ₀.absVal (f.val m - g.val m) ≤ ℚ₀.pow2 k

theorem CauchySeq.Equiv_refl (f : CauchySeq) : CauchySeq.Equiv f f := by
  intro k
  exists 𝟘
  intro m _
  have hzero : f.val m - f.val m = 0 := ℚ₀.add_neg_self (f.val m)
  rw [hzero, ℚ₀.absVal_zero]
  exact ℚ₀.pow2_nonneg k

theorem CauchySeq.Equiv_symm {f g : CauchySeq} (h : CauchySeq.Equiv f g) : CauchySeq.Equiv g f := by
  intro k
  rcases h k with ⟨N, hN⟩
  exists N
  intro m hm
  have hsym : ℚ₀.absVal (g.val m - f.val m) = ℚ₀.absVal (f.val m - g.val m) := ℚ₀.absVal_sub_comm (g.val m) (f.val m)
  rw [hsym]
  exact hN m hm

theorem CauchySeq.Equiv_trans {f g h : CauchySeq} (h1 : CauchySeq.Equiv f g) (h2 : CauchySeq.Equiv g h) : CauchySeq.Equiv f h := by
  intro k
  rcases h1 (σ k) with ⟨N1, hN1⟩
  rcases h2 (σ k) with ⟨N2, hN2⟩
  exists Peano.Lattice.max N1 N2
  intro m hm
  have hN1_le : le₀ N1 m := Peano.Order.le_trans N1 (Peano.Lattice.max N1 N2) m (Peano.Lattice.le_max_left N1 N2) hm
  have hN2_le : le₀ N2 m := Peano.Order.le_trans N2 (Peano.Lattice.max N1 N2) m (Peano.Lattice.le_max_right N1 N2) hm
  have h_bound1 := hN1 m hN1_le
  have h_bound2 := hN2 m hN2_le
  
  let a : ℚ₀ := f.val m
  let b : ℚ₀ := g.val m
  let c : ℚ₀ := h.val m
  
  have h_bound1_let : (Add.add a (-b)).absVal ≤ ℚ₀.pow2 (σ k) := h_bound1
  have h_bound2_let : (Add.add b (-c)).absVal ≤ ℚ₀.pow2 (σ k) := h_bound2
  
  have h_eq : Add.add a (-c) = Add.add (Add.add a (-b)) (Add.add b (-c)) := by
    calc
      Add.add a (-c) = Add.add a (Add.add 0 (-c)) := by rw [ℚ₀.zero_add (-c)]
      _ = Add.add a (Add.add (Add.add (-b) b) (-c)) := by rw [ℚ₀.neg_add_self b]
      _ = Add.add a (Add.add (-b) (Add.add b (-c))) := by rw [ℚ₀.add_assoc (-b) b (-c)]
      _ = Add.add (Add.add a (-b)) (Add.add b (-c)) := by rw [ℚ₀.add_assoc a (-b) (Add.add b (-c))]

  have h_tri : (Add.add a (-c)).absVal ≤ Add.add (Add.add a (-b)).absVal (Add.add b (-c)).absVal := by
    rw [h_eq]
    exact ℚ₀.absVal_add_le (Add.add a (-b)) (Add.add b (-c))
    
  have h_add_le : Add.add (Add.add a (-b)).absVal (Add.add b (-c)).absVal ≤ Add.add (ℚ₀.pow2 (σ k)) (ℚ₀.pow2 (σ k)) := by
    have ha : Add.add (Add.add a (-b)).absVal (Add.add b (-c)).absVal ≤ Add.add (ℚ₀.pow2 (σ k)) (Add.add b (-c)).absVal := 
      ℚ₀.add_le_add_right h_bound1_let (Add.add b (-c)).absVal
    have hb : Add.add (ℚ₀.pow2 (σ k)) (Add.add b (-c)).absVal ≤ Add.add (ℚ₀.pow2 (σ k)) (ℚ₀.pow2 (σ k)) := 
      ℚ₀.add_le_add_left h_bound2_let (ℚ₀.pow2 (σ k))
    exact ℚ₀.le_trans ha hb

  have h_trans := ℚ₀.le_trans h_tri h_add_le
  have h_pow_add := ℚ₀.pow2_succ_add k
  
  rw [h_pow_add] at h_trans
  exact h_trans

-- ============================================================
-- Suma, Resta y Negación (Término a Término)
-- ============================================================

/-- Suma de sucesiones de Cauchy. -/
def CauchySeq.add (f g : CauchySeq) : CauchySeq :=
  ⟨fun n => Add.add (f.val (σ n)) (g.val (σ n)), by
    intro n m
    let a := f.val (σ n)
    let b := g.val (σ n)
    let c := f.val (σ m)
    let d := g.val (σ m)
    
    have h_bound_f : (Add.add a (-c)).absVal ≤ ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m)) := f.property (σ n) (σ m)
    have h_bound_g : (Add.add b (-d)).absVal ≤ ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m)) := g.property (σ n) (σ m)
    
    have h_eq : Add.add (Add.add a b) (Neg.neg (Add.add c d)) = Add.add (Add.add a (-c)) (Add.add b (-d)) := by
      calc
        Add.add (Add.add a b) (Neg.neg (Add.add c d)) = Add.add (Add.add a b) (Add.add (-c) (-d)) := by rw [ℚ₀.neg_add c d]
        _ = Add.add a (Add.add b (Add.add (-c) (-d))) := by rw [ℚ₀.add_assoc a b (Add.add (-c) (-d))]
        _ = Add.add a (Add.add (Add.add b (-c)) (-d)) := by rw [(ℚ₀.add_assoc b (-c) (-d)).symm]
        _ = Add.add a (Add.add (Add.add (-c) b) (-d)) := by rw [ℚ₀.add_comm b (-c)]
        _ = Add.add a (Add.add (-c) (Add.add b (-d))) := by rw [ℚ₀.add_assoc (-c) b (-d)]
        _ = Add.add (Add.add a (-c)) (Add.add b (-d)) := by rw [(ℚ₀.add_assoc a (-c) (Add.add b (-d))).symm]

    have h_tri : (Add.add (Add.add a b) (Neg.neg (Add.add c d))).absVal ≤ Add.add (Add.add a (-c)).absVal (Add.add b (-d)).absVal := by
      rw [h_eq]
      exact ℚ₀.absVal_add_le (Add.add a (-c)) (Add.add b (-d))
      
    have h_add_le : Add.add (Add.add a (-c)).absVal (Add.add b (-d)).absVal ≤ Add.add (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) := by
      have ha : Add.add (Add.add a (-c)).absVal (Add.add b (-d)).absVal ≤ Add.add (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) (Add.add b (-d)).absVal := 
        ℚ₀.add_le_add_right h_bound_f (Add.add b (-d)).absVal
      have hb : Add.add (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) (Add.add b (-d)).absVal ≤ Add.add (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) := 
        ℚ₀.add_le_add_left h_bound_g (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m)))
      exact ℚ₀.le_trans ha hb

    have h_trans := ℚ₀.le_trans h_tri h_add_le
    
    have h_min_succ : Peano.Lattice.min (σ n) (σ m) = σ (Peano.Lattice.min n m) := by
      exact Peano.Lattice.min_succ_succ n m
      
    rw [h_min_succ] at h_trans
    have h_pow_add := ℚ₀.pow2_succ_add (Peano.Lattice.min n m)
    rw [h_pow_add] at h_trans
    exact h_trans⟩

instance : Add CauchySeq := ⟨CauchySeq.add⟩

/-- Negación de una sucesión de Cauchy. -/
def CauchySeq.neg (f : CauchySeq) : CauchySeq :=
  ⟨fun n => Neg.neg (f.val n), by
    intro n m
    let a := f.val n
    let b := f.val m
    have h_bound : (Add.add a (Neg.neg b)).absVal ≤ ℚ₀.pow2 (Peano.Lattice.min n m) := f.property n m
    
    have h_eq : Add.add (Neg.neg a) (Neg.neg (Neg.neg b)) = Neg.neg (Add.add a (Neg.neg b)) := by
      exact (ℚ₀.neg_add a (Neg.neg b)).symm
      
    have h_abs_eq : (Add.add (Neg.neg a) (Neg.neg (Neg.neg b))).absVal = (Add.add a (Neg.neg b)).absVal := by
      rw [h_eq]
      exact ℚ₀.absVal_neg (Add.add a (Neg.neg b))
      
    change (Add.add (Neg.neg a) (Neg.neg (Neg.neg b))).absVal ≤ ℚ₀.pow2 (Peano.Lattice.min n m)
    rw [h_abs_eq]
    exact h_bound⟩

instance : Neg CauchySeq := ⟨CauchySeq.neg⟩

/-- Resta de sucesiones de Cauchy. -/
def CauchySeq.sub (f g : CauchySeq) : CauchySeq :=
  f + (-g)

instance : Sub CauchySeq := ⟨CauchySeq.sub⟩

-- ============================================================
-- Acotación (Boundedness)
-- ============================================================

/-- Una sucesión f en ℚ₀ está acotada si existe M tal que ∀ n, |f(n)| ≤ M. -/
def CauchySeq.IsBounded (f : CauchySeq) : Prop :=
  ∃ M : ℚ₀, ∀ n : ℕ₀, ℚ₀.absVal (f.val n) ≤ M

theorem CauchySeq.isBounded_of_isCauchy (f : CauchySeq) : CauchySeq.IsBounded f := by
  let M : ℚ₀ := Add.add (ℚ₀.pow2 𝟘) (ℚ₀.absVal (f.val 𝟘))
  exists M
  intro n
  
  have h_cauchy := f.property n 𝟘
  have h_min : Peano.Lattice.min n 𝟘 = 𝟘 := Peano.Lattice.min_0_abs n
  rw [h_min] at h_cauchy
  
  let fn := f.val n
  let f0 := f.val 𝟘
  
  have h_tri : ℚ₀.absVal fn ≤ Add.add (ℚ₀.absVal (Add.add fn (Neg.neg f0))) (ℚ₀.absVal f0) := by
    have h_eq : fn = Add.add (Add.add fn (Neg.neg f0)) f0 := by
      calc
        fn = Add.add fn 0 := by rw [ℚ₀.add_zero fn]
        _ = Add.add fn (Add.add (Neg.neg f0) f0) := by rw [ℚ₀.neg_add_self f0]
        _ = Add.add (Add.add fn (Neg.neg f0)) f0 := by rw [ℚ₀.add_assoc fn (Neg.neg f0) f0]
    
    have h_abs_eq : ℚ₀.absVal fn = ℚ₀.absVal (Add.add (Add.add fn (Neg.neg f0)) f0) := by
      exact congrArg ℚ₀.absVal h_eq
      
    rw [h_abs_eq]
    exact ℚ₀.absVal_add_le (Add.add fn (Neg.neg f0)) f0
    
  have h_add_le : Add.add (ℚ₀.absVal (Add.add fn (Neg.neg f0))) (ℚ₀.absVal f0) ≤ Add.add (ℚ₀.pow2 𝟘) (ℚ₀.absVal f0) := 
    ℚ₀.add_le_add_right h_cauchy (ℚ₀.absVal f0)
    
  exact ℚ₀.le_trans h_tri h_add_le

-- ============================================================
-- Multiplicación (Término a Término)
-- ============================================================

/-- Computa la cota constructiva de la sucesión. -/
def CauchySeq.boundVal (f : CauchySeq) : ℚ₀ := Add.add (ℚ₀.pow2 𝟘) (ℚ₀.absVal (f.val 𝟘))

theorem CauchySeq.boundVal_prop (f : CauchySeq) (n : ℕ₀) : ℚ₀.absVal (f.val n) ≤ f.boundVal := by
  have h_cauchy := f.property n 𝟘
  have h_min : Peano.Lattice.min n 𝟘 = 𝟘 := Peano.Lattice.min_0_abs n
  rw [h_min] at h_cauchy
  have h_eq : f.val n = Add.add (Add.add (f.val n) (Neg.neg (f.val 𝟘))) (f.val 𝟘) := by
    calc
      f.val n = Add.add (f.val n) 0 := by rw [ℚ₀.add_zero (f.val n)]
      _ = Add.add (f.val n) (Add.add (Neg.neg (f.val 𝟘)) (f.val 𝟘)) := by rw [ℚ₀.neg_add_self (f.val 𝟘)]
      _ = Add.add (Add.add (f.val n) (Neg.neg (f.val 𝟘))) (f.val 𝟘) := by rw [ℚ₀.add_assoc (f.val n) (Neg.neg (f.val 𝟘)) (f.val 𝟘)]
  have h_abs_eq : ℚ₀.absVal (f.val n) = ℚ₀.absVal (Add.add (Add.add (f.val n) (Neg.neg (f.val 𝟘))) (f.val 𝟘)) := congrArg ℚ₀.absVal h_eq
  rw [h_abs_eq]
  have h_tri := ℚ₀.absVal_add_le (Add.add (f.val n) (Neg.neg (f.val 𝟘))) (f.val 𝟘)
  have h_add_le : Add.add (ℚ₀.absVal (Add.add (f.val n) (Neg.neg (f.val 𝟘)))) (ℚ₀.absVal (f.val 𝟘)) ≤ Add.add (ℚ₀.pow2 𝟘) (ℚ₀.absVal (f.val 𝟘)) := 
    ℚ₀.add_le_add_right h_cauchy (ℚ₀.absVal (f.val 𝟘))
  exact ℚ₀.le_trans h_tri h_add_le

/-- Encuentra un K tal que M_f + M_g <= 2^K aproximado usando division entera. -/
def CauchySeq.mulBound (f g : CauchySeq) : ℕ₀ :=
  ℚ₀.boundNat (Add.add (f.boundVal) (g.boundVal))

theorem cauchy_mul_is_cauchy (f g : CauchySeq) (K : ℕ₀) (hK : CauchySeq.mulBound f g ≤ K) :
    ℚ₀.IsCauchy (fun n => f.val (Peano.Add.add n K) * g.val (Peano.Add.add n K)) := by
  intro n m
  have h_bound_f : ∀ k, ℚ₀.absVal (f.val k) ≤ f.boundVal := f.boundVal_prop
  have h_bound_g : ∀ k, ℚ₀.absVal (g.val k) ≤ g.boundVal := g.boundVal_prop
  
  let fnK := f.val (Peano.Add.add n K)
  let gnK := g.val (Peano.Add.add n K)
  let fmK := f.val (Peano.Add.add m K)
  let gmK := g.val (Peano.Add.add m K)
  
  have h_triangle : ℚ₀.absVal (fnK * gnK - fmK * gmK) ≤ 
    Add.add (Mul.mul (ℚ₀.absVal fnK) (ℚ₀.absVal (gnK - gmK))) (Mul.mul (ℚ₀.absVal gmK) (ℚ₀.absVal (fnK - fmK))) := 
      ℚ₀.absVal_mul_sub_mul fnK gnK fmK gmK
      
  have h_f_cauchy := f.property (Peano.Add.add n K) (Peano.Add.add m K)
  have h_g_cauchy := g.property (Peano.Add.add n K) (Peano.Add.add m K)
  
  have h_min : Peano.Lattice.min (Peano.Add.add n K) (Peano.Add.add m K) = Peano.Add.add (Peano.Lattice.min n m) K :=
    Peano.Arith.min_add_add_right n m K
    
  rw [h_min] at h_f_cauchy h_g_cauchy
  
  have h_pow2_add : ℚ₀.pow2 (Peano.Add.add (Peano.Lattice.min n m) K) = 
    Mul.mul (ℚ₀.pow2 (Peano.Lattice.min n m)) (ℚ₀.pow2 K) := ℚ₀.pow2_add _ _
    
  rw [h_pow2_add] at h_f_cauchy h_g_cauchy
  
  have h_part1 : Mul.mul (ℚ₀.absVal fnK) (ℚ₀.absVal (gnK - gmK)) ≤ Mul.mul f.boundVal (Mul.mul (ℚ₀.pow2 (Peano.Lattice.min n m)) (ℚ₀.pow2 K)) := by
    apply ℚ₀.mul_le_mul (h_bound_f _) h_g_cauchy (ℚ₀.absVal_nonneg _) (ℚ₀.absVal_nonneg _)
    
  have h_part2 : Mul.mul (ℚ₀.absVal gmK) (ℚ₀.absVal (fnK - fmK)) ≤ Mul.mul g.boundVal (Mul.mul (ℚ₀.pow2 (Peano.Lattice.min n m)) (ℚ₀.pow2 K)) := by
    apply ℚ₀.mul_le_mul (h_bound_g _) h_f_cauchy (ℚ₀.absVal_nonneg _) (ℚ₀.absVal_nonneg _)
    
  have h_parts_add : Add.add (Mul.mul (ℚ₀.absVal fnK) (ℚ₀.absVal (gnK - gmK))) (Mul.mul (ℚ₀.absVal gmK) (ℚ₀.absVal (fnK - fmK))) ≤ 
    Add.add (Mul.mul f.boundVal (Mul.mul (ℚ₀.pow2 (Peano.Lattice.min n m)) (ℚ₀.pow2 K))) (Mul.mul g.boundVal (Mul.mul (ℚ₀.pow2 (Peano.Lattice.min n m)) (ℚ₀.pow2 K))) := by
    exact ℚ₀.add_le_add h_part1 h_part2
    
  let M := ℚ₀.pow2 (Peano.Lattice.min n m)
  let P := ℚ₀.pow2 K
  have hrw1 : Add.add (Mul.mul f.boundVal (Mul.mul M P)) (Mul.mul g.boundVal (Mul.mul M P)) = 
    Mul.mul (Add.add f.boundVal g.boundVal) (Mul.mul M P) := by
    exact Eq.symm (ℚ₀.right_distrib f.boundVal g.boundVal (Mul.mul M P))
  rw [hrw1] at h_parts_add
  
  have hrw2 : Mul.mul (Add.add f.boundVal g.boundVal) (Mul.mul M P) = Mul.mul (Mul.mul (Add.add f.boundVal g.boundVal) P) M := by
    have h_comm : Mul.mul M P = Mul.mul P M := ℚ₀.mul_comm M P
    rw [h_comm]
    exact Eq.symm (ℚ₀.mul_assoc (Add.add f.boundVal g.boundVal) P M)
  rw [hrw2] at h_parts_add
  
  have h_bound_add : Add.add f.boundVal g.boundVal ≤ ℚ₀.ofNat₀ K := by
    have h1 : Add.add f.boundVal g.boundVal ≤ ℚ₀.absVal (Add.add f.boundVal g.boundVal) := ℚ₀.le_absVal (Add.add f.boundVal g.boundVal)
    have h2 : ℚ₀.absVal (Add.add f.boundVal g.boundVal) ≤ ℚ₀.ofNat₀ (CauchySeq.mulBound f g) := ℚ₀.le_boundNat (Add.add f.boundVal g.boundVal)
    have h3 : ℚ₀.ofNat₀ (CauchySeq.mulBound f g) ≤ ℚ₀.ofNat₀ K := ℚ₀.ofNat₀_le_ofNat₀ hK
    exact ℚ₀.le_trans h1 (ℚ₀.le_trans h2 h3)
    
  have h_mul_P : Mul.mul (Add.add f.boundVal g.boundVal) P ≤ ℚ₀.ofNat₀ 𝟙 := by
    have h1 : Mul.mul (Add.add f.boundVal g.boundVal) P ≤ Mul.mul (ℚ₀.ofNat₀ K) P := ℚ₀.mul_le_mul_right_of_nonneg h_bound_add (ℚ₀.pow2_nonneg K)
    have h2 : Mul.mul (ℚ₀.ofNat₀ K) P ≤ ℚ₀.ofNat₀ 𝟙 := ℚ₀.pow2_bound K
    exact ℚ₀.le_trans h1 h2
    
  have h_mul_M : Mul.mul (Mul.mul (Add.add f.boundVal g.boundVal) P) M ≤ Mul.mul (ℚ₀.ofNat₀ 𝟙) M := 
    ℚ₀.mul_le_mul_right_of_nonneg h_mul_P (ℚ₀.pow2_nonneg (Peano.Lattice.min n m))
  have h_one_M : Mul.mul (ℚ₀.ofNat₀ 𝟙) M = M := ℚ₀.one_mul M
  rw [h_one_M] at h_mul_M
  
  exact ℚ₀.le_trans h_triangle (ℚ₀.le_trans h_parts_add h_mul_M)

/-- Multiplicación de sucesiones de Cauchy. -/
def CauchySeq.mul (f g : CauchySeq) : CauchySeq :=
  let K := CauchySeq.mulBound f g
  have hK : CauchySeq.mulBound f g ≤ K := Peano.Order.le_refl _
  ⟨fun n => f.val (Peano.Add.add n K) * g.val (Peano.Add.add n K), cauchy_mul_is_cauchy f g K hK⟩

instance : Mul CauchySeq := ⟨CauchySeq.mul⟩

-- ============================================================
-- Propiedad Positiva y Orden
-- ============================================================

/-- Una sucesión f es estrictamente positiva si existe k y N tal que
f(m) ≥ 1/2^k para todo m ≥ N. Al ser una estructura, contiene testigos constructivos. -/
structure CauchySeq.Pos (f : CauchySeq) where
  k : ℕ₀
  N : ℕ₀
  proof : ∀ m, le₀ N m → ℚ₀.pow2 k ≤ f.val m

/-- Relación de orden estricto f < g ↔ Pos (g - f). -/
def CauchySeq.LT (f g : CauchySeq) : Prop :=
  Nonempty (CauchySeq.Pos (g - f))

instance : LT CauchySeq := ⟨CauchySeq.LT⟩

/-- Relación de orden parcial f ≤ g ↔ ¬(g < f). -/
def CauchySeq.LE (f g : CauchySeq) : Prop :=
  ¬ (g < f)

instance : LE CauchySeq := ⟨CauchySeq.LE⟩

/-- Relación de estar alejado de cero (positiva o negativamente). -/
def CauchySeq.ApartZero (f : CauchySeq) : Type :=
  Sum (CauchySeq.Pos f) (CauchySeq.Pos (-f))

/-- Extrae el k de la prueba de alejamiento de cero. -/
def CauchySeq.ApartZero.k (f : CauchySeq) (h : CauchySeq.ApartZero f) : ℕ₀ :=
  match h with
  | Sum.inl p => p.k
  | Sum.inr p => p.k

/-- Extrae el N de la prueba de alejamiento de cero. -/
def CauchySeq.ApartZero.N (f : CauchySeq) (h : CauchySeq.ApartZero f) : ℕ₀ :=
  match h with
  | Sum.inl p => p.N
  | Sum.inr p => p.N

/-- Calcula el desplazamiento K necesario para que la inversa mantenga el ritmo de Cauchy.
K = N + 2k. -/
def CauchySeq.invBound (f : CauchySeq) (h : CauchySeq.ApartZero f) : ℕ₀ :=
  Peano.Add.add (h.N f) (Peano.Add.add (h.k f) (h.k f))

theorem ApartZero_absVal_bound (f : CauchySeq) (h : CauchySeq.ApartZero f) (m : ℕ₀)
    (hm : Peano.Order.le₀ (CauchySeq.ApartZero.N f h) m) :
    ℚ₀.pow2 (CauchySeq.ApartZero.k f h) ≤ ℚ₀.absVal (f.val m) := by
  cases h with
  | inl p =>
    have h_pos : ℚ₀.pow2 p.k ≤ f.val m := p.proof m hm
    have h_le_abs : f.val m ≤ ℚ₀.absVal (f.val m) := ℚ₀.le_absVal (f.val m)
    exact ℚ₀.le_trans h_pos h_le_abs
  | inr p =>
    have h_pos : ℚ₀.pow2 p.k ≤ (-f).val m := p.proof m hm
    have h_le_abs : Neg.neg (f.val m) ≤ ℚ₀.absVal (f.val m) := ℚ₀.neg_le_absVal (f.val m)
    exact ℚ₀.le_trans h_pos h_le_abs

theorem mul_ne_zero {x y : ℚ₀} (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 := by
  intro h
  have h1 : x⁻¹ * (x * y) = x⁻¹ * 0 := congrArg (fun z => x⁻¹ * z) h
  rw [ℚ₀.mul_zero] at h1
  rw [← ℚ₀.mul_assoc] at h1
  rw [inv_mul_cancel hx] at h1
  rw [ℚ₀.one_mul] at h1
  exact hy h1

theorem absVal_ne_zero {x : ℚ₀} (hx : x ≠ 0) : ℚ₀.absVal x ≠ 0 := by
  intro h
  exact hx ((ℚ₀.absVal_zero_iff x).mp h)

theorem absVal_one : ℚ₀.absVal 1 = 1 := by
  have h1 : ℚ₀.absVal (1 * 1) = ℚ₀.absVal 1 * ℚ₀.absVal 1 := ℚ₀.absVal_mul 1 1
  rw [ℚ₀.mul_one] at h1
  have h2 : ℚ₀.absVal 1 ≠ 0 := absVal_ne_zero one_ne_zero
  have h3 : (ℚ₀.absVal 1)⁻¹ * ℚ₀.absVal 1 = (ℚ₀.absVal 1)⁻¹ * (ℚ₀.absVal 1 * ℚ₀.absVal 1) := congrArg (fun z => (ℚ₀.absVal 1)⁻¹ * z) h1
  rw [← ℚ₀.mul_assoc] at h3
  rw [inv_mul_cancel h2] at h3
  rw [ℚ₀.one_mul] at h3
  exact h3.symm

theorem absVal_inv (x : ℚ₀) (hx : x ≠ 0) : ℚ₀.absVal (x⁻¹) = (ℚ₀.absVal x)⁻¹ := by
  have h1 : x * x⁻¹ = 1 := mul_inv_cancel hx
  have h2 : ℚ₀.absVal (x * x⁻¹) = ℚ₀.absVal 1 := congrArg ℚ₀.absVal h1
  rw [ℚ₀.absVal_mul] at h2
  rw [absVal_one] at h2
  have hx_abs_ne_zero : ℚ₀.absVal x ≠ 0 := absVal_ne_zero hx
  exact inv_unique hx_abs_ne_zero h2

theorem absVal_inv_sub_inv (x y : ℚ₀) (hx : x ≠ 0) (hy : y ≠ 0) :
    ℚ₀.absVal (x⁻¹ - y⁻¹) = ℚ₀.absVal (y - x) * (ℚ₀.absVal x * ℚ₀.absVal y)⁻¹ := by
  rw [inv_sub_inv_eq x y hx hy]
  rw [ℚ₀.absVal_mul]
  have h_xy_ne_0 : x * y ≠ 0 := mul_ne_zero hx hy
  rw [absVal_inv _ h_xy_ne_0]
  rw [ℚ₀.absVal_mul]

theorem inv_bound_lemma (x y d p Z : ℚ₀) (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : 0 ≤ d) (hp : 0 ≤ p)
    (hZ_pos : 0 ≤ Z) (hZ_nz : Z ≠ 0)
    (h_Z_le : Z ≤ x * y)
    (h_diff : d ≤ p * Z) :
    d * (x * y)⁻¹ ≤ p := by 
  have h_xy_nonneg : 0 ≤ x * y := mul_nonneg hx hy
  have h_xy_nz : x * y ≠ 0 := by
    intro h_eq_0
    rw [h_eq_0] at h_Z_le
    have h_Z_eq_0 : Z = 0 := ℚ₀.le_antisymm h_Z_le hZ_pos
    exact hZ_nz h_Z_eq_0
  have h_xy_inv_nonneg : 0 ≤ (x * y)⁻¹ := inv_nonneg h_xy_nonneg h_xy_nz
  have h_pZ_le_pxy : p * Z ≤ p * (x * y) := mul_le_mul_left_of_nonneg h_Z_le hp
  have h_d_le_pxy : d ≤ p * (x * y) := ℚ₀.le_trans h_diff h_pZ_le_pxy
  have h_mul_inv : d * (x * y)⁻¹ ≤ (p * (x * y)) * (x * y)⁻¹ := mul_le_mul_right_of_nonneg h_d_le_pxy h_xy_inv_nonneg
  have h_assoc : (p * (x * y)) * (x * y)⁻¹ = p * ((x * y) * (x * y)⁻¹) := by rw [ℚ₀.mul_assoc]
  have h_cancel : (x * y) * (x * y)⁻¹ = 1 := mul_inv_cancel h_xy_nz
  rw [h_assoc, h_cancel, ℚ₀.mul_one] at h_mul_inv
  exact h_mul_inv

theorem cauchy_inv_is_cauchy (f : CauchySeq) (h : CauchySeq.ApartZero f) :
    ℚ₀.IsCauchy (fun n => (f.val (Peano.Add.add n (CauchySeq.invBound f h)))⁻¹) := by
  intro n m
  let K := CauchySeq.invBound f h
  let fnK := f.val (Peano.Add.add n K)
  let fmK := f.val (Peano.Add.add m K)
  
  have h_N_le_K : Peano.Order.le₀ (CauchySeq.ApartZero.N f h) K := by
    dsimp [K, CauchySeq.invBound]
    exact Peano.Add.le_self_add (CauchySeq.ApartZero.N f h) (Peano.Add.add (CauchySeq.ApartZero.k f h) (CauchySeq.ApartZero.k f h))
    
  have h_K_le_nK : Peano.Order.le₀ K (Peano.Add.add n K) := 
    Peano.Add.le_self_add_l K n

  have h_N_le_nK : Peano.Order.le₀ (CauchySeq.ApartZero.N f h) (Peano.Add.add n K) := 
    Peano.Order.le_trans (CauchySeq.ApartZero.N f h) K (Peano.Add.add n K) h_N_le_K h_K_le_nK
    
  have h_pow2_le_abs_fnK : ℚ₀.pow2 (CauchySeq.ApartZero.k f h) ≤ ℚ₀.absVal fnK := 
    ApartZero_absVal_bound f h (Peano.Add.add n K) h_N_le_nK

  have hfnK_ne_0 : fnK ≠ 0 := by
    intro h_eq_0
    rw [h_eq_0, absVal_zero] at h_pow2_le_abs_fnK
    have h_pow2_def : ℚ₀.pow2 (CauchySeq.ApartZero.k f h) = ℚ₀.mk (ℤ₀.ofNat (σ 𝟘)) (ℚ₀.pow2_den (CauchySeq.ApartZero.k f h)) := rfl
    have h_zero_def : (0 : ℚ₀) = ℚ₀.mk (ℤ₀.ofNat 𝟘) den1 := rfl
    rw [h_pow2_def, h_zero_def, ℚ₀.mk_le_mk] at h_pow2_le_abs_fnK
    have h_den : ℤ₀.ofNat den1.val = 1 := ℤ₀.ofNat_one
    have hz : ℤ₀.ofNat 𝟘 = 0 := rfl
    rw [h_den, ℤ₀.mul_one, hz, ℤ₀.zero_mul] at h_pow2_le_abs_fnK
    rw [← hz, ℤ₀.le_ofNat_iff] at h_pow2_le_abs_fnK
    exact Peano.Order.le_1_0_then_false h_pow2_le_abs_fnK

  have h_K_le_mK : Peano.Order.le₀ K (Peano.Add.add m K) := 
    Peano.Add.le_self_add_l K m

  have h_N_le_mK : Peano.Order.le₀ (CauchySeq.ApartZero.N f h) (Peano.Add.add m K) := 
    Peano.Order.le_trans (CauchySeq.ApartZero.N f h) K (Peano.Add.add m K) h_N_le_K h_K_le_mK

  have h_pow2_le_abs_fmK : ℚ₀.pow2 (CauchySeq.ApartZero.k f h) ≤ ℚ₀.absVal fmK := 
    ApartZero_absVal_bound f h (Peano.Add.add m K) h_N_le_mK

  have hfmK_ne_0 : fmK ≠ 0 := by
    intro h_eq_0
    rw [h_eq_0, absVal_zero] at h_pow2_le_abs_fmK
    have h_pow2_def : ℚ₀.pow2 (CauchySeq.ApartZero.k f h) = ℚ₀.mk (ℤ₀.ofNat (σ 𝟘)) (ℚ₀.pow2_den (CauchySeq.ApartZero.k f h)) := rfl
    have h_zero_def : (0 : ℚ₀) = ℚ₀.mk (ℤ₀.ofNat 𝟘) den1 := rfl
    rw [h_pow2_def, h_zero_def, ℚ₀.mk_le_mk] at h_pow2_le_abs_fmK
    have h_den : ℤ₀.ofNat den1.val = 1 := ℤ₀.ofNat_one
    have hz : ℤ₀.ofNat 𝟘 = 0 := rfl
    rw [h_den, ℤ₀.mul_one, hz, ℤ₀.zero_mul] at h_pow2_le_abs_fmK
    rw [← hz, ℤ₀.le_ofNat_iff] at h_pow2_le_abs_fmK
    exact Peano.Order.le_1_0_then_false h_pow2_le_abs_fmK

  have h_eq : ℚ₀.absVal (fnK⁻¹ - fmK⁻¹) = Mul.mul (ℚ₀.absVal (fmK - fnK)) (Mul.mul (ℚ₀.absVal fnK) (ℚ₀.absVal fmK))⁻¹ := by
    have h_sub : ℚ₀.absVal (fnK⁻¹ - fmK⁻¹) = ℚ₀.absVal (fmK - fnK) * (ℚ₀.absVal fnK * ℚ₀.absVal fmK)⁻¹ := 
      absVal_inv_sub_inv fnK fmK hfnK_ne_0 hfmK_ne_0
    exact h_sub
    
  have h_f_cauchy := f.property (Peano.Add.add m K) (Peano.Add.add n K)
  
  let x := ℚ₀.absVal fnK
  let y := ℚ₀.absVal fmK
  let d := ℚ₀.absVal (fmK - fnK)
  let p := ℚ₀.pow2 (Peano.Lattice.min n m)
  let k := CauchySeq.ApartZero.k f h
  let Z := ℚ₀.pow2 (Peano.Add.add k k)
  
  have hx : 0 ≤ x := ℚ₀.absVal_nonneg fnK
  have hy : 0 ≤ y := ℚ₀.absVal_nonneg fmK
  have hd : 0 ≤ d := ℚ₀.absVal_nonneg (fmK - fnK)
  have hp : 0 ≤ p := ℚ₀.pow2_nonneg (Peano.Lattice.min n m)
  have hZ_pos : 0 ≤ Z := ℚ₀.pow2_nonneg (Peano.Add.add k k)
  
  have hZ_nz : Z ≠ 0 := by
    intro hz
    have h_k_ne : ℚ₀.pow2 k ≠ 0 := pow2_ne_zero k
    have h_add_pow2 : Z = Mul.mul (ℚ₀.pow2 k) (ℚ₀.pow2 k) := ℚ₀.pow2_add k k
    rw [h_add_pow2] at hz
    exact mul_ne_zero h_k_ne h_k_ne hz

  have h_Z_le : Z ≤ Mul.mul x y := by
    have h_add_pow2 : Z = Mul.mul (ℚ₀.pow2 k) (ℚ₀.pow2 k) := ℚ₀.pow2_add k k
    rw [h_add_pow2]
    exact ℚ₀.mul_le_mul h_pow2_le_abs_fnK h_pow2_le_abs_fmK (ℚ₀.pow2_nonneg k) (ℚ₀.pow2_nonneg k)

  have h_diff : d ≤ Mul.mul p Z := by
    have h_pow2_add : ℚ₀.pow2 (Peano.Add.add (Peano.Lattice.min n m) K) = Mul.mul p (ℚ₀.pow2 K) := ℚ₀.pow2_add _ _
    have h_min_add : Peano.Lattice.min (Peano.Add.add m K) (Peano.Add.add n K) = Peano.Add.add (Peano.Lattice.min m n) K := 
      Peano.Arith.min_add_add_right m n K
    have h_min_comm : Peano.Lattice.min m n = Peano.Lattice.min n m := Peano.Lattice.min_comm m n
    have h_d_le_pow2K : d ≤ ℚ₀.pow2 (Peano.Lattice.min (Peano.Add.add m K) (Peano.Add.add n K)) := h_f_cauchy
    rw [h_min_add, h_min_comm, h_pow2_add] at h_d_le_pow2K
    have h_K_def : K = Peano.Add.add (CauchySeq.ApartZero.N f h) (Peano.Add.add k k) := rfl
    have h_pow2_K : ℚ₀.pow2 K = Mul.mul (ℚ₀.pow2 (CauchySeq.ApartZero.N f h)) Z := by
      rw [h_K_def]
      exact ℚ₀.pow2_add _ _
    have h_pow2_N_le_1 : ℚ₀.pow2 (CauchySeq.ApartZero.N f h) ≤ ℚ₀.ofNat₀ 𝟙 := ℚ₀.pow2_le_one _
    have h_pow2_K_le_Z : ℚ₀.pow2 K ≤ Z := by
      rw [h_pow2_K]
      have h1 : Mul.mul (ℚ₀.pow2 (CauchySeq.ApartZero.N f h)) Z ≤ Mul.mul (ℚ₀.ofNat₀ 𝟙) Z := ℚ₀.mul_le_mul_right_of_nonneg h_pow2_N_le_1 hZ_pos
      have h2 : Mul.mul (ℚ₀.ofNat₀ 𝟙) Z = Z := ℚ₀.one_mul Z
      rw [h2] at h1
      exact h1
    have h_p_pow2_K_le_pZ : Mul.mul p (ℚ₀.pow2 K) ≤ Mul.mul p Z := ℚ₀.mul_le_mul_left_of_nonneg h_pow2_K_le_Z hp
    exact ℚ₀.le_trans h_d_le_pow2K h_p_pow2_K_le_pZ

  have h_bound := inv_bound_lemma x y d p Z hx hy hd hp hZ_pos hZ_nz h_Z_le h_diff
  rw [h_eq]
  exact h_bound

/-- El inverso de una sucesión de Cauchy está definido si la sucesión
está estrictamente alejada de cero (ApartZero f). -/
def CauchySeq.inv (f : CauchySeq) (h : CauchySeq.ApartZero f) : CauchySeq :=
  ⟨fun n => (f.val (Peano.Add.add n (CauchySeq.invBound f h)))⁻¹, cauchy_inv_is_cauchy f h⟩

/-- División de sucesiones de Cauchy. f / g = f * g⁻¹ -/
def CauchySeq.div (f g : CauchySeq) (h : CauchySeq.ApartZero g) : CauchySeq :=
  f * CauchySeq.inv g h

end ℚ₀
