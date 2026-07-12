/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.HFRatOps

open Peano

namespace ℚ₀

def sum (f : ℕ₀ → ℚ₀) : ℕ₀ → ℚ₀
  | 𝟘 => f 𝟘
  | σ k => Add.add (sum f k) (f (σ k))

theorem sum_add (f g : ℕ₀ → ℚ₀) (n : ℕ₀) :
  sum (fun i => Add.add (f i) (g i)) n = Add.add (sum f n) (sum g n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change Add.add (sum (fun i => Add.add (f i) (g i)) k) (Add.add (f (σ k)) (g (σ k))) = Add.add (Add.add (sum f k) (f (σ k))) (Add.add (sum g k) (g (σ k)))
    rw [ih]
    -- Add.add (Add.add (sum f k) (sum g k)) (Add.add (f (σ k)) (g (σ k))) =
    -- Add.add (Add.add (sum f k) (f (σ k))) (Add.add (sum g k) (g (σ k)))
    sorry

theorem sum_mul_left (f : ℕ₀ → ℚ₀) (c : ℚ₀) (n : ℕ₀) :
  sum (fun i => Mul.mul c (f i)) n = Mul.mul c (sum f n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change Add.add (sum (fun i => Mul.mul c (f i)) k) (Mul.mul c (f (σ k))) = Mul.mul c (Add.add (sum f k) (f (σ k)))
    rw [ih]
    -- Add.add (Mul.mul c (sum f k)) (Mul.mul c (f (σ k))) = Mul.mul c (Add.add (sum f k) (f (σ k)))
    sorry

theorem sum_arithmetic (n : ℕ₀) :
  Mul.mul (sum (fun i => ofNat₀ i) n) (ofNat₀ 2) = ofNat₀ (Peano.Mul.mul n (Peano.Add.add n 1)) := by
  sorry

theorem sum_geometric (x : ℚ₀) (n : ℕ₀) :
  Mul.mul (sum (fun i => pow x i) n) (Sub.sub 1 x) = Sub.sub 1 (pow x (Peano.Add.add n 1)) := by
  sorry

end ℚ₀

namespace HFRat

def sum (f : ℕ₀ → HFRat) (n : ℕ₀) : HFRat :=
  { cls  := ℚ₀.sum (fun i => (f i).cls) n
    pair := ℚ₀'.ofQ0 (ℚ₀.sum (fun i => (f i).cls) n)
    hEq  := by rw [ℚ₀'.toQ0_ofQ0] }

theorem cls_sum (f : ℕ₀ → HFRat) (n : ℕ₀) :
  (sum f n).cls = ℚ₀.sum (fun i => (f i).cls) n := rfl

theorem sum_add (f g : ℕ₀ → HFRat) (n : ℕ₀) :
  sum (fun i => Add.add (f i) (g i)) n = Add.add (sum f n) (sum g n) := by
  apply HFRat.ext
  change ℚ₀.sum (fun i => Add.add (f i).cls (g i).cls) n = Add.add (ℚ₀.sum (fun i => (f i).cls) n) (ℚ₀.sum (fun i => (g i).cls) n)
  exact ℚ₀.sum_add (fun i => (f i).cls) (fun i => (g i).cls) n

theorem sum_mul_left (f : ℕ₀ → HFRat) (c : HFRat) (n : ℕ₀) :
  sum (fun i => Mul.mul c (f i)) n = Mul.mul c (sum f n) := by
  apply HFRat.ext
  change ℚ₀.sum (fun i => Mul.mul c.cls (f i).cls) n = Mul.mul c.cls (ℚ₀.sum (fun i => (f i).cls) n)
  exact ℚ₀.sum_mul_left (fun i => (f i).cls) c.cls n

theorem sum_arithmetic (n : ℕ₀) :
  Mul.mul (sum (fun i => ofNat₀ i) n) (ofNat₀ 2) = ofNat₀ (Peano.Mul.mul n (Peano.Add.add n 1)) := by
  apply HFRat.ext
  change Mul.mul (ℚ₀.sum (fun i => (ofNat₀ i).cls) n) (ofNat₀ 2).cls = (ofNat₀ (Peano.Mul.mul n (Peano.Add.add n 1))).cls
  -- Since ofNat₀ n .cls is ℚ₀.ofNat₀ n
  -- we can just exact ℚ₀.sum_arithmetic n
  sorry

theorem sum_geometric (x : HFRat) (n : ℕ₀) :
  Mul.mul (sum (fun i => pow x i) n) (Sub.sub 1 x) = Sub.sub 1 (pow x (Peano.Add.add n 1)) := by
  apply HFRat.ext
  change Mul.mul (ℚ₀.sum (fun i => (pow x i).cls) n) (Sub.sub (1:HFRat).cls x.cls) = Sub.sub (1:HFRat).cls (pow x (Peano.Add.add n 1)).cls
  sorry

end HFRat
