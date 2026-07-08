/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/Incompleteness.lean
-- Demostración de que HFRat es incompleto (existe una sucesión de Cauchy sin límite en HFRat).

import AczelSetTheory.Rationals.HFRatCauchy

namespace ℝ₀

-- ============================================================
-- Sucesión de Bisección para √2
-- ============================================================

/-- Un paso del algoritmo de bisección. Toma un intervalo [a, b] y
devuelve la mitad izquierda o derecha dependiendo de si el punto medio
al cuadrado es mayor o menor que 2. -/
def bisectionStep (ab : HFRat × HFRat) : HFRat × HFRat :=
  let a := ab.1
  let b := ab.2
  -- m = (a + b) / 2
  -- En HFRat la división por 2 se hace multiplicando por 1/2.
  -- Usamos (a+b) * pow2 1
  let m := (a + b) * (HFRat.pow2 (σ 𝟘))
  
  -- if m^2 < 2 then (m, b) else (a, m)
  if m * m < (HFRat.ofNat₀ (σ (σ 𝟘))) then
    (m, b)
  else
    (a, m)

/-- La sucesión de intervalos generada por bisección empezando en [1, 2]. -/
def sqrt2Intervals (n : ℕ₀) : HFRat × HFRat :=
  match n with
  | 𝟘 => (1, HFRat.ofNat₀ (σ (σ 𝟘)))
  | σ k => bisectionStep (sqrt2Intervals k)

/-- La sucesión de Cauchy aproximando √2 por la izquierda. -/
def sqrt2Seq : ℕ₀ → HFRat := fun n => (sqrt2Intervals n).1

/-- La sucesión de bisección converge a ritmo diádico, por lo que es de Cauchy. -/
theorem sqrt2Seq_isCauchy : HFRat.IsCauchy sqrt2Seq := by
  -- El tamaño del intervalo en el paso n es 1/2^n.
  -- La demostración requeriría verificar que b - a = 1/2^n y 
  -- que a_n es creciente y b_n decreciente.
  sorry

/-- La sucesión que aproxima a √2 como elemento de CauchySeq. -/
def sqrt2CauchySeq : HFRat.CauchySeq := ⟨sqrt2Seq, sqrt2Seq_isCauchy⟩

-- ============================================================
-- Irracionalidad y Falta de Límite
-- ============================================================

/-- Demostración (clásica) de la irracionalidad de √2 en HFRat.
No existe ningún q en HFRat tal que q^2 = 2. -/
theorem sqrt2_irrational (q : HFRat) : q * q ≠ HFRat.ofNat₀ (σ (σ 𝟘)) := by
  -- Requiere la factorización única en ℤ₀.
  sorry

/-- La sucesión sqrt2CauchySeq no tiene límite en HFRat.
Esto demuestra la incompletitud métrica de HFRat. -/
theorem sqrt2CauchySeq_has_no_limit :
  ¬ ∃ L : HFRat, ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, le₀ N m → HFRat.absVal (sqrt2Seq m - L) ≤ HFRat.pow2 k := by
  -- Supongamos que existe un límite L ∈ HFRat.
  -- Entonces L^2 = 2 (dado que lim (a_n)^2 = 2).
  -- Por sqrt2_irrational, L^2 ≠ 2. Contradicción.
  sorry

end ℝ₀
