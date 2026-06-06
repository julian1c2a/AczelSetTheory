/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/QuotientRing.lean
-- Anillo cociente R/I para un ideal bilátero I de un HFRing.
--
-- Diseño:
--   • La estructura ADITIVA se hereda íntegra del grupo cociente
--     `quotientGroup R.toAdditiveHFGroup I.toAddSubgroup hn` (todo ideal es
--     normal en el grupo aditivo, que es abeliano).
--   • Sólo se define la MULTIPLICACIÓN sobre cosets y se prueba su
--     buena-definición vía absorción del ideal:
--         (g'·h') − (g·h) = g'·(h'−h) + (g'−g)·h ∈ I.
--
-- Público:
--   HFIdeal                       : ideal bilátero de un HFRing
--   HFIdeal.toAddSubgroup         : el ideal como subgrupo aditivo
--   HFIdeal.toAddSubgroup_isNormal: todo ideal es normal (grupo abeliano)
--   HFIdeal.quotientMul           : multiplicación sobre cosets
--   HFIdeal.quotientMul_cosetOf   : cosetOf es morfismo multiplicativo
--   HFIdeal.quotientAdd_cosetOf   : cosetOf es morfismo aditivo
--   HFRing.quotient R I           : el anillo cociente R/I

import AczelSetTheory.Algebra.Ring
import AczelSetTheory.Algebra.QuotientGroup

namespace HFAlgebra

variable {rng : HFRing}

-- ─────────────────────────────────────────────────────────────────
-- §0. Lema telescópico en el grupo aditivo de un anillo
-- ─────────────────────────────────────────────────────────────────

/-- `(A − B) + (B − C) = A − C` en el grupo aditivo del anillo. -/
private theorem add_telescope (rng : HFRing) {A B C : HFSet}
    (hA : A ∈ rng.R) (hB : B ∈ rng.R) (hC : C ∈ rng.R) :
    rng.add (rng.add A (rng.neg B)) (rng.add B (rng.neg C)) = rng.add A (rng.neg C) := by
  have hnB := rng.neg_closed hB
  have hnC := rng.neg_closed hC
  calc rng.add (rng.add A (rng.neg B)) (rng.add B (rng.neg C))
      = rng.add A (rng.add (rng.neg B) (rng.add B (rng.neg C))) :=
          rng.add_assoc hA hnB (rng.add_closed hB hnC)
    _ = rng.add A (rng.add (rng.add (rng.neg B) B) (rng.neg C)) := by
          rw [rng.add_assoc hnB hB hnC]
    _ = rng.add A (rng.add rng.zero (rng.neg C)) := by rw [rng.neg_add hB]
    _ = rng.add A (rng.neg C) := by rw [rng.zero_add hnC]

-- ─────────────────────────────────────────────────────────────────
-- §1. Ideal bilátero
-- ─────────────────────────────────────────────────────────────────

/-- Ideal bilátero de un `HFRing`: subgrupo aditivo cerrado por absorción
    multiplicativa a izquierda y derecha. -/
structure HFIdeal (rng : HFRing) where
  I            : HFSet
  I_sub        : ∀ {x : HFSet}, x ∈ I → x ∈ rng.R
  zero_mem     : rng.zero ∈ I
  add_closed   : ∀ {a b : HFSet}, a ∈ I → b ∈ I → rng.add a b ∈ I
  neg_closed   : ∀ {a : HFSet}, a ∈ I → rng.neg a ∈ I
  absorb_left  : ∀ {r a : HFSet}, r ∈ rng.R → a ∈ I → rng.mul r a ∈ I
  absorb_right : ∀ {r a : HFSet}, r ∈ rng.R → a ∈ I → rng.mul a r ∈ I

namespace HFIdeal

-- ─────────────────────────────────────────────────────────────────
-- §2. El ideal como subgrupo aditivo normal
-- ─────────────────────────────────────────────────────────────────

/-- El ideal `I` visto como subgrupo del grupo aditivo de `rng`. -/
def toAddSubgroup (J : HFIdeal rng) : HFSubgroup rng.toAdditiveHFGroup where
  H          := J.I
  H_sub      := J.I_sub
  e_mem      := J.zero_mem
  op_closed  := J.add_closed
  inv_closed := J.neg_closed

/-- Todo ideal es normal en el grupo aditivo (abeliano): `g + n − g = n ∈ I`. -/
theorem toAddSubgroup_isNormal (J : HFIdeal rng) : J.toAddSubgroup.isNormal := by
  intro g n hg hn
  have hgR : g ∈ rng.R := hg
  have hnR : n ∈ rng.R := J.I_sub hn
  show rng.add (rng.add g n) (rng.neg g) ∈ J.I
  have heq : rng.add (rng.add g n) (rng.neg g) = n := by
    calc rng.add (rng.add g n) (rng.neg g)
        = rng.add (rng.add n g) (rng.neg g) := by rw [rng.add_comm hgR hnR]
      _ = rng.add n (rng.add g (rng.neg g)) := rng.add_assoc hnR hgR (rng.neg_closed hgR)
      _ = rng.add n rng.zero := by rw [rng.add_neg hgR]
      _ = n := rng.add_zero hnR
  rw [heq]; exact hn

/-- El grupo aditivo cociente `R/I`. -/
abbrev addQuot (J : HFIdeal rng) : HFGroup :=
  quotientGroup rng.toAdditiveHFGroup J.toAddSubgroup J.toAddSubgroup_isNormal

-- ─────────────────────────────────────────────────────────────────
-- §3. Multiplicación sobre cosets y buena-definición
-- ─────────────────────────────────────────────────────────────────

/-- Multiplicación cociente: `C₁·C₂ := I·(rep C₁ · rep C₂)`. -/
abbrev quotientMul (J : HFIdeal rng) (C₁ C₂ : HFSet) : HFSet :=
  J.toAddSubgroup.rightCoset
    (rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₂))

/-- Buena-definición de la multiplicación: si `Ig = Ig'` y `Ih = Ih'`,
    entonces `I(g·h) = I(g'·h')`, usando la absorción del ideal. -/
theorem mul_welldefined (J : HFIdeal rng) {g g' h h' : HFSet}
    (hg : g ∈ rng.R) (hg' : g' ∈ rng.R) (hh : h ∈ rng.R) (hh' : h' ∈ rng.R)
    (hgg' : J.toAddSubgroup.rightCoset g = J.toAddSubgroup.rightCoset g')
    (hhh' : J.toAddSubgroup.rightCoset h = J.toAddSubgroup.rightCoset h') :
    J.toAddSubgroup.rightCoset (rng.mul g h)
      = J.toAddSubgroup.rightCoset (rng.mul g' h') := by
  have diff_g : rng.add g' (rng.neg g) ∈ J.I := by
    have := (J.toAddSubgroup.cosetEq_iff_rightCoset_eq hg hg').mpr hgg'
    exact this
  have diff_h : rng.add h' (rng.neg h) ∈ J.I := by
    have := (J.toAddSubgroup.cosetEq_iff_rightCoset_eq hh hh').mpr hhh'
    exact this
  have mem_term :
      rng.add (rng.mul g' (rng.add h' (rng.neg h)))
              (rng.mul (rng.add g' (rng.neg g)) h) ∈ J.I :=
    J.add_closed (J.absorb_left hg' diff_h) (J.absorb_right hh diff_g)
  have eqid :
      rng.add (rng.mul g' h') (rng.neg (rng.mul g h))
        = rng.add (rng.mul g' (rng.add h' (rng.neg h)))
                  (rng.mul (rng.add g' (rng.neg g)) h) := by
    rw [rng.left_distrib hg' hh' (rng.neg_closed hh), rng.mul_neg hg' hh,
        rng.right_distrib hg' (rng.neg_closed hg) hh, rng.neg_mul hg hh]
    exact (add_telescope rng (rng.mul_closed hg' hh')
            (rng.mul_closed hg' hh) (rng.mul_closed hg hh)).symm
  apply (J.toAddSubgroup.cosetEq_iff_rightCoset_eq
            (rng.mul_closed hg hh) (rng.mul_closed hg' hh')).mp
  show rng.add (rng.mul g' h') (rng.neg (rng.mul g h)) ∈ J.I
  rw [eqid]; exact mem_term

/-- `cosetOf` es morfismo multiplicativo: `I(g)·I(h) = I(g·h)`. -/
theorem quotientMul_cosetOf (J : HFIdeal rng) {g h : HFSet}
    (hg : g ∈ rng.R) (hh : h ∈ rng.R) :
    J.quotientMul (J.toAddSubgroup.cosetOf g) (J.toAddSubgroup.cosetOf h)
      = J.toAddSubgroup.cosetOf (rng.mul g h) := by
  apply J.mul_welldefined
    (J.toAddSubgroup.cosetRep_mem_G (J.toAddSubgroup.cosetOf_mem_cosets hg))
    hg
    (J.toAddSubgroup.cosetRep_mem_G (J.toAddSubgroup.cosetOf_mem_cosets hh))
    hh
  · exact J.toAddSubgroup.cosetRep_rightCoset_eq (J.toAddSubgroup.cosetOf_mem_cosets hg)
  · exact J.toAddSubgroup.cosetRep_rightCoset_eq (J.toAddSubgroup.cosetOf_mem_cosets hh)

/-- `cosetOf` es morfismo aditivo: `I(g)+I(h) = I(g+h)`
    (envoltura de `quotientOp_cosetOf` en términos de `rng.add`). -/
theorem quotientAdd_cosetOf (J : HFIdeal rng) {g h : HFSet}
    (hg : g ∈ rng.R) (hh : h ∈ rng.R) :
    J.toAddSubgroup.quotientOp (J.toAddSubgroup.cosetOf g) (J.toAddSubgroup.cosetOf h)
      = J.toAddSubgroup.cosetOf (rng.add g h) :=
  J.toAddSubgroup.quotientOp_cosetOf J.toAddSubgroup_isNormal hg hh

end HFIdeal

-- ─────────────────────────────────────────────────────────────────
-- §4. El anillo cociente
-- ─────────────────────────────────────────────────────────────────

/-- El anillo cociente `R/I` para un ideal bilátero `I`.
    La estructura aditiva se hereda del grupo cociente; sólo se añade la
    multiplicación y sus axiomas. -/
def HFRing.quotient (rng : HFRing) (J : HFIdeal rng) : HFRing where
  R   := J.toAddSubgroup.cosets
  add := J.toAddSubgroup.quotientOp
  mul := J.quotientMul
  zero := J.toAddSubgroup.quotientId
  one  := J.toAddSubgroup.cosetOf rng.one
  neg  := J.toAddSubgroup.quotientInv
  -- pertenencias y axiomas aditivos: heredados del grupo cociente
  zero_mem   := J.addQuot.e_mem
  add_closed := J.addQuot.op_closed
  neg_closed := J.addQuot.inv_closed
  add_assoc  := J.addQuot.op_assoc
  zero_add   := J.addQuot.op_id_left
  neg_add    := J.addQuot.op_inv_left
  add_comm := by
    intro C₁ C₂ h₁ h₂
    have hr₁ := J.toAddSubgroup.cosetRep_mem_G h₁
    have hr₂ := J.toAddSubgroup.cosetRep_mem_G h₂
    show J.toAddSubgroup.rightCoset
            (rng.add (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₂))
       = J.toAddSubgroup.rightCoset
            (rng.add (J.toAddSubgroup.cosetRep C₂) (J.toAddSubgroup.cosetRep C₁))
    rw [rng.add_comm hr₁ hr₂]
  one_mem := J.toAddSubgroup.cosetOf_mem_cosets rng.one_mem
  -- multiplicación: cerradura
  mul_closed := by
    intro C₁ C₂ h₁ h₂
    show J.quotientMul C₁ C₂ ∈ J.toAddSubgroup.cosets
    rw [HFSubgroup.mem_cosets]
    exact ⟨rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₂),
           rng.mul_closed (J.toAddSubgroup.cosetRep_mem_G h₁)
                          (J.toAddSubgroup.cosetRep_mem_G h₂), rfl⟩
  -- asociatividad multiplicativa
  mul_assoc := by
    intro C₁ C₂ C₃ h₁ h₂ h₃
    have hr₁ := J.toAddSubgroup.cosetRep_mem_G h₁
    have hr₂ := J.toAddSubgroup.cosetRep_mem_G h₂
    have hr₃ := J.toAddSubgroup.cosetRep_mem_G h₃
    have e₁ : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁) = C₁ :=
      J.toAddSubgroup.cosetRep_rightCoset_eq h₁
    have e₂ : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₂) = C₂ :=
      J.toAddSubgroup.cosetRep_rightCoset_eq h₂
    have e₃ : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃) = C₃ :=
      J.toAddSubgroup.cosetRep_rightCoset_eq h₃
    show J.quotientMul (J.quotientMul C₁ C₂) C₃
       = J.quotientMul C₁ (J.quotientMul C₂ C₃)
    calc J.quotientMul (J.quotientMul C₁ C₂) C₃
        = J.quotientMul (J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₁))
                                        (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₂)))
                         (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₃)) := by
              show J.quotientMul (J.quotientMul C₁ C₂) C₃
                 = J.quotientMul (J.quotientMul (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁))
                                                 (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₂)))
                                  (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃))
              rw [e₁, e₂, e₃]
      _ = J.quotientMul (J.toAddSubgroup.cosetOf
                          (rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₂)))
                         (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₃)) := by
              rw [J.quotientMul_cosetOf hr₁ hr₂]
      _ = J.toAddSubgroup.cosetOf
            (rng.mul (rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₂))
                     (J.toAddSubgroup.cosetRep C₃)) :=
              J.quotientMul_cosetOf (rng.mul_closed hr₁ hr₂) hr₃
      _ = J.toAddSubgroup.cosetOf
            (rng.mul (J.toAddSubgroup.cosetRep C₁)
                     (rng.mul (J.toAddSubgroup.cosetRep C₂) (J.toAddSubgroup.cosetRep C₃))) := by
              rw [rng.mul_assoc hr₁ hr₂ hr₃]
      _ = J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₁))
                         (J.toAddSubgroup.cosetOf
                            (rng.mul (J.toAddSubgroup.cosetRep C₂) (J.toAddSubgroup.cosetRep C₃))) :=
              (J.quotientMul_cosetOf hr₁ (rng.mul_closed hr₂ hr₃)).symm
      _ = J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₁))
                         (J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₂))
                                         (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₃))) := by
              rw [J.quotientMul_cosetOf hr₂ hr₃]
      _ = J.quotientMul C₁ (J.quotientMul C₂ C₃) := by
              show J.quotientMul (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁))
                     (J.quotientMul (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₂))
                                     (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃))) = _
              rw [e₁, e₂, e₃]
  -- elemento neutro multiplicativo derecho
  mul_one := by
    intro C hC
    have hr := J.toAddSubgroup.cosetRep_mem_G hC
    have er : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C) = C :=
      J.toAddSubgroup.cosetRep_rightCoset_eq hC
    show J.quotientMul C (J.toAddSubgroup.cosetOf rng.one) = C
    calc J.quotientMul C (J.toAddSubgroup.cosetOf rng.one)
        = J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C))
                         (J.toAddSubgroup.cosetOf rng.one) := by
              show J.quotientMul C (J.toAddSubgroup.cosetOf rng.one)
                 = J.quotientMul (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C))
                                  (J.toAddSubgroup.cosetOf rng.one)
              rw [er]
      _ = J.toAddSubgroup.cosetOf (rng.mul (J.toAddSubgroup.cosetRep C) rng.one) :=
              J.quotientMul_cosetOf hr rng.one_mem
      _ = J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C) := by rw [rng.mul_one hr]
      _ = C := er
  -- elemento neutro multiplicativo izquierdo
  one_mul := by
    intro C hC
    have hr := J.toAddSubgroup.cosetRep_mem_G hC
    have er : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C) = C :=
      J.toAddSubgroup.cosetRep_rightCoset_eq hC
    show J.quotientMul (J.toAddSubgroup.cosetOf rng.one) C = C
    calc J.quotientMul (J.toAddSubgroup.cosetOf rng.one) C
        = J.quotientMul (J.toAddSubgroup.cosetOf rng.one)
                         (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C)) := by
              show J.quotientMul (J.toAddSubgroup.cosetOf rng.one) C
                 = J.quotientMul (J.toAddSubgroup.cosetOf rng.one)
                                  (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C))
              rw [er]
      _ = J.toAddSubgroup.cosetOf (rng.mul rng.one (J.toAddSubgroup.cosetRep C)) :=
              J.quotientMul_cosetOf rng.one_mem hr
      _ = J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C) := by rw [rng.one_mul hr]
      _ = C := er
  -- distributividad izquierda
  left_distrib := by
    intro C₁ C₂ C₃ h₁ h₂ h₃
    have hr₁ := J.toAddSubgroup.cosetRep_mem_G h₁
    have hr₂ := J.toAddSubgroup.cosetRep_mem_G h₂
    have hr₃ := J.toAddSubgroup.cosetRep_mem_G h₃
    have e₁ : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁) = C₁ :=
      J.toAddSubgroup.cosetRep_rightCoset_eq h₁
    have e₂ : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₂) = C₂ :=
      J.toAddSubgroup.cosetRep_rightCoset_eq h₂
    have e₃ : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃) = C₃ :=
      J.toAddSubgroup.cosetRep_rightCoset_eq h₃
    show J.quotientMul C₁ (J.toAddSubgroup.quotientOp C₂ C₃)
       = J.toAddSubgroup.quotientOp (J.quotientMul C₁ C₂) (J.quotientMul C₁ C₃)
    calc J.quotientMul C₁ (J.toAddSubgroup.quotientOp C₂ C₃)
        = J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₁))
              (J.toAddSubgroup.quotientOp
                  (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₂))
                  (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₃))) := by
              show J.quotientMul C₁ (J.toAddSubgroup.quotientOp C₂ C₃)
                 = J.quotientMul (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁))
                     (J.toAddSubgroup.quotientOp
                         (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₂))
                         (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃)))
              rw [e₁, e₂, e₃]
      _ = J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₁))
              (J.toAddSubgroup.cosetOf
                  (rng.add (J.toAddSubgroup.cosetRep C₂) (J.toAddSubgroup.cosetRep C₃))) := by
              rw [J.quotientAdd_cosetOf hr₂ hr₃]
      _ = J.toAddSubgroup.cosetOf
            (rng.mul (J.toAddSubgroup.cosetRep C₁)
                     (rng.add (J.toAddSubgroup.cosetRep C₂) (J.toAddSubgroup.cosetRep C₃))) :=
              J.quotientMul_cosetOf hr₁ (rng.add_closed hr₂ hr₃)
      _ = J.toAddSubgroup.cosetOf
            (rng.add (rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₂))
                     (rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₃))) := by
              rw [rng.left_distrib hr₁ hr₂ hr₃]
      _ = J.toAddSubgroup.quotientOp
            (J.toAddSubgroup.cosetOf
                (rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₂)))
            (J.toAddSubgroup.cosetOf
                (rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₃))) :=
              (J.quotientAdd_cosetOf (rng.mul_closed hr₁ hr₂) (rng.mul_closed hr₁ hr₃)).symm
      _ = J.toAddSubgroup.quotientOp
            (J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₁))
                            (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₂)))
            (J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₁))
                            (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₃))) := by
              rw [J.quotientMul_cosetOf hr₁ hr₂, J.quotientMul_cosetOf hr₁ hr₃]
      _ = J.toAddSubgroup.quotientOp (J.quotientMul C₁ C₂) (J.quotientMul C₁ C₃) := by
              show J.toAddSubgroup.quotientOp
                     (J.quotientMul (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁))
                                     (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₂)))
                     (J.quotientMul (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁))
                                     (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃))) = _
              rw [e₁, e₂, e₃]
  -- distributividad derecha
  right_distrib := by
    intro C₁ C₂ C₃ h₁ h₂ h₃
    have hr₁ := J.toAddSubgroup.cosetRep_mem_G h₁
    have hr₂ := J.toAddSubgroup.cosetRep_mem_G h₂
    have hr₃ := J.toAddSubgroup.cosetRep_mem_G h₃
    have e₁ : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁) = C₁ :=
      J.toAddSubgroup.cosetRep_rightCoset_eq h₁
    have e₂ : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₂) = C₂ :=
      J.toAddSubgroup.cosetRep_rightCoset_eq h₂
    have e₃ : J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃) = C₃ :=
      J.toAddSubgroup.cosetRep_rightCoset_eq h₃
    show J.quotientMul (J.toAddSubgroup.quotientOp C₁ C₂) C₃
       = J.toAddSubgroup.quotientOp (J.quotientMul C₁ C₃) (J.quotientMul C₂ C₃)
    calc J.quotientMul (J.toAddSubgroup.quotientOp C₁ C₂) C₃
        = J.quotientMul
              (J.toAddSubgroup.quotientOp
                  (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₁))
                  (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₂)))
              (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₃)) := by
              show J.quotientMul (J.toAddSubgroup.quotientOp C₁ C₂) C₃
                 = J.quotientMul
                     (J.toAddSubgroup.quotientOp
                         (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁))
                         (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₂)))
                     (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃))
              rw [e₁, e₂, e₃]
      _ = J.quotientMul
              (J.toAddSubgroup.cosetOf
                  (rng.add (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₂)))
              (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₃)) := by
              rw [J.quotientAdd_cosetOf hr₁ hr₂]
      _ = J.toAddSubgroup.cosetOf
            (rng.mul (rng.add (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₂))
                     (J.toAddSubgroup.cosetRep C₃)) :=
              J.quotientMul_cosetOf (rng.add_closed hr₁ hr₂) hr₃
      _ = J.toAddSubgroup.cosetOf
            (rng.add (rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₃))
                     (rng.mul (J.toAddSubgroup.cosetRep C₂) (J.toAddSubgroup.cosetRep C₃))) := by
              rw [rng.right_distrib hr₁ hr₂ hr₃]
      _ = J.toAddSubgroup.quotientOp
            (J.toAddSubgroup.cosetOf
                (rng.mul (J.toAddSubgroup.cosetRep C₁) (J.toAddSubgroup.cosetRep C₃)))
            (J.toAddSubgroup.cosetOf
                (rng.mul (J.toAddSubgroup.cosetRep C₂) (J.toAddSubgroup.cosetRep C₃))) :=
              (J.quotientAdd_cosetOf (rng.mul_closed hr₁ hr₃) (rng.mul_closed hr₂ hr₃)).symm
      _ = J.toAddSubgroup.quotientOp
            (J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₁))
                            (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₃)))
            (J.quotientMul (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₂))
                            (J.toAddSubgroup.cosetOf (J.toAddSubgroup.cosetRep C₃))) := by
              rw [J.quotientMul_cosetOf hr₁ hr₃, J.quotientMul_cosetOf hr₂ hr₃]
      _ = J.toAddSubgroup.quotientOp (J.quotientMul C₁ C₃) (J.quotientMul C₂ C₃) := by
              show J.toAddSubgroup.quotientOp
                     (J.quotientMul (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₁))
                                     (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃)))
                     (J.quotientMul (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₂))
                                     (J.toAddSubgroup.rightCoset (J.toAddSubgroup.cosetRep C₃))) = _
              rw [e₁, e₂, e₃]

end HFAlgebra
