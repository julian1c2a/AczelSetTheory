/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/LinearSpace.lean
-- Espacios vectoriales sobre HFField: estructura, aplicaciones lineales y subespacios.
--
-- Público:
--   HFLinearSpace                   : espacio vectorial sobre HFField
--   HFLinearSpace.toAdditiveHFGroup : grupo aditivo del espacio vectorial
--   HFLinearSpace.zero_smul         : 0F ⊙ v = 0V
--   HFLinearSpace.smul_zero         : k ⊙ 0V = 0V
--   HFLinearSpace.neg_smul          : (-k) ⊙ v = -(k ⊙ v)
--   HFLinearSpace.smul_neg          : k ⊙ (-v) = -(k ⊙ v)
--   HFLinearMap                     : aplicación lineal f : V → W
--   HFLinearMap.hom_zero            : f(0V) = 0W
--   HFLinearMap.hom_neg             : f(-v) = -f(v)
--   HFLinearMap.comp                : composición de aplicaciones lineales
--   HFSubspace                      : subespacio vectorial de HFLinearSpace
--   HFSubspace.toHFLinearSpace      : subespacio como HFLinearSpace
--   HFSubspace.inter                : intersección de subespacios

import AczelSetTheory.Algebra.Field
import AczelSetTheory.Axioms.Intersection

namespace HFAlgebra

-- ─────────────────────────────────────────────────────────────────
-- Estructura principal
-- ─────────────────────────────────────────────────────────────────

/-- Espacio vectorial sobre HFField.
    Un espacio vectorial es un módulo izquierdo sobre un cuerpo.
    Se define independientemente (no como caso especial de HFModule)
    para evitar dependencia de una conversión HFField → HFRing. -/
structure HFLinearSpace (fld : HFField) where
  V     : HFSet
  add   : HFSet → HFSet → HFSet
  zero  : HFSet
  neg   : HFSet → HFSet
  smul  : HFSet → HFSet → HFSet   -- k ⊙ v  (k ∈ fld.F, v ∈ V)
  -- pertenencia
  zero_mem    : zero ∈ V
  add_closed  : ∀ {v w : HFSet}, v ∈ V → w ∈ V → add v w ∈ V
  neg_closed  : ∀ {v : HFSet}, v ∈ V → neg v ∈ V
  smul_closed : ∀ {k v : HFSet}, k ∈ fld.F → v ∈ V → smul k v ∈ V
  -- grupo aditivo abeliano (axiomas izquierdos + comm)
  add_assoc   : ∀ {v w u : HFSet}, v ∈ V → w ∈ V → u ∈ V →
                  add (add v w) u = add v (add w u)
  add_comm    : ∀ {v w : HFSet}, v ∈ V → w ∈ V → add v w = add w v
  zero_add    : ∀ {v : HFSet}, v ∈ V → add zero v = v
  neg_add     : ∀ {v : HFSet}, v ∈ V → add (neg v) v = zero
  -- axiomas de espacio vectorial
  smul_add    : ∀ {k v w : HFSet}, k ∈ fld.F → v ∈ V → w ∈ V →
                  smul k (add v w) = add (smul k v) (smul k w)
  add_smul    : ∀ {k l v : HFSet}, k ∈ fld.F → l ∈ fld.F → v ∈ V →
                  smul (fld.add k l) v = add (smul k v) (smul l v)
  mul_smul    : ∀ {k l v : HFSet}, k ∈ fld.F → l ∈ fld.F → v ∈ V →
                  smul (fld.mul k l) v = smul k (smul l v)
  one_smul    : ∀ {v : HFSet}, v ∈ V → smul fld.one v = v

namespace HFLinearSpace

variable {fld : HFField} (vs : HFLinearSpace fld)

-- ─────────────────────────────────────────────────────────────────
-- Grupo aditivo subyacente
-- ─────────────────────────────────────────────────────────────────

/-- El espacio vectorial `vs` visto como grupo abeliano aditivo. -/
def toAdditiveHFGroup : HFGroup where
  G           := vs.V
  op          := vs.add
  e           := vs.zero
  inv         := vs.neg
  e_mem       := vs.zero_mem
  op_closed   := vs.add_closed
  inv_closed  := vs.neg_closed
  op_assoc    := vs.add_assoc
  op_id_left  := vs.zero_add
  op_inv_left := vs.neg_add

-- ─────────────────────────────────────────────────────────────────
-- Anulaciones
-- ─────────────────────────────────────────────────────────────────

theorem zero_smul {v : HFSet} (hv : v ∈ vs.V) : vs.smul fld.zero v = vs.zero := by
  have hzv : vs.smul fld.zero v ∈ vs.V := vs.smul_closed fld.zero_mem hv
  have hxx : vs.add (vs.smul fld.zero v) (vs.smul fld.zero v) = vs.smul fld.zero v :=
    calc vs.add (vs.smul fld.zero v) (vs.smul fld.zero v)
        = vs.smul (fld.add fld.zero fld.zero) v := (vs.add_smul fld.zero_mem fld.zero_mem hv).symm
      _ = vs.smul fld.zero v                    := by rw [fld.zero_add fld.zero_mem]
  calc vs.smul fld.zero v
      = vs.add vs.zero (vs.smul fld.zero v)               := (vs.zero_add hzv).symm
    _ = vs.add (vs.add (vs.neg (vs.smul fld.zero v)) (vs.smul fld.zero v))
                (vs.smul fld.zero v)                       := by rw [vs.neg_add hzv]
    _ = vs.add (vs.neg (vs.smul fld.zero v))
                (vs.add (vs.smul fld.zero v) (vs.smul fld.zero v)) := by
            rw [vs.add_assoc (vs.neg_closed hzv) hzv hzv]
    _ = vs.add (vs.neg (vs.smul fld.zero v)) (vs.smul fld.zero v) := by rw [hxx]
    _ = vs.zero                                                      := vs.neg_add hzv

theorem smul_zero {k : HFSet} (hk : k ∈ fld.F) : vs.smul k vs.zero = vs.zero := by
  have hkz : vs.smul k vs.zero ∈ vs.V := vs.smul_closed hk vs.zero_mem
  have hxx : vs.add (vs.smul k vs.zero) (vs.smul k vs.zero) = vs.smul k vs.zero :=
    calc vs.add (vs.smul k vs.zero) (vs.smul k vs.zero)
        = vs.smul k (vs.add vs.zero vs.zero) := (vs.smul_add hk vs.zero_mem vs.zero_mem).symm
      _ = vs.smul k vs.zero                  := by rw [vs.zero_add vs.zero_mem]
  calc vs.smul k vs.zero
      = vs.add vs.zero (vs.smul k vs.zero)               := (vs.zero_add hkz).symm
    _ = vs.add (vs.add (vs.neg (vs.smul k vs.zero)) (vs.smul k vs.zero))
                (vs.smul k vs.zero)                       := by rw [vs.neg_add hkz]
    _ = vs.add (vs.neg (vs.smul k vs.zero))
                (vs.add (vs.smul k vs.zero) (vs.smul k vs.zero)) := by
            rw [vs.add_assoc (vs.neg_closed hkz) hkz hkz]
    _ = vs.add (vs.neg (vs.smul k vs.zero)) (vs.smul k vs.zero) := by rw [hxx]
    _ = vs.zero                                                   := vs.neg_add hkz

-- ─────────────────────────────────────────────────────────────────
-- Negativos
-- ─────────────────────────────────────────────────────────────────

theorem neg_smul {k v : HFSet} (hk : k ∈ fld.F) (hv : v ∈ vs.V) :
    vs.smul (fld.neg k) v = vs.neg (vs.smul k v) := by
  have hkv  : vs.smul k v ∈ vs.V          := vs.smul_closed hk hv
  have hnkv : vs.smul (fld.neg k) v ∈ vs.V := vs.smul_closed (fld.neg_closed hk) hv
  have hkey : vs.add (vs.smul (fld.neg k) v) (vs.smul k v) = vs.zero :=
    calc vs.add (vs.smul (fld.neg k) v) (vs.smul k v)
        = vs.smul (fld.add (fld.neg k) k) v := (vs.add_smul (fld.neg_closed hk) hk hv).symm
      _ = vs.smul fld.zero v               := by rw [fld.neg_add hk]
      _ = vs.zero                          := vs.zero_smul hv
  exact vs.toAdditiveHFGroup.unique_inv hkv hnkv hkey

theorem smul_neg {k v : HFSet} (hk : k ∈ fld.F) (hv : v ∈ vs.V) :
    vs.smul k (vs.neg v) = vs.neg (vs.smul k v) := by
  have hkv  : vs.smul k v ∈ vs.V          := vs.smul_closed hk hv
  have hknv : vs.smul k (vs.neg v) ∈ vs.V := vs.smul_closed hk (vs.neg_closed hv)
  have hkey : vs.add (vs.smul k (vs.neg v)) (vs.smul k v) = vs.zero :=
    calc vs.add (vs.smul k (vs.neg v)) (vs.smul k v)
        = vs.smul k (vs.add (vs.neg v) v) := (vs.smul_add hk (vs.neg_closed hv) hv).symm
      _ = vs.smul k vs.zero              := by rw [vs.neg_add hv]
      _ = vs.zero                        := vs.smul_zero hk
  exact vs.toAdditiveHFGroup.unique_inv hkv hknv hkey

end HFLinearSpace

-- ─────────────────────────────────────────────────────────────────
-- Aplicación lineal
-- ─────────────────────────────────────────────────────────────────

/-- Aplicación lineal entre HFLinearSpace sobre el mismo HFField.
    Preserva la suma y la multiplicación escalar. -/
structure HFLinearMap (fld : HFField) (V W : HFLinearSpace fld) where
  f      : HFSet → HFSet
  f_mem  : ∀ {v : HFSet}, v ∈ V.V → f v ∈ W.V
  f_add  : ∀ {v w : HFSet}, v ∈ V.V → w ∈ V.V →
             f (V.add v w) = W.add (f v) (f w)
  f_smul : ∀ {k v : HFSet}, k ∈ fld.F → v ∈ V.V →
             f (V.smul k v) = W.smul k (f v)

namespace HFLinearMap

variable {fld : HFField} {V W U : HFLinearSpace fld} (φ : HFLinearMap fld V W)

-- ─────────────────────────────────────────────────────────────────
-- f(0V) = 0W,  f(-v) = -f(v)
-- ─────────────────────────────────────────────────────────────────

theorem hom_zero : φ.f V.zero = W.zero := by
  have hfz : φ.f V.zero ∈ W.V := φ.f_mem V.zero_mem
  apply W.toAdditiveHFGroup.left_cancel hfz hfz W.zero_mem
  show W.add (φ.f V.zero) (φ.f V.zero) = W.add (φ.f V.zero) W.zero
  calc W.add (φ.f V.zero) (φ.f V.zero)
      = φ.f (V.add V.zero V.zero) := (φ.f_add V.zero_mem V.zero_mem).symm
    _ = φ.f V.zero                := by rw [V.zero_add V.zero_mem]
    _ = W.add (φ.f V.zero) W.zero := (W.toAdditiveHFGroup.op_id_right hfz).symm

theorem hom_neg {v : HFSet} (hv : v ∈ V.V) : φ.f (V.neg v) = W.neg (φ.f v) := by
  have hfv  : φ.f v ∈ W.V         := φ.f_mem hv
  have hfnv : φ.f (V.neg v) ∈ W.V := φ.f_mem (V.neg_closed hv)
  have hkey : W.add (φ.f (V.neg v)) (φ.f v) = W.zero :=
    calc W.add (φ.f (V.neg v)) (φ.f v)
        = φ.f (V.add (V.neg v) v) := (φ.f_add (V.neg_closed hv) hv).symm
      _ = φ.f V.zero              := by rw [V.neg_add hv]
      _ = W.zero                  := φ.hom_zero
  exact W.toAdditiveHFGroup.unique_inv hfv hfnv hkey

-- ─────────────────────────────────────────────────────────────────
-- Identidad y composición
-- ─────────────────────────────────────────────────────────────────

/-- La identidad es una aplicación lineal. -/
def id (V : HFLinearSpace fld) : HFLinearMap fld V V where
  f      := fun v => v
  f_mem  := fun hv => hv
  f_add  := fun _ _ => rfl
  f_smul := fun _ _ => rfl

/-- Composición de aplicaciones lineales. -/
def comp (ψ : HFLinearMap fld W U) (φ : HFLinearMap fld V W) : HFLinearMap fld V U where
  f      := fun v => ψ.f (φ.f v)
  f_mem  := fun hv => ψ.f_mem (φ.f_mem hv)
  f_add  := fun hv hw => by rw [φ.f_add hv hw, ψ.f_add (φ.f_mem hv) (φ.f_mem hw)]
  f_smul := fun hk hv => by rw [φ.f_smul hk hv, ψ.f_smul hk (φ.f_mem hv)]

end HFLinearMap

-- ─────────────────────────────────────────────────────────────────
-- Subespacio
-- ─────────────────────────────────────────────────────────────────

/-- Subespacio vectorial de un HFLinearSpace.
    Cerrado bajo suma y multiplicación escalar (la clausura bajo neg
    se incluye explícitamente como axioma para simplicidad del esqueleto;
    es derivable de smul_closed con escalar neg fld.one). -/
structure HFSubspace (fld : HFField) (vs : HFLinearSpace fld) where
  W           : HFSet
  W_sub       : ∀ {v : HFSet}, v ∈ W → v ∈ vs.V
  zero_mem    : vs.zero ∈ W
  add_closed  : ∀ {v w : HFSet}, v ∈ W → w ∈ W → vs.add v w ∈ W
  neg_closed  : ∀ {v : HFSet}, v ∈ W → vs.neg v ∈ W
  smul_closed : ∀ {k v : HFSet}, k ∈ fld.F → v ∈ W → vs.smul k v ∈ W

namespace HFSubspace

variable {fld : HFField} {vs : HFLinearSpace fld}

/-- Todo subespacio es un espacio vectorial, heredando las operaciones del ambiente. -/
def toHFLinearSpace (sub : HFSubspace fld vs) : HFLinearSpace fld where
  V           := sub.W
  add         := vs.add
  zero        := vs.zero
  neg         := vs.neg
  smul        := vs.smul
  zero_mem    := sub.zero_mem
  add_closed  := sub.add_closed
  neg_closed  := sub.neg_closed
  smul_closed := sub.smul_closed
  add_assoc   := fun hv hw hu =>
    vs.add_assoc (sub.W_sub hv) (sub.W_sub hw) (sub.W_sub hu)
  add_comm    := fun hv hw =>
    vs.add_comm (sub.W_sub hv) (sub.W_sub hw)
  zero_add    := fun hv => vs.zero_add (sub.W_sub hv)
  neg_add     := fun hv => vs.neg_add (sub.W_sub hv)
  smul_add    := fun hk hv hw =>
    vs.smul_add hk (sub.W_sub hv) (sub.W_sub hw)
  add_smul    := fun hk hl hv =>
    vs.add_smul hk hl (sub.W_sub hv)
  mul_smul    := fun hk hl hv =>
    vs.mul_smul hk hl (sub.W_sub hv)
  one_smul    := fun hv => vs.one_smul (sub.W_sub hv)

/-- La intersección de dos subespacios del mismo espacio vectorial es un subespacio. -/
def inter (sub₁ sub₂ : HFSubspace fld vs) : HFSubspace fld vs where
  W           := HFSet.inter sub₁.W sub₂.W
  W_sub       := fun hv => by rw [HFSet.mem_inter] at hv; exact sub₁.W_sub hv.1
  zero_mem    := by rw [HFSet.mem_inter]; exact ⟨sub₁.zero_mem, sub₂.zero_mem⟩
  add_closed  := fun hv hw => by
    rw [HFSet.mem_inter] at hv hw ⊢
    exact ⟨sub₁.add_closed hv.1 hw.1, sub₂.add_closed hv.2 hw.2⟩
  neg_closed  := fun hv => by
    rw [HFSet.mem_inter] at hv ⊢
    exact ⟨sub₁.neg_closed hv.1, sub₂.neg_closed hv.2⟩
  smul_closed := fun hk hv => by
    rw [HFSet.mem_inter] at hv ⊢
    exact ⟨sub₁.smul_closed hk hv.1, sub₂.smul_closed hk hv.2⟩

end HFSubspace

end HFAlgebra
