/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Module.lean
-- Módulos izquierdos sobre HFRing: estructura, homomorfismos y submódulos.
--
-- Público:
--   HFModule                   : módulo izquierdo sobre HFRing
--   HFModule.toAdditiveHFGroup : grupo aditivo del módulo
--   HFModule.zero_smul         : 0R ⊙ m = 0M
--   HFModule.smul_zero         : r ⊙ 0M = 0M
--   HFModule.neg_smul          : (-r) ⊙ m = -(r ⊙ m)
--   HFModule.smul_neg          : r ⊙ (-m) = -(r ⊙ m)
--   HFModuleHom                : homomorfismo de módulos (R-lineal) f : M → N
--   HFModuleHom.hom_zero       : f(0M) = 0N
--   HFModuleHom.hom_neg        : f(-m) = -f(m)
--   HFModuleHom.comp           : composición de homomorfismos
--   HFSubmodule                : submódulo de HFModule
--   HFSubmodule.toHFModule     : submódulo como HFModule
--   HFSubmodule.inter          : intersección de submódulos

import AczelSetTheory.Algebra.Ring
import AczelSetTheory.Axioms.Intersection

namespace HFAlgebra

-- ─────────────────────────────────────────────────────────────────
-- Estructura principal
-- ─────────────────────────────────────────────────────────────────

/-- Módulo izquierdo sobre HFRing.
    `smul r m` denota la multiplicación escalar `r ⊙ m`. -/
structure HFModule (rng : HFRing) where
  M    : HFSet
  add  : HFSet → HFSet → HFSet
  zero : HFSet
  neg  : HFSet → HFSet
  smul : HFSet → HFSet → HFSet   -- r ⊙ m
  -- pertenencia
  zero_mem    : zero ∈ M
  add_closed  : ∀ {m n : HFSet}, m ∈ M → n ∈ M → add m n ∈ M
  neg_closed  : ∀ {m : HFSet}, m ∈ M → neg m ∈ M
  smul_closed : ∀ {r m : HFSet}, r ∈ rng.R → m ∈ M → smul r m ∈ M
  -- grupo aditivo abeliano (axiomas izquierdos + comm)
  add_assoc   : ∀ {m n p : HFSet}, m ∈ M → n ∈ M → p ∈ M →
                  add (add m n) p = add m (add n p)
  add_comm    : ∀ {m n : HFSet}, m ∈ M → n ∈ M → add m n = add n m
  zero_add    : ∀ {m : HFSet}, m ∈ M → add zero m = m
  neg_add     : ∀ {m : HFSet}, m ∈ M → add (neg m) m = zero
  -- axiomas de módulo izquierdo
  smul_add    : ∀ {r m n : HFSet}, r ∈ rng.R → m ∈ M → n ∈ M →
                  smul r (add m n) = add (smul r m) (smul r n)
  add_smul    : ∀ {r s m : HFSet}, r ∈ rng.R → s ∈ rng.R → m ∈ M →
                  smul (rng.add r s) m = add (smul r m) (smul s m)
  mul_smul    : ∀ {r s m : HFSet}, r ∈ rng.R → s ∈ rng.R → m ∈ M →
                  smul (rng.mul r s) m = smul r (smul s m)
  one_smul    : ∀ {m : HFSet}, m ∈ M → smul rng.one m = m

namespace HFModule

variable {rng : HFRing} (mod : HFModule rng)

-- ─────────────────────────────────────────────────────────────────
-- Grupo aditivo subyacente
-- ─────────────────────────────────────────────────────────────────

/-- El módulo `mod` visto como grupo abeliano aditivo. -/
def toAdditiveHFGroup : HFGroup where
  G           := mod.M
  op          := mod.add
  e           := mod.zero
  inv         := mod.neg
  e_mem       := mod.zero_mem
  op_closed   := mod.add_closed
  inv_closed  := mod.neg_closed
  op_assoc    := mod.add_assoc
  op_id_left  := mod.zero_add
  op_inv_left := mod.neg_add

-- ─────────────────────────────────────────────────────────────────
-- Anulación: 0R ⊙ m = 0M
-- ─────────────────────────────────────────────────────────────────

theorem zero_smul {m : HFSet} (hm : m ∈ mod.M) : mod.smul rng.zero m = mod.zero := by
  -- (0+0)⊙m = 0⊙m + 0⊙m, así 0⊙m + 0⊙m = 0⊙m, luego 0⊙m = 0
  have hzm : mod.smul rng.zero m ∈ mod.M := mod.smul_closed rng.zero_mem hm
  have hxx : mod.add (mod.smul rng.zero m) (mod.smul rng.zero m) = mod.smul rng.zero m :=
    calc mod.add (mod.smul rng.zero m) (mod.smul rng.zero m)
        = mod.smul (rng.add rng.zero rng.zero) m := (mod.add_smul rng.zero_mem rng.zero_mem hm).symm
      _ = mod.smul rng.zero m                    := by rw [rng.zero_add rng.zero_mem]
  -- de x+x=x deducimos x=0: add (neg x) (add x x) = 0, pero también add (neg x) x = 0
  have key : mod.smul rng.zero m = mod.zero :=
    calc mod.smul rng.zero m
        = mod.add mod.zero (mod.smul rng.zero m)             := (mod.zero_add hzm).symm
      _ = mod.add (mod.add (mod.neg (mod.smul rng.zero m)) (mod.smul rng.zero m))
                  (mod.smul rng.zero m)                       := by rw [mod.neg_add hzm]
      _ = mod.add (mod.neg (mod.smul rng.zero m))
                  (mod.add (mod.smul rng.zero m) (mod.smul rng.zero m)) := by
              rw [mod.add_assoc (mod.neg_closed hzm) hzm hzm]
      _ = mod.add (mod.neg (mod.smul rng.zero m)) (mod.smul rng.zero m) := by rw [hxx]
      _ = mod.zero                                                        := mod.neg_add hzm
  exact key

-- ─────────────────────────────────────────────────────────────────
-- Anulación: r ⊙ 0M = 0M
-- ─────────────────────────────────────────────────────────────────

theorem smul_zero {r : HFSet} (hr : r ∈ rng.R) : mod.smul r mod.zero = mod.zero := by
  have hrz : mod.smul r mod.zero ∈ mod.M := mod.smul_closed hr mod.zero_mem
  have hxx : mod.add (mod.smul r mod.zero) (mod.smul r mod.zero) = mod.smul r mod.zero :=
    calc mod.add (mod.smul r mod.zero) (mod.smul r mod.zero)
        = mod.smul r (mod.add mod.zero mod.zero) := (mod.smul_add hr mod.zero_mem mod.zero_mem).symm
      _ = mod.smul r mod.zero                    := by rw [mod.zero_add mod.zero_mem]
  calc mod.smul r mod.zero
      = mod.add mod.zero (mod.smul r mod.zero)               := (mod.zero_add hrz).symm
    _ = mod.add (mod.add (mod.neg (mod.smul r mod.zero)) (mod.smul r mod.zero))
                (mod.smul r mod.zero)                         := by rw [mod.neg_add hrz]
    _ = mod.add (mod.neg (mod.smul r mod.zero))
                (mod.add (mod.smul r mod.zero) (mod.smul r mod.zero)) := by
            rw [mod.add_assoc (mod.neg_closed hrz) hrz hrz]
    _ = mod.add (mod.neg (mod.smul r mod.zero)) (mod.smul r mod.zero) := by rw [hxx]
    _ = mod.zero                                                        := mod.neg_add hrz

-- ─────────────────────────────────────────────────────────────────
-- (-r) ⊙ m = -(r ⊙ m)
-- ─────────────────────────────────────────────────────────────────

theorem neg_smul {r m : HFSet} (hr : r ∈ rng.R) (hm : m ∈ mod.M) :
    mod.smul (rng.neg r) m = mod.neg (mod.smul r m) := by
  have hrm  : mod.smul r m ∈ mod.M         := mod.smul_closed hr hm
  have hnrm : mod.smul (rng.neg r) m ∈ mod.M := mod.smul_closed (rng.neg_closed hr) hm
  have hkey : mod.add (mod.smul (rng.neg r) m) (mod.smul r m) = mod.zero :=
    calc mod.add (mod.smul (rng.neg r) m) (mod.smul r m)
        = mod.smul (rng.add (rng.neg r) r) m := (mod.add_smul (rng.neg_closed hr) hr hm).symm
      _ = mod.smul rng.zero m                := by rw [rng.neg_add hr]
      _ = mod.zero                           := mod.zero_smul hm
  exact mod.toAdditiveHFGroup.unique_inv hrm hnrm hkey

-- ─────────────────────────────────────────────────────────────────
-- r ⊙ (-m) = -(r ⊙ m)
-- ─────────────────────────────────────────────────────────────────

theorem smul_neg {r m : HFSet} (hr : r ∈ rng.R) (hm : m ∈ mod.M) :
    mod.smul r (mod.neg m) = mod.neg (mod.smul r m) := by
  have hrm  : mod.smul r m ∈ mod.M          := mod.smul_closed hr hm
  have hrnm : mod.smul r (mod.neg m) ∈ mod.M := mod.smul_closed hr (mod.neg_closed hm)
  have hkey : mod.add (mod.smul r (mod.neg m)) (mod.smul r m) = mod.zero :=
    calc mod.add (mod.smul r (mod.neg m)) (mod.smul r m)
        = mod.smul r (mod.add (mod.neg m) m) := (mod.smul_add hr (mod.neg_closed hm) hm).symm
      _ = mod.smul r mod.zero                := by rw [mod.neg_add hm]
      _ = mod.zero                           := mod.smul_zero hr
  exact mod.toAdditiveHFGroup.unique_inv hrm hrnm hkey

end HFModule

-- ─────────────────────────────────────────────────────────────────
-- Homomorfismo de módulos
-- ─────────────────────────────────────────────────────────────────

/-- Homomorfismo R-lineal entre HFModule sobre el mismo HFRing.
    Preserva la suma y la multiplicación escalar. -/
structure HFModuleHom (rng : HFRing) (M N : HFModule rng) where
  f      : HFSet → HFSet
  f_mem  : ∀ {m : HFSet}, m ∈ M.M → f m ∈ N.M
  f_add  : ∀ {m n : HFSet}, m ∈ M.M → n ∈ M.M →
             f (M.add m n) = N.add (f m) (f n)
  f_smul : ∀ {r m : HFSet}, r ∈ rng.R → m ∈ M.M →
             f (M.smul r m) = N.smul r (f m)

namespace HFModuleHom

variable {rng : HFRing} {M N P : HFModule rng} (φ : HFModuleHom rng M N)

-- ─────────────────────────────────────────────────────────────────
-- f(0M) = 0N
-- ─────────────────────────────────────────────────────────────────

theorem hom_zero : φ.f M.zero = N.zero := by
  have hfz : φ.f M.zero ∈ N.M := φ.f_mem M.zero_mem
  apply N.toAdditiveHFGroup.left_cancel hfz hfz N.zero_mem
  show N.add (φ.f M.zero) (φ.f M.zero) = N.add (φ.f M.zero) N.zero
  calc N.add (φ.f M.zero) (φ.f M.zero)
      = φ.f (M.add M.zero M.zero) := (φ.f_add M.zero_mem M.zero_mem).symm
    _ = φ.f M.zero                := by rw [M.zero_add M.zero_mem]
    _ = N.add (φ.f M.zero) N.zero := (N.toAdditiveHFGroup.op_id_right hfz).symm

-- ─────────────────────────────────────────────────────────────────
-- f(-m) = -f(m)
-- ─────────────────────────────────────────────────────────────────

theorem hom_neg {m : HFSet} (hm : m ∈ M.M) : φ.f (M.neg m) = N.neg (φ.f m) := by
  have hfm  : φ.f m ∈ N.M         := φ.f_mem hm
  have hfnm : φ.f (M.neg m) ∈ N.M := φ.f_mem (M.neg_closed hm)
  have hkey : N.add (φ.f (M.neg m)) (φ.f m) = N.zero :=
    calc N.add (φ.f (M.neg m)) (φ.f m)
        = φ.f (M.add (M.neg m) m) := (φ.f_add (M.neg_closed hm) hm).symm
      _ = φ.f M.zero              := by rw [M.neg_add hm]
      _ = N.zero                  := φ.hom_zero
  exact N.toAdditiveHFGroup.unique_inv hfm hfnm hkey

-- ─────────────────────────────────────────────────────────────────
-- Identidad y composición
-- ─────────────────────────────────────────────────────────────────

/-- La identidad es un homomorfismo de módulos. -/
def id (M : HFModule rng) : HFModuleHom rng M M where
  f      := fun m => m
  f_mem  := fun hm => hm
  f_add  := fun _ _ => rfl
  f_smul := fun _ _ => rfl

/-- Composición de homomorfismos de módulos. -/
def comp (ψ : HFModuleHom rng N P) (φ : HFModuleHom rng M N) : HFModuleHom rng M P where
  f      := fun m => ψ.f (φ.f m)
  f_mem  := fun hm => ψ.f_mem (φ.f_mem hm)
  f_add  := fun hm hn => by rw [φ.f_add hm hn, ψ.f_add (φ.f_mem hm) (φ.f_mem hn)]
  f_smul := fun hr hm => by rw [φ.f_smul hr hm, ψ.f_smul hr (φ.f_mem hm)]

end HFModuleHom

-- ─────────────────────────────────────────────────────────────────
-- Submódulo
-- ─────────────────────────────────────────────────────────────────

/-- Submódulo de un HFModule.
    Cerrado bajo suma y multiplicación escalar.
    La clausura bajo neg es explícita (derivable de smul con neg rng.one,
    pero se incluye como axioma para simplicidad del esqueleto). -/
structure HFSubmodule (rng : HFRing) (mod : HFModule rng) where
  S           : HFSet
  S_sub       : ∀ {x : HFSet}, x ∈ S → x ∈ mod.M
  zero_mem    : mod.zero ∈ S
  add_closed  : ∀ {m n : HFSet}, m ∈ S → n ∈ S → mod.add m n ∈ S
  neg_closed  : ∀ {m : HFSet}, m ∈ S → mod.neg m ∈ S
  smul_closed : ∀ {r m : HFSet}, r ∈ rng.R → m ∈ S → mod.smul r m ∈ S

namespace HFSubmodule

variable {rng : HFRing} {mod : HFModule rng}

/-- Todo submódulo es un módulo, heredando las operaciones del módulo ambiente. -/
def toHFModule (sub : HFSubmodule rng mod) : HFModule rng where
  M           := sub.S
  add         := mod.add
  zero        := mod.zero
  neg         := mod.neg
  smul        := mod.smul
  zero_mem    := sub.zero_mem
  add_closed  := sub.add_closed
  neg_closed  := sub.neg_closed
  smul_closed := sub.smul_closed
  add_assoc   := fun hm hn hp =>
    mod.add_assoc (sub.S_sub hm) (sub.S_sub hn) (sub.S_sub hp)
  add_comm    := fun hm hn =>
    mod.add_comm (sub.S_sub hm) (sub.S_sub hn)
  zero_add    := fun hm => mod.zero_add (sub.S_sub hm)
  neg_add     := fun hm => mod.neg_add (sub.S_sub hm)
  smul_add    := fun hr hm hn =>
    mod.smul_add hr (sub.S_sub hm) (sub.S_sub hn)
  add_smul    := fun hr hs hm =>
    mod.add_smul hr hs (sub.S_sub hm)
  mul_smul    := fun hr hs hm =>
    mod.mul_smul hr hs (sub.S_sub hm)
  one_smul    := fun hm => mod.one_smul (sub.S_sub hm)

/-- La intersección de dos submódulos del mismo módulo es un submódulo. -/
def inter (sub₁ sub₂ : HFSubmodule rng mod) : HFSubmodule rng mod where
  S           := HFSet.inter sub₁.S sub₂.S
  S_sub       := fun hx => by rw [HFSet.mem_inter] at hx; exact sub₁.S_sub hx.1
  zero_mem    := by rw [HFSet.mem_inter]; exact ⟨sub₁.zero_mem, sub₂.zero_mem⟩
  add_closed  := fun hm hn => by
    rw [HFSet.mem_inter] at hm hn ⊢
    exact ⟨sub₁.add_closed hm.1 hn.1, sub₂.add_closed hm.2 hn.2⟩
  neg_closed  := fun hm => by
    rw [HFSet.mem_inter] at hm ⊢
    exact ⟨sub₁.neg_closed hm.1, sub₂.neg_closed hm.2⟩
  smul_closed := fun hr hm => by
    rw [HFSet.mem_inter] at hm ⊢
    exact ⟨sub₁.smul_closed hr hm.1, sub₂.smul_closed hr hm.2⟩

end HFSubmodule

end HFAlgebra
