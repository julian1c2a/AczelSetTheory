import AczelSetTheory.HFSets
import AczelSetTheory.Axioms.Subset
import AczelSetTheory.Axioms.Intersection

namespace HFAlgebra

/-!
# Retículos (Lattices) sobre HFSet

Un **retículo** `(L, ⊓, ⊔)` satisface las leyes de conmutatividad, asociatividad
y absorción para las operaciones de ínfimo (`meet`) y supremo (`join`).
-/

structure HFLattice where
  L    : HFSet
  meet : HFSet → HFSet → HFSet
  join : HFSet → HFSet → HFSet
  meet_closed : ∀ {a b : HFSet}, a ∈ L → b ∈ L → meet a b ∈ L
  join_closed : ∀ {a b : HFSet}, a ∈ L → b ∈ L → join a b ∈ L
  meet_comm   : ∀ {a b : HFSet}, a ∈ L → b ∈ L → meet a b = meet b a
  join_comm   : ∀ {a b : HFSet}, a ∈ L → b ∈ L → join a b = join b a
  meet_assoc  : ∀ {a b c : HFSet}, a ∈ L → b ∈ L → c ∈ L →
                  meet (meet a b) c = meet a (meet b c)
  join_assoc  : ∀ {a b c : HFSet}, a ∈ L → b ∈ L → c ∈ L →
                  join (join a b) c = join a (join b c)
  meet_absorb : ∀ {a b : HFSet}, a ∈ L → b ∈ L → meet a (join a b) = a
  join_absorb : ∀ {a b : HFSet}, a ∈ L → b ∈ L → join a (meet a b) = a

namespace HFLattice

section Derived

variable (lat : HFLattice)

/-- El orden natural: `a ≤ b ↔ a ⊓ b = a`. -/
def le (a b : HFSet) : Prop := lat.meet a b = a

/-- Idempotencia del ínfimo (derivada de absorción). -/
theorem meet_idem {a : HFSet} (ha : a ∈ lat.L) : lat.meet a a = a := by
  have h1 : lat.join a (lat.meet a a) = a := lat.join_absorb ha ha
  calc lat.meet a a
      = lat.meet a (lat.join a (lat.meet a a)) := by rw [h1]
    _ = a := lat.meet_absorb ha (lat.meet_closed ha ha)

/-- Idempotencia del supremo (derivada de absorción). -/
theorem join_idem {a : HFSet} (ha : a ∈ lat.L) : lat.join a a = a := by
  have h1 : lat.meet a (lat.join a a) = a := lat.meet_absorb ha ha
  calc lat.join a a
      = lat.join a (lat.meet a (lat.join a a)) := by rw [h1]
    _ = a := lat.join_absorb ha (lat.join_closed ha ha)

theorem le_refl {a : HFSet} (ha : a ∈ lat.L) : lat.le a a :=
  lat.meet_idem ha

theorem le_antisymm {a b : HFSet} (ha : a ∈ lat.L) (hb : b ∈ lat.L)
    (hab : lat.le a b) (hba : lat.le b a) : a = b := by
  have h2 : lat.meet b a = b := hba
  rw [lat.meet_comm hb ha] at h2
  rw [← hab, h2]

theorem le_trans {a b c : HFSet} (ha : a ∈ lat.L) (hb : b ∈ lat.L) (hc : c ∈ lat.L)
    (hab : lat.le a b) (hbc : lat.le b c) : lat.le a c := by
  show lat.meet a c = a
  calc lat.meet a c
      = lat.meet (lat.meet a b) c := by rw [hab]
    _ = lat.meet a (lat.meet b c) := lat.meet_assoc ha hb hc
    _ = lat.meet a b              := by rw [hbc]
    _ = a                         := hab

/-- El ínfimo `a ⊓ b` está por debajo de `a`. -/
theorem meet_le_left {a b : HFSet} (ha : a ∈ lat.L) (hb : b ∈ lat.L) :
    lat.le (lat.meet a b) a := by
  show lat.meet (lat.meet a b) a = lat.meet a b
  rw [lat.meet_comm (lat.meet_closed ha hb) ha,
      ← lat.meet_assoc ha ha hb,
      lat.meet_idem ha]

/-- El ínfimo `a ⊓ b` está por debajo de `b`. -/
theorem meet_le_right {a b : HFSet} (ha : a ∈ lat.L) (hb : b ∈ lat.L) :
    lat.le (lat.meet a b) b := by
  show lat.meet (lat.meet a b) b = lat.meet a b
  rw [lat.meet_assoc ha hb hb, lat.meet_idem hb]

/-- `a` está por debajo del supremo `a ⊔ b`. -/
theorem le_join_left {a b : HFSet} (ha : a ∈ lat.L) (hb : b ∈ lat.L) :
    lat.le a (lat.join a b) := by
  show lat.meet a (lat.join a b) = a
  exact lat.meet_absorb ha hb

/-- `b` está por debajo del supremo `a ⊔ b`. -/
theorem le_join_right {a b : HFSet} (ha : a ∈ lat.L) (hb : b ∈ lat.L) :
    lat.le b (lat.join a b) := by
  show lat.meet b (lat.join a b) = b
  rw [lat.join_comm ha hb]
  exact lat.meet_absorb hb ha

end Derived

end HFLattice

/-! ## Retículo acotado -/

/-- Retículo con elemento mínimo (`bot`) y máximo (`top`).
    Todos los axiomas se listan de forma plana, igual que `HFGroup`. -/
structure HFBoundedLattice where
  L    : HFSet
  meet : HFSet → HFSet → HFSet
  join : HFSet → HFSet → HFSet
  bot  : HFSet
  top  : HFSet
  -- axiomas de retículo
  meet_closed : ∀ {a b : HFSet}, a ∈ L → b ∈ L → meet a b ∈ L
  join_closed : ∀ {a b : HFSet}, a ∈ L → b ∈ L → join a b ∈ L
  meet_comm   : ∀ {a b : HFSet}, a ∈ L → b ∈ L → meet a b = meet b a
  join_comm   : ∀ {a b : HFSet}, a ∈ L → b ∈ L → join a b = join b a
  meet_assoc  : ∀ {a b c : HFSet}, a ∈ L → b ∈ L → c ∈ L →
                  meet (meet a b) c = meet a (meet b c)
  join_assoc  : ∀ {a b c : HFSet}, a ∈ L → b ∈ L → c ∈ L →
                  join (join a b) c = join a (join b c)
  meet_absorb : ∀ {a b : HFSet}, a ∈ L → b ∈ L → meet a (join a b) = a
  join_absorb : ∀ {a b : HFSet}, a ∈ L → b ∈ L → join a (meet a b) = a
  -- axiomas de cota
  bot_mem  : bot ∈ L
  top_mem  : top ∈ L
  /-- `bot` es elemento neutro para el supremo: `a ⊔ ⊥ = a`. -/
  join_bot : ∀ {a : HFSet}, a ∈ L → join a bot = a
  /-- `top` es elemento neutro para el ínfimo: `a ⊓ ⊤ = a`. -/
  meet_top : ∀ {a : HFSet}, a ∈ L → meet a top = a

/-- Convierte un `HFBoundedLattice` en `HFLattice` (olvidando bot y top). -/
def HFBoundedLattice.toLattice (bl : HFBoundedLattice) : HFLattice where
  L           := bl.L
  meet        := bl.meet
  join        := bl.join
  meet_closed := bl.meet_closed
  join_closed := bl.join_closed
  meet_comm   := bl.meet_comm
  join_comm   := bl.join_comm
  meet_assoc  := bl.meet_assoc
  join_assoc  := bl.join_assoc
  meet_absorb := bl.meet_absorb
  join_absorb := bl.join_absorb

namespace HFBoundedLattice

section Derived

variable (bl : HFBoundedLattice)

/-- `bot` es absorbente para el ínfimo: `a ⊓ ⊥ = ⊥`. -/
theorem meet_bot {a : HFSet} (ha : a ∈ bl.L) : bl.meet a bl.bot = bl.bot := by
  have hjba : bl.join bl.bot a = a := by
    rw [bl.join_comm bl.bot_mem ha]; exact bl.join_bot ha
  have hm : bl.meet bl.bot a = bl.bot := by
    have := bl.meet_absorb bl.bot_mem ha
    rw [hjba] at this
    exact this
  rw [bl.meet_comm ha bl.bot_mem]; exact hm

/-- `top` es absorbente para el supremo: `a ⊔ ⊤ = ⊤`. -/
theorem join_top {a : HFSet} (ha : a ∈ bl.L) : bl.join a bl.top = bl.top := by
  have hmta : bl.meet bl.top a = a := by
    rw [bl.meet_comm bl.top_mem ha]; exact bl.meet_top ha
  have := bl.join_absorb bl.top_mem ha
  rw [hmta] at this
  rw [bl.join_comm ha bl.top_mem]; exact this

end Derived

end HFBoundedLattice

/-! ## Retículo distributivo -/

/-- Retículo que satisface la ley distributiva. -/
structure HFDistributiveLattice where
  L    : HFSet
  meet : HFSet → HFSet → HFSet
  join : HFSet → HFSet → HFSet
  -- axiomas de retículo
  meet_closed : ∀ {a b : HFSet}, a ∈ L → b ∈ L → meet a b ∈ L
  join_closed : ∀ {a b : HFSet}, a ∈ L → b ∈ L → join a b ∈ L
  meet_comm   : ∀ {a b : HFSet}, a ∈ L → b ∈ L → meet a b = meet b a
  join_comm   : ∀ {a b : HFSet}, a ∈ L → b ∈ L → join a b = join b a
  meet_assoc  : ∀ {a b c : HFSet}, a ∈ L → b ∈ L → c ∈ L →
                  meet (meet a b) c = meet a (meet b c)
  join_assoc  : ∀ {a b c : HFSet}, a ∈ L → b ∈ L → c ∈ L →
                  join (join a b) c = join a (join b c)
  meet_absorb : ∀ {a b : HFSet}, a ∈ L → b ∈ L → meet a (join a b) = a
  join_absorb : ∀ {a b : HFSet}, a ∈ L → b ∈ L → join a (meet a b) = a
  /-- Ley distributiva: `a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)`. -/
  meet_distrib : ∀ {a b c : HFSet}, a ∈ L → b ∈ L → c ∈ L →
                   meet a (join b c) = join (meet a b) (meet a c)

/-- Convierte un `HFDistributiveLattice` en `HFLattice`. -/
def HFDistributiveLattice.toLattice (dl : HFDistributiveLattice) : HFLattice where
  L           := dl.L
  meet        := dl.meet
  join        := dl.join
  meet_closed := dl.meet_closed
  join_closed := dl.join_closed
  meet_comm   := dl.meet_comm
  join_comm   := dl.join_comm
  meet_assoc  := dl.meet_assoc
  join_assoc  := dl.join_assoc
  meet_absorb := dl.meet_absorb
  join_absorb := dl.join_absorb

namespace HFDistributiveLattice

section Derived

variable (dl : HFDistributiveLattice)

/-- Ley distributiva dual: `a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)`. -/
theorem join_distrib {a b c : HFSet} (ha : a ∈ dl.L) (hb : b ∈ dl.L) (hc : c ∈ dl.L) :
    dl.join a (dl.meet b c) = dl.meet (dl.join a b) (dl.join a c) := by
  symm
  -- Probamos: (a⊔b)⊓(a⊔c) = a⊔(b⊓c)
  calc dl.meet (dl.join a b) (dl.join a c)
      -- Paso 1: distribuir meet sobre join (aplicado a (a⊔b), a, c)
      = dl.join (dl.meet (dl.join a b) a) (dl.meet (dl.join a b) c) :=
            dl.meet_distrib (dl.join_closed ha hb) ha hc
      -- Paso 2: (a⊔b)⊓a = a por conmut. + absorción
    _ = dl.join a (dl.meet (dl.join a b) c) := by
            rw [dl.meet_comm (dl.join_closed ha hb) ha, dl.meet_absorb ha hb]
      -- Paso 3: (a⊔b)⊓c = (a⊓c)⊔(b⊓c) por conmut. + meet_distrib + conmut.
    _ = dl.join a (dl.join (dl.meet a c) (dl.meet b c)) := by
            congr 1
            rw [dl.meet_comm (dl.join_closed ha hb) hc, dl.meet_distrib hc ha hb,
                dl.meet_comm hc ha, dl.meet_comm hc hb]
      -- Paso 4: asociatividad del join
    _ = dl.join (dl.join a (dl.meet a c)) (dl.meet b c) :=
            (dl.join_assoc ha (dl.meet_closed ha hc) (dl.meet_closed hb hc)).symm
      -- Paso 5: a⊔(a⊓c) = a por absorción
    _ = dl.join a (dl.meet b c) := by rw [dl.join_absorb ha hc]

end Derived

end HFDistributiveLattice

/-! ## Homomorfismo de retículos -/

/-- Homomorfismo de retículos: preserva ⊓ y ⊔. -/
structure HFLatHom (L M : HFLattice) where
  f      : HFSet → HFSet
  f_mem  : ∀ {a : HFSet}, a ∈ L.L → f a ∈ M.L
  f_meet : ∀ {a b : HFSet}, a ∈ L.L → b ∈ L.L → f (L.meet a b) = M.meet (f a) (f b)
  f_join : ∀ {a b : HFSet}, a ∈ L.L → b ∈ L.L → f (L.join a b) = M.join (f a) (f b)

namespace HFLatHom

/-- El homomorfismo identidad. -/
def id (L : HFLattice) : HFLatHom L L where
  f      := fun a => a
  f_mem  := fun ha => ha
  f_meet := fun _ _ => rfl
  f_join := fun _ _ => rfl

/-- Composición de homomorfismos. -/
def comp {L M N : HFLattice} (ψ : HFLatHom M N) (φ : HFLatHom L M) : HFLatHom L N where
  f      := fun a => ψ.f (φ.f a)
  f_mem  := fun ha => ψ.f_mem (φ.f_mem ha)
  f_meet := fun ha hb => by rw [φ.f_meet ha hb, ψ.f_meet (φ.f_mem ha) (φ.f_mem hb)]
  f_join := fun ha hb => by rw [φ.f_join ha hb, ψ.f_join (φ.f_mem ha) (φ.f_mem hb)]

end HFLatHom

/-! ## Subretículo -/

/-- Subretículo: subconjunto cerrado bajo ⊓ y ⊔. -/
structure HFSublattice (lat : HFLattice) where
  S           : HFSet
  S_sub       : ∀ {x : HFSet}, x ∈ S → x ∈ lat.L
  meet_closed : ∀ {a b : HFSet}, a ∈ S → b ∈ S → lat.meet a b ∈ S
  join_closed : ∀ {a b : HFSet}, a ∈ S → b ∈ S → lat.join a b ∈ S

namespace HFSublattice

/-- Todo subretículo es un retículo. -/
def toHFLattice {lat : HFLattice} (sub : HFSublattice lat) : HFLattice where
  L           := sub.S
  meet        := lat.meet
  join        := lat.join
  meet_closed := fun ha hb => sub.meet_closed ha hb
  join_closed := fun ha hb => sub.join_closed ha hb
  meet_comm   := fun ha hb => lat.meet_comm (sub.S_sub ha) (sub.S_sub hb)
  join_comm   := fun ha hb => lat.join_comm (sub.S_sub ha) (sub.S_sub hb)
  meet_assoc  := fun ha hb hc =>
                   lat.meet_assoc (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)
  join_assoc  := fun ha hb hc =>
                   lat.join_assoc (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)
  meet_absorb := fun ha hb => lat.meet_absorb (sub.S_sub ha) (sub.S_sub hb)
  join_absorb := fun ha hb => lat.join_absorb (sub.S_sub ha) (sub.S_sub hb)

/-- La intersección de dos subretículos es un subretículo. -/
def inter {lat : HFLattice} (sub₁ sub₂ : HFSublattice lat) : HFSublattice lat where
  S           := HFSet.inter sub₁.S sub₂.S
  S_sub       := fun hx => by
                   rw [HFSet.mem_inter] at hx
                   exact sub₁.S_sub hx.1
  meet_closed := fun ha hb => by
                   rw [HFSet.mem_inter] at ha hb ⊢
                   exact ⟨sub₁.meet_closed ha.1 hb.1, sub₂.meet_closed ha.2 hb.2⟩
  join_closed := fun ha hb => by
                   rw [HFSet.mem_inter] at ha hb ⊢
                   exact ⟨sub₁.join_closed ha.1 hb.1, sub₂.join_closed ha.2 hb.2⟩

end HFSublattice

end HFAlgebra
