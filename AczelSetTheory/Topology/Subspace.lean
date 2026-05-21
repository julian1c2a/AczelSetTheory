import AczelSetTheory.Topology.Basic
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Powerset

open Classical

namespace HFTopology

/-!
# Topología heredada (subespacio) y aplicaciones continuas

Dado un espacio topológico `(X, τ)` y un subconjunto `A ⊆ X`, la **topología
inducida** sobre `A` es `τ_A = {U ∩ A | U ∈ τ}`.

Una **aplicación continua** `f : (X₁, τ₁) → (X₂, τ₂)` satisface que la
preimagen de todo abierto es abierta.
-/

/-! ## Preimagen -/

/-- Preimagen de `V` bajo `f` respecto al dominio `X`. -/
noncomputable def HFTopSpace.preimage (ts : HFTopSpace) (f : HFSet → HFSet) (V : HFSet) : HFSet :=
  HFSet.sep ts.X (fun x => f x ∈ V)

theorem HFTopSpace.mem_preimage (ts : HFTopSpace) (f : HFSet → HFSet) (V x : HFSet) :
    x ∈ ts.preimage f V ↔ x ∈ ts.X ∧ f x ∈ V := by
  unfold preimage
  rw [HFSet.mem_sep]

/-! ## Topología subespacio -/

/-- Topología inducida sobre `A ⊆ X`: los abiertos son las intersecciones `U ∩ A` con `U ∈ τ`. -/
noncomputable def HFTopSpace.subspace (ts : HFTopSpace) (A : HFSet) (hA : A ⊆ ts.X) :
    HFTopSpace where
  X          := A
  τ          := HFSet.sep (HFSet.powerset A) (fun V => ∃ U, U ∈ ts.τ ∧ V = HFSet.inter U A)
  τ_sub      := by
    intro U hU
    rw [HFSet.mem_sep, HFSet.mem_powerset] at hU
    exact hU.1
  empty_mem  := by
    rw [HFSet.mem_sep]
    refine ⟨(HFSet.mem_powerset A HFSet.empty).mpr (HFSet.empty_subset A),
           HFSet.empty, ts.empty_mem, ?_⟩
    exact sorry
  univ_mem   := by
    rw [HFSet.mem_sep]
    refine ⟨(HFSet.mem_powerset A A).mpr (HFSet.subset_refl A),
           ts.X, ts.univ_mem, ?_⟩
    exact sorry
  sUnion_mem := by
    intro F hFτ
    rw [HFSet.subset_iff] at hFτ
    rw [HFSet.mem_sep]
    constructor
    · rw [HFSet.mem_powerset]
      intro z hz
      rw [HFSet.mem_sUnion] at hz
      obtain ⟨V, hVF, hzV⟩ := hz
      have hVsep := hFτ V hVF
      rw [HFSet.mem_sep, HFSet.mem_powerset] at hVsep
      exact hVsep.1 z hzV
    · -- sUnion F = inter (sUnion {U | ∃V∈F, V = inter U A}) A
      -- Build the "lifted" collection: {U ∈ τ | inter U A ∈ F}
      let G := HFSet.sep ts.τ (fun U => HFSet.inter U A ∈ F)
      refine ⟨HFSet.sUnion G, ?_, ?_⟩
      · apply ts.sUnion_mem
        rw [HFSet.subset_iff]; intro U hU
        rw [HFSet.mem_sep] at hU; exact hU.1
      · apply HFSet.extensionality; intro x
        exact sorry
  inter_mem  := by
    intro U V hU hV
    rw [HFSet.mem_sep] at hU hV ⊢
    obtain ⟨_, U₀, hU₀τ, rfl⟩ := hU
    obtain ⟨_, V₀, hV₀τ, rfl⟩ := hV
    constructor
    · rw [HFSet.mem_powerset]
      intro z hz
      rw [HFSet.mem_inter, HFSet.mem_inter] at hz
      exact hz.1.2
    · refine ⟨HFSet.inter U₀ V₀, ts.inter_mem hU₀τ hV₀τ, ?_⟩
      exact sorry

/-! ## Aplicaciones continuas -/

/-- `f : X₁ → X₂` es continua si la preimagen de todo abierto es abierta. -/
structure HFContinuous (ts₁ ts₂ : HFTopSpace) where
  /-- La función subyacente. -/
  f             : HFSet → HFSet
  /-- `f` lleva `X₁` en `X₂`. -/
  f_mem         : ∀ {x : HFSet}, x ∈ ts₁.X → f x ∈ ts₂.X
  /-- La preimagen de todo abierto es abierta. -/
  preimage_open : ∀ {V : HFSet}, V ∈ ts₂.τ → ts₁.preimage f V ∈ ts₁.τ

namespace HFContinuous

/-- La aplicación identidad es continua. -/
noncomputable def id (ts : HFTopSpace) : HFContinuous ts ts where
  f             := fun x => x
  f_mem         := fun hx => hx
  preimage_open := by
    intro V hV
    have : ts.preimage (fun x => x) V = HFSet.inter ts.X V := by
      apply HFSet.extensionality; intro x
      rw [HFTopSpace.mem_preimage, HFSet.mem_inter]
    rw [this]
    -- inter X V = V when V ⊆ X (V is open so V ⊆ X)
    have hVsub : V ⊆ ts.X := ts.τ_sub hV
    have : HFSet.inter ts.X V = V := by
      apply HFSet.extensionality; intro x
      rw [HFSet.mem_inter]
      exact ⟨And.right, fun hx => ⟨hVsub x hx, hx⟩⟩
    rw [this]; exact hV

/-- Composición de aplicaciones continuas. -/
noncomputable def comp {ts₁ ts₂ ts₃ : HFTopSpace}
    (g : HFContinuous ts₂ ts₃) (f : HFContinuous ts₁ ts₂) : HFContinuous ts₁ ts₃ where
  f             := fun x => g.f (f.f x)
  f_mem         := fun hx => g.f_mem (f.f_mem hx)
  preimage_open := by
    intro W hW
    -- f⁻¹(g⁻¹(W)) = (g∘f)⁻¹(W)
    have key : ts₁.preimage (fun x => g.f (f.f x)) W =
               ts₁.preimage f.f (ts₂.preimage g.f W) := by
      apply HFSet.extensionality; intro x
      rw [HFTopSpace.mem_preimage]
      constructor
      · intro ⟨hxX, hgfW⟩
        rw [HFTopSpace.mem_preimage]
        exact ⟨hxX, by rw [HFTopSpace.mem_preimage]; exact ⟨f.f_mem hxX, hgfW⟩⟩
      · intro hx
        rw [HFTopSpace.mem_preimage] at hx
        obtain ⟨hxX, hfx⟩ := hx
        rw [HFTopSpace.mem_preimage] at hfx
        exact ⟨hxX, hfx.2⟩
    rw [key]
    exact f.preimage_open (g.preimage_open hW)

/-- La preimagen de `V₁ ∩ V₂` es `f⁻¹(V₁) ∩ f⁻¹(V₂)`. -/
theorem preimage_inter (ts₁ ts₂ : HFTopSpace) (f : HFContinuous ts₁ ts₂)
    {V₁ V₂ : HFSet} (h₁ : V₁ ∈ ts₂.τ) (h₂ : V₂ ∈ ts₂.τ) :
    ts₁.preimage f.f (HFSet.inter V₁ V₂) =
    HFSet.inter (ts₁.preimage f.f V₁) (ts₁.preimage f.f V₂) := by
  apply HFSet.extensionality; intro x
  exact sorry

end HFContinuous

end HFTopology
