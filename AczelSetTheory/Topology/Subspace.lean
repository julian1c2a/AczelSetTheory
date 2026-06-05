import AczelSetTheory.Topology.Basic
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Powerset

namespace HFTopology

/-!
# Topología heredada (subespacio) y aplicaciones continuas

Dado un espacio topológico `(X, τ)` y un subconjunto `A ⊆ X`, la **topología
inducida** sobre `A` es `τ_A = {U ∩ A | U ∈ τ}`.

Una **aplicación continua** `f : (X₁, τ₁) → (X₂, τ₂)` satisface que la
preimagen de cada abierto es abierta.
-/

/-! ## Preimagen -/

/-- Preimagen de `V` bajo `f` respecto al dominio `X`. -/
def HFTopSpace.preimage (ts : HFTopSpace) (f : HFSet → HFSet) (V : HFSet) : HFSet :=
  HFSet.sep ts.X (fun x => f x ∈ V)

theorem HFTopSpace.mem_preimage (ts : HFTopSpace) (f : HFSet → HFSet) (V x : HFSet) :
    x ∈ ts.preimage f V ↔ x ∈ ts.X ∧ f x ∈ V := by
  unfold preimage
  rw [HFSet.mem_sep]

/-! ## Topología subespacio -/

/-- Topología inducida sobre `A ⊆ X`: los abiertos son las intersecciones `U ∩ A` con `U ∈ τ`. -/
def HFTopSpace.subspace (ts : HFTopSpace) (A : HFSet) (hA : A ⊆ ts.X) :
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
    -- ∅ = inter ∅ A: ambos lados son vacíos
    apply HFSet.extensionality; intro x
    rw [HFSet.mem_inter]
    exact ⟨fun h => absurd h (HFSet.not_mem_empty x),
           fun ⟨h, _⟩ => absurd h (HFSet.not_mem_empty x)⟩
  univ_mem   := by
    rw [HFSet.mem_sep]
    refine ⟨(HFSet.mem_powerset A A).mpr (HFSet.subset_refl A),
           ts.X, ts.univ_mem, ?_⟩
    -- A = inter X A porque A ⊆ X
    apply HFSet.extensionality; intro x
    rw [HFSet.mem_inter]
    exact ⟨fun h => ⟨hA x h, h⟩, And.right⟩
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
        -- sUnion F = inter (sUnion G) A
        rw [HFSet.mem_inter, HFSet.mem_sUnion, HFSet.mem_sUnion]
        constructor
        · rintro ⟨V, hVF, hxV⟩
          -- V ∈ F y F ⊆ subτ, luego V = inter U₀ A para algún U₀ ∈ ts.τ
          have hVsep := hFτ V hVF
          rw [HFSet.mem_sep] at hVsep
          obtain ⟨_, U₀, hU₀τ, rfl⟩ := hVsep
          rw [HFSet.mem_inter] at hxV
          exact ⟨⟨U₀, by rw [HFSet.mem_sep]; exact ⟨hU₀τ, hVF⟩, hxV.1⟩, hxV.2⟩
        · rintro ⟨⟨U, hUG, hxU⟩, hxA⟩
          rw [HFSet.mem_sep] at hUG
          exact ⟨HFSet.inter U A, hUG.2, by rw [HFSet.mem_inter]; exact ⟨hxU, hxA⟩⟩
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
      -- (U₀∩A) ∩ (V₀∩A) = (U₀∩V₀) ∩ A
      apply HFSet.extensionality; intro z
      rw [HFSet.mem_inter, HFSet.mem_inter, HFSet.mem_inter,
          HFSet.mem_inter, HFSet.mem_inter]
      constructor
      · rintro ⟨⟨hzU, hzA⟩, hzV, _⟩
        exact ⟨⟨hzU, hzV⟩, hzA⟩
      · rintro ⟨⟨hzU, hzV⟩, hzA⟩
        exact ⟨⟨hzU, hzA⟩, hzV, hzA⟩

/-! ## Aplicaciones continuas -/

/-- `f : X₁ → X₂` es continua si la preimagen de cada abierto es abierta. -/
structure HFContinuous (ts₁ ts₂ : HFTopSpace) where
  /-- La función subyacente. -/
  f             : HFSet → HFSet
  /-- `f` lleva `X₁` en `X₂`. -/
  f_mem         : ∀ {x : HFSet}, x ∈ ts₁.X → f x ∈ ts₂.X
  /-- La preimagen de cada abierto es abierta. -/
  preimage_open : ∀ {V : HFSet}, V ∈ ts₂.τ → ts₁.preimage f V ∈ ts₁.τ

namespace HFContinuous

/-- La aplicación identidad es continua. -/
def id (ts : HFTopSpace) : HFContinuous ts ts where
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
def comp {ts₁ ts₂ ts₃ : HFTopSpace}
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
    {V₁ V₂ : HFSet} (_h₁ : V₁ ∈ ts₂.τ) (_h₂ : V₂ ∈ ts₂.τ) :
    ts₁.preimage f.f (HFSet.inter V₁ V₂) =
    HFSet.inter (ts₁.preimage f.f V₁) (ts₁.preimage f.f V₂) := by
  apply HFSet.extensionality; intro x
  -- Expandir en orden: preimage del inter, luego inter de preimages
  rw [HFTopSpace.mem_preimage, HFSet.mem_inter,  -- LHS: x∈X ∧ f(x)∈V₁ ∧ f(x)∈V₂
      HFSet.mem_inter,                           -- RHS: x∈preimage V₁ ∧ x∈preimage V₂
      HFTopSpace.mem_preimage, HFTopSpace.mem_preimage]  -- x∈preimage Vⱼ ↔ x∈X ∧ f(x)∈Vⱼ
  constructor
  · rintro ⟨hxX, hf1, hf2⟩
    exact ⟨⟨hxX, hf1⟩, hxX, hf2⟩
  · rintro ⟨⟨hxX, hf1⟩, _, hf2⟩
    exact ⟨hxX, hf1, hf2⟩

end HFContinuous

end HFTopology
