import AczelSetTheory.Topology.Basic
import AczelSetTheory.Axioms.Singleton
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Intersection
import AczelSetTheory.Axioms.Setminus

open Classical

namespace HFTopology

/-!
# Axiomas de separación

Dado un espacio topológico `(X, τ)` sobre `HFSet`, se definen los axiomas de
separación T₀ (Kolmogorov), T₁ (Fréchet), T₂ (Hausdorff), regularidad y
normalidad, junto con los espacios T₃ y T₄.

## Cadena de implicaciones

```
T₄ → T₃ → T₂ → T₁ → T₀
```

## Caracterización fundamental

T₁ ↔ cada singleton `{x}` es cerrado.
-/

/-! ## Definiciones -/

/-- **T₀ (Kolmogorov)**: para cada par de puntos distintos existe un abierto que
    contiene a uno pero no al otro. -/
def HFTopSpace.isT0 (ts : HFTopSpace) : Prop :=
  ∀ {x y : HFSet}, x ∈ ts.X → y ∈ ts.X → x ≠ y →
    ∃ U, U ∈ ts.τ ∧ ((x ∈ U ∧ y ∉ U) ∨ (y ∈ U ∧ x ∉ U))

/-- **T₁ (Fréchet)**: para cada par de puntos distintos existen abiertos que
    los separan mutuamente (cada abierto excluye al otro punto). -/
def HFTopSpace.isT1 (ts : HFTopSpace) : Prop :=
  ∀ {x y : HFSet}, x ∈ ts.X → y ∈ ts.X → x ≠ y →
    ∃ U V, U ∈ ts.τ ∧ V ∈ ts.τ ∧ x ∈ U ∧ y ∉ U ∧ y ∈ V ∧ x ∉ V

/-- **T₂ (Hausdorff)**: para cada par de puntos distintos existen abiertos
    *disjuntos* que los contienen. -/
def HFTopSpace.isT2 (ts : HFTopSpace) : Prop :=
  ∀ {x y : HFSet}, x ∈ ts.X → y ∈ ts.X → x ≠ y →
    ∃ U V, U ∈ ts.τ ∧ V ∈ ts.τ ∧ x ∈ U ∧ y ∈ V ∧
      HFSet.inter U V = HFSet.empty

/-- **Espacio regular**: para cada punto `x` y cerrado `A` con `x ∉ A`,
    existen abiertos disjuntos que los separan. -/
def HFTopSpace.isRegular (ts : HFTopSpace) : Prop :=
  ∀ {x A : HFSet}, x ∈ ts.X → ts.isClosed A → x ∉ A →
    ∃ U V, U ∈ ts.τ ∧ V ∈ ts.τ ∧ x ∈ U ∧ A ⊆ V ∧
      HFSet.inter U V = HFSet.empty

/-- **T₃**: T₁ + regular. -/
def HFTopSpace.isT3 (ts : HFTopSpace) : Prop :=
  ts.isT1 ∧ ts.isRegular

/-- **Espacio normal**: para cada par de cerrados disjuntos existen abiertos
    disjuntos que los contienen. -/
def HFTopSpace.isNormal (ts : HFTopSpace) : Prop :=
  ∀ {A B : HFSet}, ts.isClosed A → ts.isClosed B →
    HFSet.inter A B = HFSet.empty →
    ∃ U V, U ∈ ts.τ ∧ V ∈ ts.τ ∧ A ⊆ U ∧ B ⊆ V ∧
      HFSet.inter U V = HFSet.empty

/-- **T₄**: T₁ + normal. -/
def HFTopSpace.isT4 (ts : HFTopSpace) : Prop :=
  ts.isT1 ∧ ts.isNormal

/-! ## Implicaciones: T₂ → T₁ → T₀ -/

/-- T₂ implica T₁. -/
theorem HFTopSpace.T2_implies_T1 {ts : HFTopSpace} (h : ts.isT2) : ts.isT1 := by
  intro x y hx hy hne
  obtain ⟨U, V, hUτ, hVτ, hxU, hyV, hdisj⟩ := h hx hy hne
  refine ⟨U, V, hUτ, hVτ, hxU, ?_, hyV, ?_⟩
  · intro hyU
    have hmem : y ∈ HFSet.inter U V := by rw [HFSet.mem_inter]; exact ⟨hyU, hyV⟩
    rw [hdisj] at hmem
    exact HFSet.not_mem_empty y hmem
  · intro hxV
    have hmem : x ∈ HFSet.inter U V := by rw [HFSet.mem_inter]; exact ⟨hxU, hxV⟩
    rw [hdisj] at hmem
    exact HFSet.not_mem_empty x hmem

/-- T₁ implica T₀. -/
theorem HFTopSpace.T1_implies_T0 {ts : HFTopSpace} (h : ts.isT1) : ts.isT0 := by
  intro x y hx hy hne
  obtain ⟨U, _, hUτ, _, hxU, hyU, _, _⟩ := h hx hy hne
  exact ⟨U, hUτ, Or.inl ⟨hxU, hyU⟩⟩

/-! ## Caracterización: T₁ ↔ singletons cerrados -/

/-- Si T₁, entonces cada singleton `{x}` es cerrado. -/
theorem HFTopSpace.singletons_closed_of_T1 {ts : HFTopSpace} (h : ts.isT1)
    {x : HFSet} (hx : x ∈ ts.X) : ts.isClosed (HFSet.singleton x) := by
  show HFSet.setminus ts.X (HFSet.singleton x) ∈ ts.τ
  -- X \ {x} = ⋃ {U ∈ τ | x ∉ U}
  have key : HFSet.setminus ts.X (HFSet.singleton x) =
      HFSet.sUnion (HFSet.sep ts.τ (fun U => x ∉ U)) := by
    apply HFSet.extensionality
    intro z
    rw [HFSet.mem_setminus, HFSet.mem_singleton, HFSet.mem_sUnion]
    constructor
    · intro ⟨hzX, hzne⟩
      -- T₁ con (x, z): da V con z ∈ V y x ∉ V
      obtain ⟨_, V, _, hVτ, _, _, hzV, hxV⟩ := h hx hzX (fun heq => hzne heq.symm)
      exact ⟨V, by rw [HFSet.mem_sep]; exact ⟨hVτ, hxV⟩, hzV⟩
    · intro ⟨U, hUF, hzU⟩
      rw [HFSet.mem_sep] at hUF
      exact ⟨ts.τ_sub hUF.1 z hzU, fun heq => hUF.2 (heq ▸ hzU)⟩
  rw [key]
  apply ts.sUnion_mem
  intro U hU
  rw [HFSet.mem_sep] at hU
  exact hU.1

/-- Si cada singleton es cerrado, entonces T₁. -/
theorem HFTopSpace.T1_of_singletons_closed {ts : HFTopSpace}
    (h : ∀ {x : HFSet}, x ∈ ts.X → ts.isClosed (HFSet.singleton x)) :
    ts.isT1 := by
  intro x y hx hy hne
  -- U = X \ {y} (abierto, contiene x, no contiene y)
  -- V = X \ {x} (abierto, contiene y, no contiene x)
  refine ⟨HFSet.setminus ts.X (HFSet.singleton y),
          HFSet.setminus ts.X (HFSet.singleton x),
          h hy, h hx, ?_, ?_, ?_, ?_⟩
  · -- x ∈ X \ {y}: hx y x ≠ y
    rw [HFSet.mem_setminus, HFSet.mem_singleton]
    exact ⟨hx, hne⟩
  · -- y ∉ X \ {y}
    intro hmem
    rw [HFSet.mem_setminus, HFSet.mem_singleton] at hmem
    exact hmem.2 rfl
  · -- y ∈ X \ {x}: hy y y ≠ x
    rw [HFSet.mem_setminus, HFSet.mem_singleton]
    exact ⟨hy, hne.symm⟩
  · -- x ∉ X \ {x}
    intro hmem
    rw [HFSet.mem_setminus, HFSet.mem_singleton] at hmem
    exact hmem.2 rfl

/-- T₁ si y solo si cada singleton es cerrado. -/
theorem HFTopSpace.T1_iff_singletons_closed {ts : HFTopSpace} :
    ts.isT1 ↔ ∀ {x : HFSet}, x ∈ ts.X → ts.isClosed (HFSet.singleton x) :=
  ⟨fun h _ hx => HFTopSpace.singletons_closed_of_T1 h hx,
   fun h => HFTopSpace.T1_of_singletons_closed h⟩

/-! ## Implicaciones: T₃ → T₂ y T₄ → T₃ -/

/-- T₃ implica T₂. -/
theorem HFTopSpace.T3_implies_T2 {ts : HFTopSpace} (h : ts.isT3) : ts.isT2 := by
  obtain ⟨hT1, hReg⟩ := h
  intro x y hx hy hne
  -- {y} es cerrado por T₁
  have hcl : ts.isClosed (HFSet.singleton y) :=
    HFTopSpace.singletons_closed_of_T1 hT1 hy
  -- x ∉ {y} pues x ≠ y
  have hxny : x ∉ HFSet.singleton y :=
    fun hmem => hne ((HFSet.mem_singleton x y).mp hmem)
  -- Regularidad: ∃ U, V abiertos disjuntos con x ∈ U y {y} ⊆ V
  obtain ⟨U, V, hUτ, hVτ, hxU, hsingV, hdisj⟩ := hReg hx hcl hxny
  -- y ∈ V pues {y} ⊆ V
  have hyV : y ∈ V := hsingV y ((HFSet.mem_singleton y y).mpr rfl)
  exact ⟨U, V, hUτ, hVτ, hxU, hyV, hdisj⟩

/-- T₄ implica T₃. -/
theorem HFTopSpace.T4_implies_T3 {ts : HFTopSpace} (h : ts.isT4) : ts.isT3 := by
  obtain ⟨hT1, hNorm⟩ := h
  refine ⟨hT1, ?_⟩
  intro x A hx hclA hxA
  -- {x} es cerrado por T₁
  have hclx : ts.isClosed (HFSet.singleton x) :=
    HFTopSpace.singletons_closed_of_T1 hT1 hx
  -- {x} ∩ A = ∅ pues x ∉ A
  have hdisj : HFSet.inter (HFSet.singleton x) A = HFSet.empty := by
    apply HFSet.extensionality
    intro z
    rw [HFSet.mem_inter, HFSet.mem_singleton]
    exact ⟨fun ⟨heq, hzA⟩ => absurd (heq ▸ hzA) hxA,
           fun hmem => absurd hmem (HFSet.not_mem_empty z)⟩
  -- Normalidad: ∃ U, V abiertos disjuntos con {x} ⊆ U y A ⊆ V
  obtain ⟨U, V, hUτ, hVτ, hsingU, hAV, hUVdisj⟩ := hNorm hclx hclA hdisj
  -- x ∈ U pues {x} ⊆ U
  have hxU : x ∈ U := hsingU x ((HFSet.mem_singleton x x).mpr rfl)
  exact ⟨U, V, hUτ, hVτ, hxU, hAV, hUVdisj⟩

/-! ## Implicaciones transitivas -/

/-- T₄ implica T₂ (vía T₃). -/
theorem HFTopSpace.T4_implies_T2 {ts : HFTopSpace} (h : ts.isT4) : ts.isT2 :=
  HFTopSpace.T3_implies_T2 (HFTopSpace.T4_implies_T3 h)

/-- T₃ implica T₁. -/
theorem HFTopSpace.T3_implies_T1 {ts : HFTopSpace} (h : ts.isT3) : ts.isT1 :=
  HFTopSpace.T2_implies_T1 (HFTopSpace.T3_implies_T2 h)

/-- T₄ implica T₁. -/
theorem HFTopSpace.T4_implies_T1 {ts : HFTopSpace} (h : ts.isT4) : ts.isT1 :=
  HFTopSpace.T2_implies_T1 (HFTopSpace.T4_implies_T2 h)

/-- T₂ implica T₀. -/
theorem HFTopSpace.T2_implies_T0 {ts : HFTopSpace} (h : ts.isT2) : ts.isT0 :=
  HFTopSpace.T1_implies_T0 (HFTopSpace.T2_implies_T1 h)

/-- T₃ implica T₀. -/
theorem HFTopSpace.T3_implies_T0 {ts : HFTopSpace} (h : ts.isT3) : ts.isT0 :=
  HFTopSpace.T1_implies_T0 (HFTopSpace.T3_implies_T1 h)

/-- T₄ implica T₀. -/
theorem HFTopSpace.T4_implies_T0 {ts : HFTopSpace} (h : ts.isT4) : ts.isT0 :=
  HFTopSpace.T1_implies_T0 (HFTopSpace.T4_implies_T1 h)

end HFTopology
