import AczelSetTheory.Topology.Basic
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Powerset

namespace HFTopology

/-!
# Sistema de entornos y equivalencia con la topología de abiertos

Un **sistema de entornos** asigna a cada punto `x ∈ X` una colección `𝒩(x)` de
subconjuntos de `X` (los *entornos* de `x`) que satisface los axiomas de Hausdorff:

1. Cada entorno `N ∈ 𝒩(x)` contiene a `x`.
2. `X` es entorno de cada punto.
3. Cada superconjunto (en X) de un entorno es entorno.
4. Intersección finita de entornos es entorno.
5. (Interior) Cada entorno contiene un abierto que contiene a `x` y es entorno
   de cada uno de sus puntos.

El axioma 5 es el que garantiza la equivalencia con la definición de abiertos.
-/

structure HFNeighborSpace where
  /-- Conjunto base del espacio. -/
  X         : HFSet
  /-- `𝒩 x` es la colección de entornos de `x`. -/
  𝒩         : HFSet → HFSet
  /-- Cada entorno está contenido en `X`. -/
  𝒩_sub     : ∀ {x N : HFSet}, x ∈ X → N ∈ 𝒩 x → N ⊆ X
  /-- `x` pertenece a cada uno de sus entornos. -/
  point_mem : ∀ {x N : HFSet}, x ∈ X → N ∈ 𝒩 x → x ∈ N
  /-- `X` es entorno de cada punto. -/
  univ_mem  : ∀ {x : HFSet}, x ∈ X → X ∈ 𝒩 x
  /-- Herencia hacia arriba: si `N ∈ 𝒩(x)` y `N ⊆ M ⊆ X`, entonces `M ∈ 𝒩(x)`. -/
  up_closed : ∀ {x N M : HFSet}, x ∈ X → N ∈ 𝒩 x → N ⊆ M → M ⊆ X → M ∈ 𝒩 x
  /-- Estabilidad por intersección finita: `N, M ∈ 𝒩(x) → N ∩ M ∈ 𝒩(x)`. -/
  inter_mem : ∀ {x N M : HFSet}, x ∈ X → N ∈ 𝒩 x → M ∈ 𝒩 x → HFSet.inter N M ∈ 𝒩 x
  /-- Axioma de interior: cada entorno contiene un abierto (entorno de cada uno de sus puntos). -/
  interior  : ∀ {x N : HFSet}, x ∈ X → N ∈ 𝒩 x →
                ∃ M, M ∈ 𝒩 x ∧ M ⊆ N ∧ ∀ {y : HFSet}, y ∈ M → N ∈ 𝒩 y

/-!
## De topología de abiertos a sistema de entornos

Dado `ts : HFTopSpace`, se define `𝒩_ts(x) = {N ⊆ X | ∃ U ∈ τ, x ∈ U ∧ U ⊆ N}`.
-/

def HFTopSpace.toNeighborSpace (ts : HFTopSpace) : HFNeighborSpace where
  X         := ts.X
  𝒩         := fun x =>
                  HFSet.sep (HFSet.powerset ts.X)
                    (fun N => ∃ U, U ∈ ts.τ ∧ x ∈ U ∧ U ⊆ N)
  𝒩_sub     := by
    intro x N _ hN
    rw [HFSet.mem_sep, HFSet.mem_powerset] at hN
    exact hN.1
  point_mem := by
    intro x N hx hN
    rw [HFSet.mem_sep] at hN
    obtain ⟨_, U, _, hxU, hUsub⟩ := hN
    exact hUsub x hxU
  univ_mem  := by
    intro x hx
    rw [HFSet.mem_sep]
    exact ⟨(HFSet.mem_powerset ts.X ts.X).mpr (fun z hz => hz),
           ts.X, ts.univ_mem, hx, HFSet.subset_refl ts.X⟩
  up_closed := by
    intro x N M _ hN hNM hMX
    rw [HFSet.mem_sep] at hN ⊢
    obtain ⟨_, U, hUτ, hxU, hUsub⟩ := hN
    exact ⟨(HFSet.mem_powerset ts.X M).mpr hMX,
           U, hUτ, hxU, HFSet.subset_trans U N M hUsub hNM⟩
  inter_mem := by
    intro x N M hx hN hM
    rw [HFSet.mem_sep] at hN hM ⊢
    obtain ⟨hNsub, U, hUτ, hxU, hUN⟩ := hN
    obtain ⟨hMsub, V, hVτ, hxV, hVM⟩ := hM
    have hNsub' : N ⊆ ts.X := (HFSet.mem_powerset ts.X N).mp hNsub
    have hMsub' : M ⊆ ts.X := (HFSet.mem_powerset ts.X M).mp hMsub
    have hINM : HFSet.inter N M ⊆ ts.X :=
      HFSet.subset_trans _ N ts.X (HFSet.inter_subset_left N M) hNsub'
    refine ⟨(HFSet.mem_powerset ts.X _).mpr hINM, ?_⟩
    refine ⟨HFSet.inter U V, ts.inter_mem hUτ hVτ, ?_, ?_⟩
    · rw [HFSet.mem_inter]; exact ⟨hxU, hxV⟩
    · have hIUV_N : HFSet.inter U V ⊆ N :=
        HFSet.subset_trans _ U N (HFSet.inter_subset_left U V) hUN
      have hIUV_M : HFSet.inter U V ⊆ M :=
        HFSet.subset_trans _ V M (HFSet.inter_subset_right U V) hVM
      exact HFSet.subset_inter _ N M hIUV_N hIUV_M
  interior  := by
    intro x N _ hN
    rw [HFSet.mem_sep] at hN
    obtain ⟨hNsub, U, hUτ, hxU, hUN⟩ := hN
    refine ⟨U, ?_, hUN, ?_⟩
    · rw [HFSet.mem_sep]
      exact ⟨(HFSet.mem_powerset ts.X U).mpr (ts.τ_sub hUτ),
             U, hUτ, hxU, HFSet.subset_refl U⟩
    · intro y hyU
      rw [HFSet.mem_sep]
      exact ⟨hNsub,
             U, hUτ, hyU, hUN⟩

/-!
## De sistema de entornos a topología de abiertos

Dado `ns : HFNeighborSpace`, se define `τ_ns = {U ⊆ X | ∀ x ∈ U, U ∈ 𝒩(x)}`.
-/

def HFNeighborSpace.toTopSpace (ns : HFNeighborSpace) : HFTopSpace where
  X          := ns.X
  τ          := HFSet.sep (HFSet.powerset ns.X) (fun U => ∀ x, x ∈ U → U ∈ ns.𝒩 x)
  τ_sub      := by
    intro U hU
    rw [HFSet.mem_sep, HFSet.mem_powerset] at hU
    exact hU.1
  empty_mem  := by
    rw [HFSet.mem_sep]
    exact ⟨(HFSet.mem_powerset ns.X HFSet.empty).mpr (HFSet.empty_subset ns.X),
           fun x hx => absurd hx (HFSet.not_mem_empty x)⟩
  univ_mem   := by
    rw [HFSet.mem_sep]
    exact ⟨(HFSet.mem_powerset ns.X ns.X).mpr (HFSet.subset_refl ns.X),
           fun x hx => ns.univ_mem hx⟩
  sUnion_mem := by
    intro F hF
    rw [HFSet.subset_iff] at hF
    rw [HFSet.mem_sep]
    constructor
    · rw [HFSet.mem_powerset]
      intro z hz
      rw [HFSet.mem_sUnion] at hz
      obtain ⟨U, hUF, hzU⟩ := hz
      have hUsep := hF U hUF
      rw [HFSet.mem_sep, HFSet.mem_powerset] at hUsep
      exact hUsep.1 z hzU
    · intro x hx
      rw [HFSet.mem_sUnion] at hx
      obtain ⟨U, hUF, hxU⟩ := hx
      have hUsep := hF U hUF
      rw [HFSet.mem_sep, HFSet.mem_powerset] at hUsep
      have hxX : x ∈ ns.X := hUsep.1 x hxU
      have hUsep2 : U ∈ ns.𝒩 x := hUsep.2 x hxU
      apply ns.up_closed hxX hUsep2
      · intro z hzU
        rw [HFSet.mem_sUnion]; exact ⟨U, hUF, hzU⟩
      · intro z hz
        rw [HFSet.mem_sUnion] at hz
        obtain ⟨V, hVF, hzV⟩ := hz
        have hVsep := hF V hVF
        rw [HFSet.mem_sep, HFSet.mem_powerset] at hVsep
        exact hVsep.1 z hzV
  inter_mem  := by
    intro U V hU hV
    rw [HFSet.mem_sep] at hU hV ⊢
    constructor
    · rw [HFSet.mem_powerset]
      intro z hz
      rw [HFSet.mem_inter] at hz
      exact (HFSet.mem_powerset ns.X U).mp hU.1 z hz.1
    · intro x hx
      rw [HFSet.mem_inter] at hx
      have hxX : x ∈ ns.X := (HFSet.mem_powerset ns.X U).mp hU.1 x hx.1
      exact ns.inter_mem hxX (hU.2 x hx.1) (hV.2 x hx.2)

/-!
## Equivalencia

La composición `ts.toNeighborSpace.toTopSpace` recupera la topología original,
y `ns.toTopSpace.toNeighborSpace` recupera el sistema de entornos original.
-/

/-- La topología recuperada desde los entornos tiene los mismos abiertos. -/
theorem toNeighborSpace_toTopSpace_τ (ts : HFTopSpace) :
    ts.toNeighborSpace.toTopSpace.τ = ts.τ := by
  apply HFSet.extensionality
  intro U
  simp only [HFNeighborSpace.toTopSpace, HFTopSpace.toNeighborSpace]
  rw [HFSet.mem_sep]
  constructor
  · rintro ⟨_, hopen⟩
    -- U = sUnion {τ ’ | V ⊆ U}: para x ∈ U hay V ∈ τ con x ∈ V ⊆ U
    have hU_eq : U = HFSet.sUnion (HFSet.sep ts.τ (fun V => V ⊆ U)) := by
      apply HFSet.extensionality; intro x
      rw [HFSet.mem_sUnion]
      constructor
      · intro hxU
        have hxN := hopen x hxU
        rw [HFSet.mem_sep] at hxN
        obtain ⟨_, V, hVτ, hxV, hVU⟩ := hxN
        exact ⟨V, by rw [HFSet.mem_sep]; exact ⟨hVτ, hVU⟩, hxV⟩
      · rintro ⟨V, hVsep, hxV⟩
        rw [HFSet.mem_sep] at hVsep
        exact hVsep.2 x hxV
    rw [hU_eq]
    apply ts.sUnion_mem
    intro V hV
    rw [HFSet.mem_sep] at hV
    exact hV.1
  · intro hUτ
    exact ⟨(HFSet.mem_powerset ts.X U).mpr (ts.τ_sub hUτ),
           fun x hx => by
             rw [HFSet.mem_sep]
             exact ⟨(HFSet.mem_powerset ts.X U).mpr (ts.τ_sub hUτ),
                    U, hUτ, hx, HFSet.subset_refl U⟩⟩

/-- El sistema de entornos recuperado desde la topología coincide con el original. -/
theorem toTopSpace_toNeighborSpace_𝒩 (ns : HFNeighborSpace) (x : HFSet) (hx : x ∈ ns.X) :
    ns.toTopSpace.toNeighborSpace.𝒩 x = ns.𝒩 x := by
  apply HFSet.extensionality
  intro N
  simp only [HFTopSpace.toNeighborSpace, HFNeighborSpace.toTopSpace]
  rw [HFSet.mem_sep]
  constructor
  · rintro ⟨hNX, U, hUτ, hxU, hUN⟩
    rw [HFSet.mem_sep] at hUτ
    -- U ∈ 𝒩(x) (de hUτ.2), N ⊇ U y N ⊆ X (de hNX)
    exact ns.up_closed hx (hUτ.2 x hxU) hUN ((HFSet.mem_powerset ns.X N).mp hNX)
  · intro hN
    -- La meta ya está expandida por el rw [HFSet.mem_sep] externo:
    -- N ∈ HFSet.powerset ns.X ∧ ∃ U, U ∈ sep(...) ∧ x ∈ U ∧ U ⊆ N
    refine ⟨(HFSet.mem_powerset ns.X N).mpr (ns.𝒩_sub hx hN), ?_⟩
    -- Testigo: V = {y ∈ X | N ∈ 𝒩(y)}
    refine ⟨HFSet.sep ns.X (fun y => N ∈ ns.𝒩 y), ?_, ?_, ?_⟩
    · -- V ∈ τ_ns: HFSet.sep ns.X (...) ∈ HFSet.sep (powerset ns.X) (...)
      rw [HFSet.mem_sep]
      constructor
      · rw [HFSet.mem_powerset]
        intro y hy; rw [HFSet.mem_sep] at hy; exact hy.1
      · intro y hy
        rw [HFSet.mem_sep] at hy
        obtain ⟨hyX, hNy⟩ := hy
        obtain ⟨M, hMy, _, hMint⟩ := ns.interior hyX hNy
        apply ns.up_closed hyX hMy
        · intro z hzM
          rw [HFSet.mem_sep]
          exact ⟨ns.𝒩_sub hyX hMy z hzM, hMint hzM⟩
        · intro z hz; rw [HFSet.mem_sep] at hz; exact hz.1
    · -- x ∈ V
      rw [HFSet.mem_sep]; exact ⟨hx, hN⟩
    · -- V ⊆ N
      intro y hy; rw [HFSet.mem_sep] at hy; exact ns.point_mem hy.1 hy.2

end HFTopology
