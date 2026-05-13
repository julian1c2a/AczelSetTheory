import AczelSetTheory.VN.Injective
import AczelSetTheory.PList.Omega0
open Peano
namespace VN

theorem mem_vN_iff_lt (m n : ℕ₀) : vN m ∈ vN n ↔ m < n := by
  induction n with
  | zero =>
    simp only [vN_zero]
    constructor
    · exact fun h => absurd h (HFSet.not_mem_empty _)
    · intro h
      simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_zero] at h
      omega
  | succ k ih =>
    rw [vN_succ, HFSet.mem_succ]
    constructor
    · rintro (h | h)
      · have hlt := ih.mp h
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hlt ⊢
        omega
      · have heq := vN_injective h
        simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ, PList.Omega0.ψ_eq_iff] at heq ⊢
        omega
    · intro h
      simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at h
      by_cases heq : m = k
      · exact Or.inr (congrArg vN heq)
      · apply Or.inl
        apply ih.mpr
        have hne : Ψ m ≠ Ψ k := fun h => heq ((PList.Omega0.ψ_eq_iff m k).mpr h)
        simp only [PList.Omega0.ψ_lt_iff]
        omega

theorem vN_mono (m n : ℕ₀) (h : m ≤ n) : vN m ⊆ vN n := by
  induction n generalizing m with
  | zero =>
    have hm : m = 𝟘 := by
      simp only [PList.Omega0.ψ_eq_iff, PList.Omega0.ψ_le_iff,
                  PList.Omega0.ψ_zero] at h ⊢
      omega
    subst hm
    intro x hx; exact hx
  | succ k ih =>
    by_cases heq : m = σ k
    · subst heq; intro x hx; exact hx
    · have hle : m ≤ k := by
        simp only [PList.Omega0.ψ_le_iff, PList.Omega0.ψ_succ,
                   PList.Omega0.ψ_eq_iff] at h heq ⊢
        omega
      intro x hx
      exact (mem_vN_succ x k).mpr (Or.inl (ih m hle x hx))

theorem vN_le_iff_subset (m n : ℕ₀) : m ≤ n ↔ vN m ⊆ vN n := by
  constructor
  · intro hle; exact vN_mono m n hle
  · intro hsub
    rcases Nat.lt_or_ge (Ψ n) (Ψ m) with hlt | hge
    · exfalso
      have hmn : vN n ∈ vN m :=
        (mem_vN_iff_lt n m).mpr ((PList.Omega0.ψ_lt_iff n m).mpr hlt)
      have hnn : vN n ∈ vN n := hsub (vN n) hmn
      have hlt2 : n < n := (mem_vN_iff_lt n n).mp hnn
      simp only [PList.Omega0.ψ_lt_iff] at hlt2; omega
    · exact (PList.Omega0.ψ_le_iff m n).mpr hge

end VN