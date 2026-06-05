import AczelSetTheory.VN.Basic
open Peano
namespace VN

theorem isNat_vN (n : ℕ₀) : HFSet.isNat (vN n) := by
  induction n with
  | zero  => exact HFSet.isNat_zero
  | succ k ih => simp only [vN_succ]; exact HFSet.isNat_succ ih

theorem vN_mem_range {A : HFSet} (h : HFSet.isNat A) : ∃ n : ℕ₀, vN n = A := by
  induction h with
  | zero      => exact ⟨𝟘, vN_zero⟩
  | succ _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨σ k, by rw [vN_succ, hk]⟩

theorem isNat_iff_range (A : HFSet) : HFSet.isNat A ↔ ∃ n : ℕ₀, vN n = A :=
  ⟨vN_mem_range, fun ⟨n, hn⟩ => hn ▸ isNat_vN n⟩

end VN