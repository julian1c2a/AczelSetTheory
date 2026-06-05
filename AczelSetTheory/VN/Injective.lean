import AczelSetTheory.VN.Basic
open Peano
namespace VN

theorem vN_injective : Function.Injective vN := by
  intro m
  induction m with
  | zero =>
    intro n hn
    cases n with
    | zero => rfl
    | succ k =>
      simp only [vN_zero, vN_succ] at hn
      exact absurd hn.symm (HFSet.succ_ne_empty (vN k))
  | succ m' ihm =>
    intro n hn
    cases n with
    | zero =>
      simp only [vN_succ, vN_zero] at hn
      exact absurd hn (HFSet.succ_ne_empty (vN m'))
    | succ k =>
      simp only [vN_succ] at hn
      exact congrArg ℕ₀.succ (ihm (HFSet.succ_injective _ _ hn))

end VN