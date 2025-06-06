import Mathlib.Data.Nat.Basic

namespace FunctionProof

variable (f : ℕ → ℕ)

theorem f_eq_n_for_positive_n (h₀ : ∀ n, 0 < n → 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1)) :
  ∀ n, 0 < n → f n = n :=
begin
  intro n,
  induction n with k ih,
  { intro h, exfalso, exact Nat.not_lt_zero 0 h },
  { intro h,
    cases k,
    { have : 0 < f 1 := h₀ 1 (Nat.succ_pos 0),
      have : f (f 1) < f 2 := h₁ 1 (Nat.succ_pos 0),
      have : f 1 = 1,
      { by_contradiction h,
        have : f 1 > 1 := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt this) h,
        have : f (f 1) < f 1 := by linarith,
        exact Nat.lt_irrefl _ this },
      exact this },
    { have ih' : f (k + 1) = k + 1 := ih (Nat.succ_pos k),
      have : f (f (k + 1)) < f (k + 2) := h₁ (k + 1) (Nat.succ_pos k),
      by_contradiction h,
      have : f (k + 2) > k + 2 := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (h₀ (k + 2) (Nat.succ_pos _))) h,
      have : f (f (k + 1)) < f (k + 1) := by linarith,
      exact Nat.lt_irrefl _ this } }
end

end FunctionProof