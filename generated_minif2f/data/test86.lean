import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

theorem mersenne_prime_implication : ∀ (n : ℕ), 0 < n → nat.prime (2^n - 1) → nat.prime n :=
begin
  intros n hn h,
  by_contra hnp,
  have h1 : 1 < n := lt_of_not_ge (λ hge, hnp (nat.prime_iff.2 ⟨hn, λ d hd, (hge hd).elim⟩)),
  have h2 : 2 ≤ n := le_of_lt h1,
  have h3 : 2^n - 1 = (2^n - 1) * 1 := by ring,
  have h4 : 2^n - 1 = (2^(n - 1) - 1) * (2 + 1) := by {
    rw [←pow_succ, Nat.sub_add_cancel h2],
    ring,
  },
  have h5 : 2^(n - 1) - 1 > 1 := by {
    apply lt_of_le_of_ne,
    { apply Nat.sub_le_sub_right,
      apply pow_le_pow,
      exact le_refl 2,
      exact Nat.pred_le_pred h2 },
    { intro h6,
      rw [h6, sub_self] at h4,
      have h7 : 2^n - 1 = 0 := by linarith,
      exact Nat.not_prime_zero h h7 },
  },
  have h6 : 2^n - 1 = (2^(n - 1) - 1) * 3 := by linarith,
  rw h6 at h,
  exact h.not_prime_mul h5 (by norm_num),
end