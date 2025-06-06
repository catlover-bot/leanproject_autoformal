import Mathlib.Data.Nat.Digits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace AMC12A2003P5

theorem amc12a_2003_p5
  (A M C : ℕ)
  (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
  (h₁ : nat.of_digits 10 [0,1,C,M,A] + nat.of_digits 10 [2,1,C,M,A] = 123422) :
  A + M + C = 14 :=
by
  have h₂ : nat.of_digits 10 [0,1,C,M,A] = 1000 * C + 100 * M + 10 * A := by norm_num
  have h₃ : nat.of_digits 10 [2,1,C,M,A] = 20000 + 1000 * C + 100 * M + 10 * A := by norm_num
  rw [h₂, h₃] at h₁
  linarith

end AMC12A2003P5