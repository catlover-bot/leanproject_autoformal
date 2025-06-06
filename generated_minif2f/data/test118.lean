import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Gcd

theorem mathd_numbertheory_435
  (k : ℕ)
  (h₀ : 0 < k)
  (h₁ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 3) = 1)
  (h₂ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 2) = 1)
  (h₃ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 1) = 1) :
  5 ≤ k :=
by
  by_contra hk
  push_neg at hk
  have h₄ : k ≤ 4 := Nat.le_of_lt_succ hk
  interval_cases k with hk
  case h_1 =>
    specialize h₁ 0
    simp at h₁
    contradiction
  case h_2 =>
    specialize h₂ 0
    simp at h₂
    contradiction
  case h_3 =>
    specialize h₃ 0
    simp at h₃
    contradiction
  case h_4 =>
    specialize h₁ 0
    simp at h₁
    contradiction