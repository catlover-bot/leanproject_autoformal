import Mathlib.Data.Nat.GCD.Basic

theorem mathd_numbertheory_435
  (k : ℕ)
  (h₀ : 0 < k)
  (h₁ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 3) = 1)
  (h₂ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 2) = 1)
  (h₃ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 1) = 1) :
  5 ≤ k :=
begin
  by_contra h,
  have hk : k < 5 := Nat.lt_of_not_ge h,
  interval_cases k with hk,
  { -- k = 1
    specialize h₁ 0,
    specialize h₂ 0,
    specialize h₃ 0,
    norm_num at h₁ h₂ h₃,
    contradiction },
  { -- k = 2
    specialize h₂ 0,
    norm_num at h₂,
    contradiction },
  { -- k = 3
    specialize h₁ 0,
    norm_num at h₁,
    contradiction },
  { -- k = 4
    specialize h₂ 0,
    norm_num at h₂,
    contradiction },
end