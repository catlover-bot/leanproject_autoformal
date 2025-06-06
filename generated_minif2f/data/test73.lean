import Mathlib.Data.Nat.Basic

theorem mathd_numbertheory_5
(n : ℕ)
(h₀ : 10 ≤ n)
(h₁ : ∃ x, x^2 = n)
(h₂ : ∃ t, t^3 = n) :
64 ≤ n :=
begin
  rcases h₁ with ⟨x, rfl⟩,
  rcases h₂ with ⟨t, ht⟩,
  have h : x^2 = t^3 := ht,
  have : x = t * t := by {
    have h' : x^2 = (t * t) * t := by rw [←h, mul_assoc],
    exact nat.eq_of_mul_eq_mul_left (nat.zero_lt_succ _) h',
  },
  have : x = t * t := this,
  have : t * t * t = n := ht,
  have : t * t * t = t^3 := by rw [←mul_assoc, mul_comm t, mul_assoc],
  rw this at ht,
  have : t^3 = n := ht,
  have : t^3 ≥ 64 := by {
    have : t ≥ 4 := by {
      by_contradiction h,
      push_neg at h,
      interval_cases t with h,
      { norm_num at this },
      { norm_num at this },
      { norm_num at this },
    },
    exact nat.pow_le_pow_of_le_left this 3,
  },
  exact this,
end