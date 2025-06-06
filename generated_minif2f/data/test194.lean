import Real

open Real

theorem mathd_algebra_270
  (f : ℝ → ℝ)
  (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
  f (f 1) = 3 / 7 :=
begin
  have h₁ : f 1 = 1 / (1 + 2), from h₀ 1 (by norm_num),
  have h₂ : f 1 = 1 / 3, by rw [h₁, add_comm, add_assoc, add_comm 1 2, add_assoc, add_comm 2 1],
  have h₃ : f (1 / 3) = 1 / ((1 / 3) + 2), from h₀ (1 / 3) (by norm_num),
  have h₄ : f (1 / 3) = 1 / (1 / 3 + 6 / 3), by rw [h₃, ←add_div, div_self (by norm_num : 3 ≠ 0)],
  have h₅ : f (1 / 3) = 1 / (7 / 3), by rw [h₄, add_comm, add_assoc, add_comm (1 / 3) (6 / 3)],
  have h₆ : f (1 / 3) = 3 / 7, by rw [h₅, div_div_eq_div_mul, mul_comm, div_self (by norm_num : 7 ≠ 0)],
  rw [h₂, h₆],
end