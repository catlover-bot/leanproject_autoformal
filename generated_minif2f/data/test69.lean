import data.finset
import algebra.big_operators

open finset

theorem mathd_algebra_215
(S : finset ℝ)
(h₀ : ∀ (x : ℝ), x ∈ S ↔ (x + 3)^2 = 121) :
∑ k in S, k = -6 :=
begin
  have h₁ : ∀ x, (x + 3)^2 = 121 ↔ x = 8 ∨ x = -14,
  { intro x,
    split,
    { intro h,
      have : x + 3 = 11 ∨ x + 3 = -11 := by linarith [eq_or_eq_neg_of_sq_eq_sq _ _ h],
      cases this,
      { left, linarith },
      { right, linarith } },
    { intro h,
      cases h,
      { rw h, norm_num },
      { rw h, norm_num } } },
  have h₂ : S = {8, -14},
  { ext x,
    rw [h₀, h₁],
    simp },
  rw h₂,
  simp,
end