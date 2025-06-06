import data.rat.basic
import data.finset
import algebra.big_operators.basic

open_locale big_operators

theorem aime_1984_p1
  (u : ℕ → ℚ)
  (h₀ : ∀ n, u (n + 1) = u n + 1)
  (h₁ : ∑ k in finset.range 98, u k.succ = 137) :
  ∑ k in finset.range 49, u (2 * k.succ) = 93 :=
begin
  -- Step 1: Express u(n) in terms of u(0)
  have h₂ : ∀ n, u n = u 0 + n,
  { intro n,
    induction n with n ih,
    { refl },
    { rw [h₀, ih, add_assoc] } },

  -- Step 2: Use h₁ to find u(0)
  have h₃ : ∑ k in finset.range 98, (u 0 + (k + 1)) = 137,
  { rw h₁,
    congr,
    ext,
    rw h₂ },

  -- Simplify the sum
  rw finset.sum_add_distrib at h₃,
  rw finset.sum_const at h₃,
  rw finset.card_range at h₃,
  have h₄ : ∑ k in finset.range 98, (k + 1) = 98 * 99 / 2,
  { rw finset.sum_range_succ,
    norm_num },

  -- Solve for u(0)
  have h₅ : 98 * u 0 + 98 * 99 / 2 = 137,
  { rw [h₃, h₄] },
  have h₆ : u 0 = 137 - 98 * 99 / 2,
  { linarith },

  -- Step 3: Calculate the target sum
  have h₇ : ∑ k in finset.range 49, u (2 * k.succ) = ∑ k in finset.range 49, (u 0 + 2 * k.succ),
  { congr,
    ext,
    rw h₂ },

  rw finset.sum_add_distrib at h₇,
  rw finset.sum_const at h₇,
  rw finset.card_range at h₇,
  have h₈ : ∑ k in finset.range 49, (2 * (k + 1)) = 2 * ∑ k in finset.range 49, (k + 1),
  { rw finset.sum_mul },
  have h₉ : ∑ k in finset.range 49, (k + 1) = 49 * 50 / 2,
  { rw finset.sum_range_succ,
    norm_num },

  rw [h₈, h₉] at h₇,
  have h₁₀ : 49 * u 0 + 2 * (49 * 50 / 2) = 93,
  { rw h₇,
    linarith [h₆] },

  exact h₁₀,
end