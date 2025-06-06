import data.rat.basic
import data.nat.basic
import data.finset
import algebra.big_operators.basic

open_locale big_operators

theorem aime_1984_p1
  (u : ℕ → ℚ)
  (h₀ : ∀ n, u (n + 1) = u n + 1)
  (h₁ : ∑ k in finset.range 98, u k.succ = 137) :
  ∑ k in finset.range 49, u (2 * k.succ) = 93 :=
begin
  have h₂ : ∀ n, u n = u 0 + n,
  { intro n,
    induction n with n ih,
    { refl },
    { rw [h₀, ih, add_assoc] } },
  have h₃ : ∑ k in finset.range 98, (u 0 + k + 1) = 137,
  { rw h₂,
    convert h₁,
    ext,
    rw [nat.succ_eq_add_one, add_assoc] },
  have h₄ : ∑ k in finset.range 98, (u 0 + k + 1) = 98 * u 0 + ∑ k in finset.range 98, (k + 1),
  { rw finset.sum_add_distrib,
    congr' 1,
    rw finset.sum_const,
    simp },
  have h₅ : ∑ k in finset.range 98, (k + 1) = 98 * 99 / 2,
  { rw finset.sum_range_succ,
    norm_num },
  have h₆ : 98 * u 0 + 98 * 99 / 2 = 137,
  { rw [←h₄, h₃] },
  have h₇ : u 0 = -49,
  { linarith },
  have h₈ : ∑ k in finset.range 49, (u 0 + (2 * k + 1)) = 49 * u 0 + ∑ k in finset.range 49, (2 * k + 1),
  { rw finset.sum_add_distrib,
    congr' 1,
    rw finset.sum_const,
    simp },
  have h₉ : ∑ k in finset.range 49, (2 * k + 1) = 49 * 49,
  { rw finset.sum_range_succ,
    norm_num },
  rw [h₂, h₈, h₉, h₇],
  norm_num,
end