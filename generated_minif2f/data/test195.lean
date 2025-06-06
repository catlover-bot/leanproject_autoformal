import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Complex

theorem amc12a_2021_p12
  (a b c d : ℝ)
  (f : ℂ → ℂ)
  (h₀ : ∀ z, f z = z^6 - 10 * z^5 + a * z^4 + b * z^3 + c * z^2 + d * z + 16)
  (h₁ : ∀ z, f z = 0 → (z.im = 0 ∧ 0 < z.re ∧ ↑(int.floor z.re) = z.re)) :
  b = 88 := 
begin
  have h₂ : ∀ z : ℂ, f z = 0 → z ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := 
  begin
    intros z hz,
    obtain ⟨hz_im, hz_re_pos, hz_re_int⟩ := h₁ z hz,
    rw [← int.cast_inj, int.cast_floor, int.cast_ofNat] at hz_re_int,
    have : z.re ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    { norm_num at hz_re_int,
      exact hz_re_int },
    exact this,
  end,

  have h₃ : ∀ n : ℕ, (n : ℂ) ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} → f n = 0,
  { intros n hn,
    rw h₀ n,
    norm_num,
    fin_cases hn; norm_num },

  have h₄ : ∀ n : ℕ, n ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} → n^6 - 10 * n^5 + a * n^4 + b * n^3 + c * n^2 + d * n + 16 = 0,
  { intros n hn,
    specialize h₃ n hn,
    rw h₀ n at h₃,
    exact h₃ },

  have h₅ : ∑ n in {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, n^3 = 880,
  { norm_num },

  have h₆ : ∑ n in {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, n^6 - 10 * n^5 + a * n^4 + b * n^3 + c * n^2 + d * n + 16 = 0,
  { apply finset.sum_eq_zero,
    intros n hn,
    exact h₄ n hn },

  have h₇ : ∑ n in {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, n^3 = 880,
  { norm_num },

  have h₈ : b * 880 = 0,
  { rw ← h₆,
    ring_nf,
    linarith },

  have h₉ : b = 88,
  { linarith },

  exact h₉,
end