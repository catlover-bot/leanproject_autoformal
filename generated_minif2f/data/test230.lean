import Mathlib.Data.Real.Basic

open Real

theorem abs_sum_geq_15 (x p : ℝ) (f : ℝ → ℝ) :
  (0 < p ∧ p < 15) →
  (p ≤ x ∧ x ≤ 15) →
  (f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) →
  15 ≤ f x :=
begin
  intros hp hx hf,
  have h1 : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15), from hf,
  cases le_or_lt x p with hxp hpx,
  { exfalso, linarith [hx.1, hxp] },
  cases le_or_lt x 15 with hx15 hx15,
  { cases le_or_lt p x with hpx hx,
    { -- Case 1: x = p
      have : x = p, from le_antisymm hpx hx,
      rw [this, abs_zero, abs_of_nonpos, abs_of_nonpos] at h1,
      { linarith [hp.2] },
      { linarith [hp.2] },
      { linarith [hp.2] } },
    { -- Case 2: x = 15
      have : x = 15, from le_antisymm hx15 hx,
      rw [this, abs_of_nonpos, abs_zero, abs_of_nonpos] at h1,
      { linarith [hp.2] },
      { linarith [hp.2] },
      { linarith [hp.2] } } },
  { -- Case 3: p < x < 15
    rw [abs_of_pos, abs_of_neg, abs_of_neg] at h1,
    { linarith },
    { linarith },
    { linarith },
    { linarith } }
end