import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod

open Real
open Finset

theorem aime_1983_p3
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (x^2 + (18 * x + 30) - 2 * sqrt (x^2 + (18 * x + 45))))
  (h₁ : fintype (f⁻¹' {0})) :
  ∏ x in (f⁻¹' {0}).to_finset, x = 20 :=
begin
  have h₂ : ∀ x, f x = 0 ↔ x^2 + 18 * x + 30 = 2 * sqrt (x^2 + 18 * x + 45),
  { intro x,
    rw h₀ x,
    simp },
  have h₃ : ∀ x, f x = 0 ↔ (x + 9)^2 = 45,
  { intro x,
    rw h₂ x,
    split,
    { intro h,
      rw [← sqrt_inj (by linarith) (by linarith), pow_two, pow_two] at h,
      linarith },
    { intro h,
      rw [← sqrt_inj (by linarith) (by linarith), pow_two, pow_two],
      linarith } },
  have h₄ : f⁻¹' {0} = {x | (x + 9)^2 = 45},
  { ext x,
    rw [set.mem_preimage, set.mem_set_of_eq, h₃ x] },
  have h₅ : f⁻¹' {0} = {-9 + sqrt 45, -9 - sqrt 45},
  { ext x,
    rw [h₄, set.mem_set_of_eq],
    split,
    { intro h,
      rw [← sqrt_inj (by linarith) (by linarith), pow_two, pow_two] at h,
      cases h,
      { left, linarith },
      { right, linarith } },
    { intro h,
      cases h,
      { rw h, linarith },
      { rw h, linarith } } },
  have h₆ : (f⁻¹' {0}).to_finset = {-9 + sqrt 45, -9 - sqrt 45}.to_finset,
  { rw h₅ },
  rw h₆,
  simp only [prod_insert, prod_singleton, mem_singleton, not_false_iff],
  have h₇ : (-9 + sqrt 45) * (-9 - sqrt 45) = 20,
  { ring_nf,
    rw [pow_two, sqrt_mul_self (by linarith)],
    norm_num },
  exact h₇,
end