import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Finset

theorem mathd_algebra_215
(S : finset ℝ)
(h₀ : ∀ (x : ℝ), x ∈ S ↔ (x + 3)^2 = 121) :
∑ k in S, k = -6 :=
begin
  have h₁ : ∀ x, x ∈ S ↔ x = 8 ∨ x = -14,
  { intro x,
    rw h₀,
    split,
    { intro h,
      have : x + 3 = 11 ∨ x + 3 = -11 := by linarith,
      cases this,
      { left, linarith },
      { right, linarith } },
    { intro h,
      cases h,
      { linarith },
      { linarith } } },
  have h₂ : S = {8, -14},
  { ext x,
    rw [mem_insert, mem_singleton, h₁] },
  rw h₂,
  simp,
end