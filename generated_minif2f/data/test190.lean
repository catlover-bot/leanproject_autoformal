import Mathlib.Data.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.AbsoluteValue

open Finset

theorem mathd_algebra_196
(S : finset ℝ)
(h₀ : ∀ (x : ℝ), x ∈ S ↔ abs (2 - x) = 3) :
∑ k in S, k = 4 :=
begin
  have h₁ : S = {5, -1},
  { ext x,
    simp only [mem_insert, mem_singleton],
    rw h₀ x,
    rw abs_eq_iff,
    split,
    { rintro (h | h),
      { left, linarith },
      { right, linarith } },
    { rintro (h | h),
      { linarith },
      { linarith } } },
  rw h₁,
  simp,
end