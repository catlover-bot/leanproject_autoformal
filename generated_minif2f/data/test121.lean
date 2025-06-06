import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

open Int

theorem function_value_at_4 (f : ℤ → ℤ) :
  (∀ n, odd n → f n = n^2) ∧ (∀ n, even n → f n = n^2 - 4*n - 1) → f 4 = -1 :=
begin
  intro h,
  have h_even : even 4 := by norm_num,
  have h₁ := h.2 4 h_even,
  calc
    f 4 = 4^2 - 4*4 - 1 : h₁
    ... = 16 - 16 - 1   : by ring
    ... = -1            : by ring,
end