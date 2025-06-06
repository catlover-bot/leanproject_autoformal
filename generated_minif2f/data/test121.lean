import Mathlib.Data.Int.Basic
import Mathlib.Tactic

open Int

theorem problem (f : ℤ → ℤ) :
  (∀ n, odd n → f n = n^2) ∧ (∀ n, even n → f n = n^2 - 4*n - 1) → f 4 = -1 :=
begin
  intro h,
  have h_even := h.2,
  specialize h_even 4,
  have h4_even : even 4 := by norm_num,
  rw h4_even at h_even,
  rw h_even,
  norm_num,
end