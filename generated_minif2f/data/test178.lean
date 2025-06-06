import Mathlib.Data.Int.Basic

namespace Int

theorem problem (f : ℤ → ℤ) :
  (∀ a b, f (2 * a) + (2 * f b) = f (f (a + b))) ↔ (∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) :=
begin
  split,
  { intro h,
    by_cases h0 : ∀ z, f z = 0,
    { left, exact h0 },
    { right,
      push_neg at h0,
      obtain ⟨z0, hz0⟩ := h0,
      have h1 : ∀ z, f z = 2 * z + (f 0 - 0),
      { intro z,
        specialize h z 0,
        rw [mul_zero, add_zero, f 0] at h,
        have h2 : f (2 * z) = 2 * f z + f 0,
        { linarith },
        specialize h z z0,
        rw [mul_add, add_assoc, ←h2, ←h2] at h,
        linarith },
      use f 0,
      exact h1 } },
  { rintros (h | ⟨c, hc⟩),
    { intros a b,
      rw [h a, h b, h (a + b)],
      ring },
    { intros a b,
      rw [hc (2 * a), hc b, hc (a + b)],
      ring } }
end

end Int