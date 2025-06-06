import Mathlib.Data.Int.Basic

theorem functional_equation_solution (f : ℤ → ℤ) :
  (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔
  (∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) :=
begin
  split,
  { intro h,
    by_cases h0 : ∀ z, f z = 0,
    { left, exact h0 },
    { right,
      have h1 : ∃ z, f z ≠ 0, from not_forall.mp h0,
      obtain ⟨z0, hz0⟩ := h1,
      have h2 : ∀ z, f z = 2 * z + f 0,
      { intro z,
        specialize h z 0,
        rw [mul_zero, add_zero, f 0] at h,
        have h3 : f (2 * z) = f (f z) - 2 * f 0,
        { linarith },
        specialize h 0 z,
        rw [mul_zero, zero_add, f 0] at h,
        have h4 : 2 * f z = f (f z) - f 0,
        { linarith },
        have h5 : f (f z) = 2 * z + f 0,
        { linarith },
        exact h5 },
      use f 0,
      exact h2 } },
  { rintros (h | ⟨c, hc⟩),
    { intros a b,
      rw h a,
      rw h b,
      simp },
    { intros a b,
      rw [hc (2 * a), hc b, hc (a + b)],
      ring } }
end