import Mathlib.Data.Int.Basic

theorem not_even_iff_sum_squares_multiple_of_8 (a b : ℤ) :
  ¬ ((∃ i j, a = 2 * i ∧ b = 2 * j) ↔ (∃ k, a^2 + b^2 = 8 * k)) :=
begin
  intro h,
  have h1 : (∃ i j, a = 2 * i ∧ b = 2 * j) → (∃ k, a^2 + b^2 = 8 * k),
  { intro h2,
    obtain ⟨i, j, ha, hb⟩ := h2,
    use (i^2 + j^2),
    rw [ha, hb],
    ring },
  have h2 : (∃ k, a^2 + b^2 = 8 * k) → (∃ i j, a = 2 * i ∧ b = 2 * j),
  { intro h3,
    obtain ⟨k, hk⟩ := h3,
    have : a^2 + b^2 ≡ 0 [MOD 8] := by { rw hk, exact int.modeq_zero_iff_dvd.mpr (dvd_refl _) },
    have : a^2 ≡ 0 [MOD 4] ∧ b^2 ≡ 0 [MOD 4],
    { split;
      { have := int.modeq_of_dvd (int.dvd_add_left (int.dvd_refl (b^2))),
        rw [int.modeq_zero_iff_dvd, int.modeq_zero_iff_dvd] at this,
        exact this } },
    have : a ≡ 0 [MOD 2] ∧ b ≡ 0 [MOD 2],
    { split;
      { apply int.modeq_zero_iff_dvd.mpr,
        apply int.dvd_of_pow_dvd_pow 2,
        rw int.modeq_zero_iff_dvd,
        exact this.left } },
    obtain ⟨i, hi⟩ := int.exists_eq_mul_right_of_dvd this.left,
    obtain ⟨j, hj⟩ := int.exists_eq_mul_right_of_dvd this.right,
    use [i, j, hi, hj] },
  have : (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ (∃ k, a^2 + b^2 = 8 * k) := ⟨h1, h2⟩,
  contradiction
end