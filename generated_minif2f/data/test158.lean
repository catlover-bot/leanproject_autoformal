import data.real.basic
import data.finset
import analysis.special_functions.trigonometric

open real
open finset

theorem amc12a_2021_p19
(S : finset ℝ)
(h₀ : ∀ (x : ℝ), x ∈ S ↔ 0 ≤ x ∧ x ≤ pi ∧ sin (pi / 2 * cos x) = cos (pi / 2 * sin x)) :
S.card = 2 :=
begin
  have h₁ : ∀ x, 0 ≤ x ∧ x ≤ pi → sin (pi / 2 * cos x) = cos (pi / 2 * sin x) ↔ cos (pi / 2 * cos x) = sin (pi / 2 * sin x),
  { intros x hx,
    split,
    { intro h,
      rw [← sin_pi_div_two_sub, ← cos_pi_div_two_sub] at h,
      exact h },
    { intro h,
      rw [← sin_pi_div_two_sub, ← cos_pi_div_two_sub],
      exact h } },
  
  have h₂ : ∀ x, 0 ≤ x ∧ x ≤ pi → sin (pi / 2 * cos x) = cos (pi / 2 * sin x) ↔ x = pi / 4 ∨ x = 3 * pi / 4,
  { intros x hx,
    rw h₁ x hx,
    split,
    { intro h,
      have : cos (pi / 2 * cos x) = sin (pi / 2 * sin x) ↔ pi / 2 * cos x = pi / 2 * sin x ∨ pi / 2 * cos x = pi - pi / 2 * sin x,
      { apply cos_eq_sin_iff },
      rw this at h,
      cases h,
      { left,
        field_simp at h,
        exact eq_of_mul_eq_mul_left pi_pos.ne' h },
      { right,
        field_simp at h,
        exact eq_of_mul_eq_mul_left pi_pos.ne' h } },
    { intro h,
      cases h,
      { rw h,
        simp },
      { rw h,
        simp } } },

  have h₃ : ∀ x, x ∈ S ↔ x = pi / 4 ∨ x = 3 * pi / 4,
  { intro x,
    rw h₀ x,
    split,
    { rintro ⟨hx₀, hx₁, hx₂⟩,
      exact (h₂ x ⟨hx₀, hx₁⟩).mp hx₂ },
    { intro h,
      cases h,
      { exact ⟨le_of_lt pi_div_four_pos, le_of_lt pi_div_four_lt_pi, (h₂ (pi / 4) ⟨le_of_lt pi_div_four_pos, le_of_lt pi_div_four_lt_pi⟩).mpr (or.inl rfl)⟩ },
      { exact ⟨le_of_lt three_pi_div_four_pos, le_of_lt three_pi_div_four_lt_pi, (h₂ (3 * pi / 4) ⟨le_of_lt three_pi_div_four_pos, le_of_lt three_pi_div_four_lt_pi⟩).mpr (or.inr rfl)⟩ } } },

  have h₄ : S = {pi / 4, 3 * pi / 4},
  { ext x,
    rw h₃ x,
    simp },

  rw h₄,
  simp,
end