import data.real.basic
import data.finset
import analysis.special_functions.trigonometric

open finset
open real

theorem amc12a_2021_p19
(S : finset ℝ)
(h₀ : ∀ (x : ℝ), x ∈ S ↔ 0 ≤ x ∧ x ≤ pi ∧ sin (pi / 2 * cos x) = cos (pi / 2 * sin x)) :
S.card = 2 :=
begin
  have h₁ : ∀ x, 0 ≤ x ∧ x ≤ pi ∧ sin (pi / 2 * cos x) = cos (pi / 2 * sin x) ↔ x = pi / 4 ∨ x = 3 * pi / 4,
  { intro x,
    split,
    { intro hx,
      have hcos : cos (pi / 2 * cos x) = sin (pi / 2 * sin x),
      { rw [← sin_pi_div_two_sub, sub_eq_iff_eq_add, add_comm, ← cos_pi_div_two_sub],
        exact hx.2.2 },
      have hsin : sin (pi / 2 * cos x) = cos (pi / 2 * sin x),
      { exact hx.2.2 },
      have hcos_eq : cos (pi / 2 * cos x) = cos (pi / 2 * sin x),
      { rw [← hsin, hcos] },
      have hsin_eq : sin (pi / 2 * cos x) = sin (pi / 2 * sin x),
      { rw [hsin, hcos] },
      rw [cos_eq_cos_iff, sin_eq_sin_iff] at hcos_eq hsin_eq,
      cases hcos_eq with hcos_eq1 hcos_eq2,
      { cases hsin_eq with hsin_eq1 hsin_eq2,
        { left,
          linarith },
        { right,
          linarith } },
      { cases hsin_eq with hsin_eq1 hsin_eq2,
        { right,
          linarith },
        { left,
          linarith } } },
    { intro hx,
      cases hx,
      { split,
        { linarith },
        { split,
          { linarith },
          { rw [hx, cos_pi_div_four, sin_pi_div_four],
            norm_num } } },
      { split,
        { linarith },
        { split,
          { linarith },
          { rw [hx, cos_three_pi_div_four, sin_three_pi_div_four],
            norm_num } } } } },
  have h₂ : S = {pi / 4, 3 * pi / 4},
  { ext x,
    rw [mem_insert, mem_singleton, h₀, h₁] },
  rw h₂,
  simp,
end