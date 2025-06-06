import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace MyNamespace

theorem problem_statement : ∀ (x y : ℕ), (x % 3 = 2) → (y % 5 = 4) → (x % 10 = y % 10) → 14 ≤ x :=
begin
  intros x y hx hy hxy,
  have hx_mod_10 : x % 10 = 2 ∨ x % 10 = 5 ∨ x % 10 = 8,
  { cases hx with h1 h2,
    { exact Or.inl h1 },
    { cases h2 with h3 h4,
      { exact Or.inr (Or.inl h3) },
      { exact Or.inr (Or.inr h4) } } },
  have hy_mod_10 : y % 10 = 4 ∨ y % 10 = 9,
  { cases hy with h1 h2,
    { exact Or.inl h1 },
    { exact Or.inr h2 } },
  cases hx_mod_10 with hx2 hx5_8,
  { rw [hx2] at hxy,
    cases hy_mod_10 with hy4 hy9,
    { rw [hy4] at hxy, norm_num at hxy },
    { rw [hy9] at hxy, norm_num at hxy } },
  { cases hx5_8 with hx5 hx8,
    { rw [hx5] at hxy,
      cases hy_mod_10 with hy4 hy9,
      { rw [hy4] at hxy, norm_num at hxy },
      { rw [hy9] at hxy, norm_num at hxy } },
    { rw [hx8] at hxy,
      cases hy_mod_10 with hy4 hy9,
      { rw [hy4] at hxy, norm_num at hxy },
      { rw [hy9] at hxy, norm_num at hxy } } }
end

end MyNamespace