```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Solution

theorem solve_problem : ∀ (a b : ℕ), (1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9) ∧ (10 * a + b)^3 = 912673 → a + b = 16 :=
begin
  intros a b h,
  rcases h with ⟨⟨ha1, ha9, hb9⟩, h_eq⟩,
  have h_cases : a = 9 ∧ b = 7,
  { norm_num at h_eq,
    have h1 : 10 * a + b = 97,
    { norm_num,
      linarith },
    have h2 : 10 * a + b = 97 := by linarith,
    have h3 : a = 9 := by linarith,
    have h4 : b = 7 := by linarith,
    exact ⟨h3, h4⟩ },
  cases h_cases with ha hb,
  linarith,
end

end Solution
```