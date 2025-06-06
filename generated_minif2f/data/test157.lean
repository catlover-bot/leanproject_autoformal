import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Nat

theorem problem_statement : ∀ (i m o : ℕ), (i ≠ 0 ∧ m ≠ 0 ∧ o ≠ 0) → (i * m * o = 2001) → (i + m + o ≤ 671) :=
begin
  intros i m o h_nonzero h_prod,
  have h_pos : i > 0 ∧ m > 0 ∧ o > 0,
  { exact ⟨Nat.pos_of_ne_zero h_nonzero.1, Nat.pos_of_ne_zero h_nonzero.2.1, Nat.pos_of_ne_zero h_nonzero.2.2⟩ },
  have h_bound : i * m * o ≥ i + m + o,
  { linarith [h_pos.1, h_pos.2.1, h_pos.2.2] },
  linarith [h_prod, h_bound],
end

end Nat