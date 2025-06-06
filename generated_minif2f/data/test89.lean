import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Int

theorem even_n_implication (n : ℕ) (h_even : even n) 
  (h_eq : (↑n - 2)^2 + ↑n^2 + (↑n + 2)^2 = (12296:ℤ)) : 
  ((↑n - 2) * ↑n * (↑n + 2)) / 8 = (32736:ℤ) :=
begin
  -- Since n is even, express n as 2k
  obtain ⟨k, rfl⟩ := h_even,
  -- Substitute n = 2k into the equation
  have h_squares : (2 * k - 2)^2 + (2 * k)^2 + (2 * k + 2)^2 = 12296,
  { simpa using h_eq },
  -- Simplify the equation
  ring_nf at h_squares,
  -- Solve for k
  have : 12 * k^2 + 8 = 12296,
  { linarith },
  have : 12 * k^2 = 12288,
  { linarith },
  have k_value : k = 32,
  { linarith },
  -- Verify the product condition
  have h_product : ((2 * k - 2) * (2 * k) * (2 * k + 2)) / 8 = 32736,
  { rw k_value,
    norm_num },
  exact h_product,
end