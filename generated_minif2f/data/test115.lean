import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem gcd_polynomial_bound (n : ℕ) (p : ℕ → ℕ) 
  (h : ∀ x, p x = x^2 - x + 41) 
  (gcd_cond : 1 < gcd (p n) (p (n+1))) : 
  41 ≤ n :=
begin
  have h_pn : p n = n^2 - n + 41 := h n,
  have h_pn1 : p (n+1) = (n+1)^2 - (n+1) + 41 := h (n+1),
  rw [h_pn, h_pn1] at gcd_cond,
  have : gcd (n^2 - n + 41) ((n+1)^2 - (n+1) + 41) = gcd (n^2 - n + 41) (2*n + 1),
  { ring_nf,
    rw [add_assoc, add_comm (n^2 - n), add_assoc, add_comm 41, add_assoc],
    ring },
  rw this at gcd_cond,
  have : gcd (n^2 - n + 41) (2*n + 1) ≤ 41,
  { apply gcd_le_right },
  linarith,
end