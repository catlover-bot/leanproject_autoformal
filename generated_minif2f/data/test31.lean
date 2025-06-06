import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem nat_exponentiation_solution (x y : ℕ) (hxy : 0 < x ∧ 0 < y) (h : x^(y^2) = y^x) :
  (x, y) = (1, 1) ∨ (x, y) = (16, 2) ∨ (x, y) = (27, 3) :=
begin
  cases hxy with hx hy,
  cases x,
  { exfalso, exact Nat.lt_irrefl 0 hx },
  cases y,
  { exfalso, exact Nat.lt_irrefl 0 hy },
  cases x with x',
  { left, cases y with y',
    { exfalso, exact Nat.lt_irrefl 0 hy },
    { simp, exact Nat.pow_eq_one_iff.mp h } },
  cases y with y',
  { exfalso, exact Nat.lt_irrefl 0 hy },
  cases x' with x'',
  { cases y' with y'',
    { left, simp },
    { exfalso, simp at h, exact Nat.succ_ne_zero _ h } },
  cases y' with y'',
  { exfalso, simp at h, exact Nat.succ_ne_zero _ h },
  have h1 : x.succ.succ^(y.succ.succ^2) = y.succ.succ^x.succ.succ := h,
  have h2 : x.succ.succ^(y.succ.succ * y.succ.succ) = y.succ.succ^x.succ.succ := h1,
  have h3 : x.succ.succ^(y.succ.succ * y.succ.succ) = y.succ.succ^x.succ.succ := h2,
  have h4 : x.succ.succ = y.succ.succ ∨ x.succ.succ ≠ y.succ.succ := em (x.succ.succ = y.succ.succ),
  cases h4,
  { left, rw h4 at h3, simp at h3, exact Nat.pow_eq_one_iff.mp h3 },
  { have h5 : x.succ.succ^(y.succ.succ * y.succ.succ) = y.succ.succ^x.succ.succ := h3,
    have h6 : x.succ.succ^(y.succ.succ * y.succ.succ) = y.succ.succ^x.succ.succ := h5,
    have h7 : x.succ.succ = 16 ∧ y.succ.succ = 2 ∨ x.succ.succ = 27 ∧ y.succ.succ = 3,
    { by_cases hxy : x.succ.succ = 16 ∧ y.succ.succ = 2,
      { left, exact hxy },
      { right, have hxy' : x.succ.succ = 27 ∧ y.succ.succ = 3,
        { split; linarith },
        exact hxy' } },
    cases h7,
    { right, left, exact h7 },
    { right, right, exact h7 } }
end