import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Nat

theorem nat_power_eq_cases :
  ∀ (x y : ℕ), (0 < x ∧ 0 < y) → (x^(y^2) = y^x) → (x, y) = (1, 1) ∨ (x, y) = (16, 2) ∨ (x, y) = (27, 3) :=
begin
  intros x y hpos heq,
  cases x with x',
  { exfalso, exact Nat.not_lt_zero 0 hpos.1 },
  cases y with y',
  { exfalso, exact Nat.not_lt_zero 0 hpos.2 },
  cases x' with x'',
  { cases y' with y'',
    { left, refl },
    { exfalso, simp at heq, linarith } },
  cases y' with y'',
  { exfalso, simp at heq, linarith },
  have hxy : x'' + 1 = 1 ∨ x'' + 1 = 16 ∨ x'' + 1 = 27,
  { have : x'' + 1 > 0 := by linarith,
    have : y'' + 1 > 0 := by linarith,
    have : (x'' + 1) ^ ((y'' + 1) ^ 2) = (y'' + 1) ^ (x'' + 1) := heq,
    interval_cases x'' + 1; interval_cases y'' + 1; try {linarith}; try {norm_num at this}; try {linarith} },
  cases hxy,
  { left, subst hxy, interval_cases y'' + 1; try {linarith}; try {norm_num at heq}; try {linarith} },
  { right, left, subst hxy, interval_cases y'' + 1; try {linarith}; try {norm_num at heq}; try {linarith} },
  { right, right, subst hxy, interval_cases y'' + 1; try {linarith}; try {norm_num at heq}; try {linarith} }
end