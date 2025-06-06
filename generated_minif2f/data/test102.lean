import Mathlib.Algebra.GroupPower.Basic

theorem example_theorem (f : ℕ → ℕ → ℕ) (h : ∀ x y, f x (y + 1) = 2^(f x y + 3) - 3) : 
  ∀ y, f 4 (y + 1) = 2^(f 4 y + 3) - 3 :=
begin
  intro y,
  apply h,
end