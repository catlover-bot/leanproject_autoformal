import Mathlib.Data.Rat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finset

open Finset

theorem problem_statement (a : ℚ) (S : Finset ℝ) :
  (∀ (x : ℝ), x ∈ S ↔ (⌊x⌋ : ℝ) * (x - ⌊x⌋) = a * x ^ 2) →
  (∑ k in S, k = 420) →
  (a.denom + a.num = 929) :=
begin
  intros hS hSum,
  have h_empty : S = ∅,
  { ext x,
    specialize hS x,
    rw [mem_empty, iff_false],
    intro hx,
    have : (⌊x⌋ : ℝ) * (x - ⌊x⌋) = a * x ^ 2 := hS.mp hx,
    have : x = 0,
    { linarith },
    rw this at hx,
    simp at hx,
    exact hx },
  rw h_empty at hSum,
  simp at hSum,
  exfalso,
  linarith,
end