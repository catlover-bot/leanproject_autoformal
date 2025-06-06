import Mathlib.Data.Int.Basic

lemma int_theorem : ∀ (x : ℤ), x = 4 → (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11 :=
begin
  intro x,
  intro hx,
  rw hx,
  norm_num,
end