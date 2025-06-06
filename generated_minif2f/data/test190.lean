import data.real.basic
import data.finset

open finset

theorem mathd_algebra_196
(S : finset ℝ)
(h₀ : ∀ (x : ℝ), x ∈ S ↔ abs (2 - x) = 3) :
∑ k in S, k = 4 :=
begin
  have h₁ : S = {-1, 5},
  { ext x,
    simp only [mem_insert, mem_singleton],
    split,
    { intro hx,
      rw h₀ at hx,
      rw abs_eq at hx,
      cases hx,
      { right,
        linarith },
      { left,
        linarith } },
    { intro hx,
      rw h₀,
      cases hx,
      { rw hx,
        simp },
      { rw hx,
        simp } } },
  rw h₁,
  simp,
end