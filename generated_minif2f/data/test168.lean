import Mathlib.Data.Real.Basic

namespace UniqueExistence

variable {f : ℕ → ℝ → ℝ}

theorem exists_unique_a (h : ∀ a n, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1) :
  ∃! a, ∀ n, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 :=
begin
  obtain ⟨a, ha⟩ : ∃ a, ∀ n, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1,
  { use 0, intro n, exact h 0 n },
  use a,
  split,
  { exact ha },
  { intros b hb,
    have hfa : ∀ n, 0 < n → f n a < 1 := λ n hn, (ha n hn).2.2,
    have hfb : ∀ n, 0 < n → f n b < 1 := λ n hn, (hb n hn).2.2,
    have hfab : ∀ n, 0 < n → f n a = f n b,
    { intros n hn,
      apply le_antisymm,
      { have : f n a < f (n + 1) a := (ha n hn).2.1,
        have : f n b < f (n + 1) b := (hb n hn).2.1,
        linarith [hfa n hn, hfb n hn] },
      { have : f n b < f (n + 1) b := (hb n hn).2.1,
        have : f n a < f (n + 1) a := (ha n hn).2.1,
        linarith [hfa n hn, hfb n hn] } },
    specialize hfab 1 (by norm_num),
    exact hfab }
end

end UniqueExistence