import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

open Classical

noncomputable section

def f : ℕ → ℝ → ℝ
| 1, x => x
| n + 1, x => f n x * (f n x + 1 / n)

theorem exists_unique_a : ∃! a : ℝ, ∀ n : ℕ, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 :=
begin
  let a := 1 / 2,
  use a,
  split,
  { intro n,
    intro hn,
    induction n with n ih,
    { exfalso, exact Nat.not_lt_zero _ hn },
    { cases n,
      { simp [f], norm_num },
      { have hfn : 0 < f (n + 1) a ∧ f (n + 1) a < 1 := ih (Nat.succ_pos _),
        have hfn_pos : 0 < f (n + 1) a := hfn.1,
        have hfn_lt_one : f (n + 1) a < 1 := hfn.2,
        simp [f],
        split,
        { apply mul_pos hfn_pos,
          linarith [hfn_lt_one] },
        split,
        { apply mul_lt_mul_of_pos_left,
          { linarith [hfn_lt_one] },
          { exact hfn_pos } },
        { apply mul_lt_one_of_nonneg_of_lt_one_left,
          { linarith [hfn_lt_one] },
          { linarith [hfn_lt_one] } } } } },
  { intros b hb,
    have hfa : ∀ n, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := hb,
    have hfb : ∀ n, 0 < n → 0 < f n b ∧ f n b < f (n + 1) b ∧ f (n + 1) b < 1 := hb,
    by_contra hne,
    wlog hlt : a < b using [a b, b a],
    { have hfa1 : 0 < f 1 a := (hfa 1 (by norm_num)).1,
      have hfb1 : 0 < f 1 b := (hfb 1 (by norm_num)).1,
      simp [f] at hfa1 hfb1,
      linarith },
    { exact this b a hfb hfa (ne.symm hne) (lt_of_le_of_ne (le_of_not_lt hlt) hne) } }
end