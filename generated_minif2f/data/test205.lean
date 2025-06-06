import data.finset
import data.real.basic
import data.int.basic

open finset

theorem card_of_set (S : finset ℤ) (h : ∀ (x : ℤ), x ∈ S ↔ ↑(abs x) < 3 * real.pi) : S.card = 19 :=
begin
  -- Calculate the approximate value of 3 * π
  have hpi : 3 * real.pi ≈ 9.42477 := by norm_num,
  
  -- Determine the range of integers x such that |x| < 3 * π
  have h_range : ∀ x : ℤ, ↑(abs x) < 3 * real.pi ↔ -9 < x ∧ x < 10,
  { intro x,
    rw [abs_lt, int.cast_lt, int.cast_lt],
    split,
    { intro h,
      split; linarith },
    { rintro ⟨h₁, h₂⟩,
      linarith } },

  -- Define the set of integers from -9 to 9
  let T : finset ℤ := Icc (-9) 9,

  -- Show that S is exactly the set of integers from -9 to 9
  have hS : S = T,
  { ext x,
    rw [h, h_range],
    exact mem_Icc },

  -- Calculate the cardinality of the set T
  have hT_card : T.card = 19,
  { rw [card_Icc, int.to_nat_sub_of_le],
    { norm_num },
    { linarith } },

  -- Conclude that S.card = 19
  rw hS,
  exact hT_card,
end