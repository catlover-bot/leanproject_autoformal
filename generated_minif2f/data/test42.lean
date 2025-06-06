import data.finset.basic
import data.nat.basic

open finset

theorem divisible_by_20_count : finset.card (finset.filter (λ x, 20 ∣ x) (finset.Icc 15 85)) = 4 :=
begin
  -- Define the set of integers from 15 to 85
  let s := finset.Icc 15 85,
  -- Filter the set for numbers divisible by 20
  let t := finset.filter (λ x, 20 ∣ x) s,
  -- Calculate the specific numbers that are divisible by 20
  have h : t = {20, 40, 60, 80},
  { ext x,
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton],
    split,
    { rintro ⟨⟨hx1, hx2⟩, hx3⟩,
      interval_cases x with hx,
      all_goals { simp [hx3] } },
    { rintro (rfl | rfl | rfl | rfl);
      simp [mem_Icc] } },
  -- Conclude by calculating the cardinality of the filtered set
  rw h,
  simp,
end