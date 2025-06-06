import data.finset
import data.nat.basic
import algebra.big_operators

open finset
open_locale big_operators

theorem sum_last_digits_div_by_3 : 
  ∑ k in finset.filter (λ x, 3 ∣ x) (finset.Icc 1 49), (k % 10) = 78 :=
begin
  let s := finset.filter (λ x, 3 ∣ x) (finset.Icc 1 49),
  have hs : s = {3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48},
  { ext x,
    simp only [mem_filter, mem_Icc, and_comm, and_assoc, and.left_comm],
    split,
    { rintro ⟨⟨hx1, hx2⟩, hx3⟩,
      obtain ⟨n, rfl⟩ := hx3,
      simp only [nat.mul_div_cancel_left _ (nat.succ_pos 2)] at hx1 hx2,
      interval_cases n; simp [hx1, hx2] },
    { intro hx,
      simp only [mem_insert, mem_singleton] at hx,
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl;
      simp } },
  rw hs,
  norm_num,
end