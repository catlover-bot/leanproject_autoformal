import Mathlib.Data.Nat.Basic

theorem imo_1982_p1
  (f : ℕ → ℕ)
  (h₀ : ∀ m n, (0 < m ∧ 0 < n) → f (m + n) - f m - f n = 0 ∨ f (m + n) - f m - f n = 1)
  (h₁ : f 2 = 0)
  (h₂ : 0 < f 3)
  (h₃ : f 9999 = 3333) :
  f 1982 = 660 :=
begin
  have h₄ : ∀ n, 0 < n → f (2 * n) = 2 * f n,
  { intros n hn,
    induction n with n ih,
    { exfalso, exact Nat.lt_irrefl 0 hn },
    { cases n,
      { rw [Nat.mul_zero, Nat.mul_zero, h₁] },
      { have h := h₀ (n + 1) (n + 1) ⟨Nat.succ_pos n, Nat.succ_pos n⟩,
        cases h,
        { rw [Nat.add_self, h, ih (Nat.succ_pos n)] },
        { exfalso,
          have : f (2 * (n + 1)) = 2 * f (n + 1),
          { rw [Nat.add_self, h, ih (Nat.succ_pos n)] },
          rw [this, Nat.add_self, h] at h₂,
          linarith } } } },
  have h₅ : ∀ n, 0 < n → f (3 * n) = 3 * f n,
  { intros n hn,
    induction n with n ih,
    { exfalso, exact Nat.lt_irrefl 0 hn },
    { cases n,
      { rw [Nat.mul_zero, Nat.mul_zero, h₁] },
      { have h := h₀ (2 * n + 1) (n + 1) ⟨Nat.succ_pos _, Nat.succ_pos n⟩,
        cases h,
        { rw [Nat.add_assoc, h, ih (Nat.succ_pos n)] },
        { exfalso,
          have : f (3 * (n + 1)) = 3 * f (n + 1),
          { rw [Nat.add_assoc, h, ih (Nat.succ_pos n)] },
          rw [this, Nat.add_assoc, h] at h₂,
          linarith } } } },
  have h₆ : f 9999 = 3 * f 3333,
  { rw [h₅ 3333 (by norm_num)] },
  have h₇ : f 3333 = 1111,
  { linarith },
  have h₈ : f 1982 = 2 * f 991,
  { rw [h₄ 991 (by norm_num)] },
  have h₉ : f 991 = 330,
  { have h := h₀ 991 991 ⟨by norm_num, by norm_num⟩,
    cases h,
    { rw [h, h₈, h₇],
      linarith },
    { exfalso,
      rw [h, h₈, h₇] at h₂,
      linarith } },
  rw [h₈, h₉],
  norm_num,
end