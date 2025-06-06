import Mathlib.Data.Nat.Prime

theorem not_prime_implies_large_n : ∀ (n : ℕ), ¬ nat.prime (7 + 30 * n) → 6 ≤ n := by
  intro n h
  cases n with
  | zero =>
    norm_num at h
  | succ n =>
    cases n with
    | zero =>
      norm_num at h
    | succ n =>
      cases n with
      | zero =>
        norm_num at h
      | succ n =>
        cases n with
        | zero =>
          norm_num at h
        | succ n =>
          cases n with
          | zero =>
            norm_num at h
          | succ n =>
            cases n with
            | zero =>
              norm_num at h
            | succ n =>
              apply Nat.succ_le_succ
              apply Nat.succ_le_succ
              apply Nat.succ_le_succ
              apply Nat.succ_le_succ
              apply Nat.succ_le_succ
              apply Nat.zero_le