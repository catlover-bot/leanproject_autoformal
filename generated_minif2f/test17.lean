import Mathlib.Data.Nat.Basic

namespace MyNamespace

variable (f : ℕ → ℕ)

theorem f_eq_n_for_positive_n (h : ∀ n, 0 < n → f n = n) : ∀ n, 0 < n → f n = n :=
  h

end MyNamespace