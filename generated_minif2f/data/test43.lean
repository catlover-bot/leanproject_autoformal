```lean
import Mathlib.Data.Nat.Basic

theorem sum_divisible_by_7 : (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 = 0 := by
  have h : 2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006 = 7 * 2003 := by
    norm_num
  rw [h]
  norm_num
```