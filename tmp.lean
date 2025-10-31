import Mathlib

-- 示例 1：如果 a = b，那么 a + 1 = b + 1
theorem add_one_eq {a b : Nat} (h : a = b) : a + 1 = b + 1 := by
  -- 用 have 引入中间等式（这里通过 rw h 获得）
  have h' : a + 1 = b + 1 := by
    sorry
  exact h'
