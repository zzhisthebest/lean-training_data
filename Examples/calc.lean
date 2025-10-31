import Mathlib
/-- 证明恒等式: (a + b)^2 = a^2 + 2 * a * b + b^2 -/
theorem square_sum : (a + b)^2 = a^2 + 2 * a * b + b^2 := by
  -- 展开 (a + b)^2 为 (a + b) * (a + b)
  rw [pow_two]

  -- 应用左分配律
  rw [add_mul]

  -- 再次应用右分配律
  rw [mul_add, mul_add]

  -- 替换乘积为平方项
  rw [← pow_two a, ← pow_two b]

  -- 使用乘法交换律 (b * a -> a * b)
  rw [mul_comm b a]

  -- 使用加法结合律，重排项
  rw [add_assoc]

  -- 合并 a * b + a * b 为 2 * (a * b)
  rw [two_mul]

  ring
