import RealInReal.Natural

structure Rational where
  num: Int
  denom: Nat

  denom_non_zero: denom ≠ 0
  denom_eq_one_if_num_eq_zero: num = 0 → denom = 1
  num_denom_coprime: num ≠ 0 → Coprime num denom

instance : LE Rational where
  le a b := a.num * b.denom ≤ b.num * a.denom

instance : LT Rational where
  lt a b := a.num * b.denom < b.num * a.denom
