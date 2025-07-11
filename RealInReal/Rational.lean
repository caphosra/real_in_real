import RealInReal.Natural

structure NumPair where
  num: Int
  denom: Nat

  denom_non_zero: denom ≠ 0

instance : LE NumPair where
  le a b := a.num * b.denom ≤ b.num * a.denom

instance : LT NumPair where
  lt a b := a.num * b.denom < b.num * a.denom

instance NumPairSetoid : Setoid NumPair where
  r := fun a b => a.num * b.denom = b.num * a.denom
  iseqv := by
    constructor
    case refl =>
      intros x
      rfl
    case symm =>
      intros x y h
      rw [Int.mul_comm]
      rw [h]
      rw [Int.mul_comm]
    case trans =>
      intros x y z h1 h2
      have h1_mod: x.num * ↑y.denom * ↑z.denom = y.num * ↑x.denom * ↑z.denom := by
        rw [h1]
      have h2_mod: y.num * ↑z.denom * ↑x.denom = z.num * ↑y.denom * ↑x.denom := by
        rw [h2]
      have: y.num * ↑x.denom * ↑z.denom = y.num * ↑z.denom * ↑x.denom := by
        rw [Int.mul_assoc]
        rw [Int.mul_assoc]
        conv =>
          lhs
          conv =>
            rhs
            rw [Int.mul_comm]
      have: y.denom * (x.num * ↑z.denom) = y.denom * (z.num * ↑x.denom) := by
        rw [←h1_mod] at this
        rw [h2_mod] at this
        conv at this =>
          lhs
          conv =>
            lhs
            rw [Int.mul_comm]
          rw [Int.mul_assoc]
        conv at this =>
          rhs
          conv =>
            lhs
            rw [Int.mul_comm]
          rw [Int.mul_assoc]
        exact this
      have y_denom_zero: (↑y.denom: Int) ≠ 0 := by
        rw [Int.ofNat_ne_zero]
        exact y.denom_non_zero
      rw [Int.mul_eq_mul_left_iff y_denom_zero] at this
      exact this

def Rational := Quotient NumPairSetoid
