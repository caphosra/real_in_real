import RealInReal.Natural

structure NumPair where
  num: Int
  denom: Nat

  denom_non_zero: denom ≠ 0

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

theorem NumPair.le_universal{a_1 a_2 b_1 b_2: NumPair}:
    a_1 ≈ a_2
      → b_1 ≈ b_2
      → a_1.num * ↑b_1.denom ≤ b_1.num * ↑a_1.denom
      → a_2.num * ↑b_2.denom ≤ b_2.num * ↑a_2.denom := by
  intros a_eq b_eq
  intros h
  have: (↑a_2.denom: Int) ≥ 0 := by
    simp
  let h' := Int.mul_le_mul_of_nonneg_right h this
  conv at h' =>
    lhs
    rw [Int.mul_right_comm]
    lhs
    rw [a_eq]
  conv at h' =>
    congr
    case a =>
      rw [Int.mul_right_comm]
    case a =>
      rw [Int.mul_right_comm]
  have: (↑a_1.denom: Int) > 0 := by
    simp
    exact Nat.zero_lt_of_ne_zero a_1.denom_non_zero
  let h'' := Int.le_of_mul_le_mul_right h' this
  have: (↑b_2.denom: Int) ≥ 0 := by
    simp
  let h''' := Int.mul_le_mul_of_nonneg_right h'' this
  conv at h''' =>
    rhs
    rw [Int.mul_right_comm]
    lhs
    rw [b_eq]
  conv at h''' =>
    congr
    case a =>
      rw [Int.mul_right_comm]
    case a =>
      rw [Int.mul_right_comm]
  have: (↑b_1.denom: Int) > 0 := by
    simp
    exact Nat.zero_lt_of_ne_zero b_1.denom_non_zero
  exact Int.le_of_mul_le_mul_right h''' this

def Rational.le (a b: Rational): Prop :=
  Quotient.liftOn₂ a b (fun x y => x.num * y.denom ≤ y.num * x.denom)
  (
    by
      intros a_1 b_1 a_2 b_2 a_eq b_eq
      simp
      constructor
      case mp =>
        exact NumPair.le_universal a_eq b_eq
      case mpr =>
        have a_eq': a_2 ≈ a_1 := by
          exact NumPairSetoid.symm a_eq
        have b_eq': b_2 ≈ b_1 := by
          exact NumPairSetoid.symm b_eq
        exact NumPair.le_universal a_eq' b_eq'
  )

instance RationalLE : LE Rational where
  le := Rational.le

instance RationalLT : LT Rational where
  lt a b := a ≤ b ∧ a ≠ b
