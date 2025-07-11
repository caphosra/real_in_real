def Coprime(a:Int)(b: Nat): Prop :=
  ∀d, d ∣ a → d ∣ b → d = 1

theorem zero_or_not: ∀d: Int, d ≠ 0 ∨ d = 0 := by
  intros d
  induction d
  case ofNat d' =>
    simp
    induction d'
    case zero =>
      simp
    case succ d'' h =>
      simp
      have: ∀a: Nat, (↑a: Int) ≥ 0 := by
        simp
      let d''_not_neg := this d''
      have: (↑d'': Int) + 1 = 0 → False := by
        intros h
        have d_minus_one: (↑d'': Int) = -1 := by
          have: (↑d'': Int) + 1 - 1 = 0 - 1 := by
            rw [h]
          simp at this
        simp [d_minus_one] at d''_not_neg
      exact Or.inl this
  case negSucc d' =>
    simp

theorem divisible_or_zero: ∀a b d: Int, d * a = d * b → a = b ∨ d = 0 := by
  intros a b d h
  let d_zero_or_not := zero_or_not d
  cases d_zero_or_not
  case inl d_neq_zero =>
    rw [Int.mul_eq_mul_left_iff d_neq_zero] at h
    exact Or.inl h
  case inr d_eq_zero =>
    exact Or.inr d_eq_zero

#print axioms zero_or_not
#print axioms divisible_or_zero
