import RealInReal.Rational
import RealInReal.Set

structure Real where
  partition: Set Rational

  partition_non_empty: ∃x, x ∈ partition
  partition_not_all: ∃x, x ∉ partition
  partition_closed: ∀x y, x < y ∧ y ∈ partition → x ∈ partition
  partition_open: ∀x, x ∈ partition → ∃y, x < y ∧ y ∈ partition

instance RealSetoid : Setoid Real where
  r := fun a b => a.partition ≈ b.partition
  iseqv := by
    constructor
    case refl =>
      intros x
      exact Setoid.refl x.partition
    case symm =>
      intros x y h
      exact Setoid.symm h
    case trans =>
      intros x y z h1 h2
      exact Setoid.trans h1 h2

instance RealLE : LE Real where
  le := fun a b => a.partition ⊆ b.partition

instance RealLT : LT Real where
  lt a b := a ≤ b ∧ a ≠ b
