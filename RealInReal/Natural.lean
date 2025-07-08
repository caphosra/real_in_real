def Coprime(a:Int)(b: Nat): Prop :=
  ∀d, d ∣ a → d ∣ b → d = 1
