def Set α := α → Prop

infixl: 50 "∈" => fun {α: Type}(a: α) (s: Set α) => s a

infixl: 50 "∉" => fun {α: Type}(a: α) (s: Set α) => ¬s a

infixl: 50 "∪" => fun {α: Type}(s_1: Set α) (s_2: Set α) =>
  fun (a: α) => s_1 a ∨ s_2 a

infixl: 50 "∩" => fun {α: Type}(s_1: Set α) (s_2: Set α) =>
  fun (a: α) => s_1 a ∧ s_2 a

def Set.Subset {α: Type} (s_1: Set α) (s_2: Set α) : Prop :=
  ∀a: α, s_1 a → s_2 a

infixl: 50 "⊆" => Set.Subset

theorem subset_refl {α: Type} (s: Set α) : s ⊆ s := by
  intros a h
  exact h

instance SubsetSetoid {α: Type} : Setoid (Set α) where
  r := fun s_1 s_2 => s_1 ⊆ s_2 ∧ s_2 ⊆ s_1
  iseqv := by
    constructor
    case refl =>
      intros x
      simp
      exact subset_refl x
    case symm =>
      intros x y h
      exact And.symm h
    case trans =>
      intros x y z h1 h2
      constructor
      case left =>
        intros a x_a
        exact h2.left a (h1.left a x_a)
      case right =>
        intros a y_a
        exact h1.right a (h2.right a y_a)
