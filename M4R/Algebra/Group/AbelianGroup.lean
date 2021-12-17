import M4R.Algebra.Group.SubGroup

namespace M4R
  namespace AbelianGroup
    open Group

    theorem mul_nat_comm [AbelianGroup α] (a b : α) (n : Nat) : n*(a + b) = n*a + n*b :=
    match n with
    | Nat.zero   => by rw [mul_nat_0, mul_nat_0, mul_nat_0, add_zero];
    | Nat.succ m => by induction m with
      | zero             => rw [mul_nat_1, mul_nat_1, mul_nat_1] 
      | succ k ih        =>
        have h2 (x : α) : Nat.succ (Nat.succ k) * x = Nat.succ k * x + x := by rfl;
          rw [h2, h2, h2, add_assoc (Nat.succ k * a) a, add_comm a (Nat.succ k * b + b),
            add_assoc _ b a, add_comm b a, ←add_assoc (Nat.succ k * a), add_right_cancel]; exact ih

    instance TrivialAbelian [Singleton α] : AbelianGroup α where
      add_comm := by intro a b; rfl

    instance SubGroupAbelian [AbelianGroup α] (s : SubGroup α) : AbelianGroup ↑s.subset where
      toGroup := s.SubGroupGroup
      add_comm := by intro a b; rw [SubGroup.image_eq]; exact add_comm a.val b.val
     
  end AbelianGroup
end M4R