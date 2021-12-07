import M4R.Algebra.Group.Basic

namespace M4R
  namespace AbelianGroup

    theorem mul_nat_comm [g : AbelianGroup α] (a b : α) (n : Nat) : n*(a + b) = n*a + n*b :=
    match n with
    | Nat.zero   => by rw [g.mul_nat_0, g.mul_nat_0, g.mul_nat_0, g.add_zero];
    | Nat.succ m => by induction m with
      | zero             => rw [g.mul_nat_1, g.mul_nat_1, g.mul_nat_1] 
      | succ k ih        =>
        have h2 (x : α) : Nat.succ (Nat.succ k) * x = Nat.succ k * x + x := by rfl;
          rw [h2, h2, h2, g.add_assoc (Nat.succ k * a) a, add_comm a (Nat.succ k * b + b),
            g.add_assoc _ b a, add_comm b a, ←g.add_assoc (Nat.succ k * a), g.add_right_cancel]; exact ih

    instance TrivialAbelian [s : Singleton α] : AbelianGroup α where
      add_comm := by intro a b; rfl
      
  end AbelianGroup
end M4R