import M4R.Algebra.Group.Defs

namespace M4R
  namespace Group

    theorem neg_add [Group α] (a : α) : -a + a = 0 := by
      calc
        -a + a = -a + a + (-a + - -a) := by rw [add_neg, add_zero]
        _      = -a + (a + -a) + - -a := by rw [←add_assoc (-a + a), add_assoc (-a)]
        _      = (0 : α)              := by rw [add_neg, add_zero, add_neg]
    theorem add_neg_comm [Group α] (a : α) : a + (-a) = (-a) + a :=
      Eq.trans (add_neg a) (Eq.symm (neg_add a))

    theorem zero_add [Group α] (a : α) : 0 + a = a := by
      rw [←add_neg a, add_assoc, neg_add, add_zero]
    theorem add_zero_comm [Group α] (a : α) : a + 0 = 0 + a :=
      Eq.trans (add_zero a) (Eq.symm (zero_add a))
      
    theorem neg_zero [Group α] : -(0 : α) = 0 := by
      rw [←zero_add (-0), add_neg];

    theorem add_right_cancel [Group α] (a b c : α) : a + c = b + c ↔ a = b  := by
      have : ∀ (x y z : α), x = y → x + z = y + z := by intro x y z; exact congrArg fun t => t + z
      apply Iff.intro
      case mpr => exact this a b c
      case mp =>
        intro hacbc
        rw [← add_zero a, ← add_zero b, ← add_neg c, ← add_assoc a, ← add_assoc b]
        exact this (a+c) (b+c) (-c) hacbc

    theorem neg_neg [Group α] (a : α) : - - a = a := by
      rw [←add_right_cancel _ _ (-a), neg_add, add_neg]
      
    theorem neg_add_distrib [Group α] (a b : α) : -(a + b) = -b + -a := by
      rw [←add_right_cancel _ _ (a + b), neg_add, add_assoc, ←add_assoc (-a), neg_add, zero_add, neg_add]

/-
  ### Natural multiplication
-/

    theorem mul_nat_zero [Group α] (n : Nat) : n*(0 : α) = 0 := by
      induction n with
      | zero      => rfl
      | succ k ih => conv => rhs rw [←ih, ←add_zero (k*(0 : α))]
    theorem mul_nat_0 [Group α] (a : α) : (0 : Nat)*a = 0 := rfl
    theorem mul_nat_1 [Group α] (a : α) : (1 : Nat)*a = a := by conv => rhs rw [←zero_add a]
    theorem mul_nat_2 [Group α] (a : α) : (2 : Nat)*a = a + a := by
      rw [←zero_add (a + a), ←add_assoc]; rfl

    theorem mul_nat_distrib [Group α] (a : α) (m n : Nat) : (m + n)*a = m*a + n*a :=
      match m, n with
      | Nat.zero  , Nat.zero   => by rw [mul_nat_0, add_zero]
      | Nat.zero  , Nat.succ q => by rw [mul_nat_0, zero_add, Nat.zero_add]
      | Nat.succ p, Nat.zero   => by rw [mul_nat_0, add_zero, Nat.add_zero]
      | Nat.succ p, Nat.succ q => by induction q with
        | zero             => rw [mul_nat_1]; rfl
        | succ k ih        =>
          have : Nat.succ (Nat.succ k) * a = Nat.succ k * a + a := rfl;
          rw [this];
          have : (Nat.succ p + Nat.succ (Nat.succ k)) * a = (Nat.succ p + Nat.succ k) * a + a := rfl;
          rw [this, ←add_assoc, add_right_cancel]; exact ih

    theorem mul_nat_comp [Group α] (a : α) (m n : Nat) : (m * n)*a = m*(n*a) :=
      match m, n with
      | Nat.zero  , Nat.zero   => by rw [mul_nat_0, mul_nat_0]
      | Nat.zero  , Nat.succ q => by simp; rw [mul_nat_0, mul_nat_0]
      | Nat.succ p, Nat.zero   => by simp; rw [mul_nat_0, mul_nat_zero];
      | Nat.succ p, Nat.succ q => by induction p with
        | zero      => simp; rw [mul_nat_1, Nat.one_mul]
        | succ k ih => rw [Nat.succ_mul, mul_nat_distrib, ih,
          Nat.succ_eq_add_one (Nat.succ k), mul_nat_distrib, mul_nat_1]
/-
  ### Integer multiplication
-/

    theorem mul_int_n1 [Group α] (a : α) : (-1 : Int)*a = -a := by
      have : (-1 : Int)*a = 0 + (-a) := rfl; rw [this, zero_add]

    theorem mul_int_distrib [Group α] (a : α) (m n : Int) : (m+n)*a = m*a + n*a :=
      match m, n with
      | Int.ofNat p, Int.ofNat q => mul_nat_distrib a p q
      | Int.ofNat p, Int.negSucc q => by
        match Int.ofNat p + Int.negSucc q with
        | Int.ofNat r   => sorry
        | Int.negSucc r => sorry
      | Int.negSucc p, Int.ofNat q => by sorry
      | Int.negSucc p, Int.negSucc q => by sorry

    theorem mul_int_comp [Group α] (a : α) (m n : Int) : (m * n)*a = m*(n*a) :=
      match m, n with
      | Int.ofNat p  , Int.ofNat q   => mul_nat_comp a p q
      | Int.ofNat p  , Int.negSucc q => sorry
      | Int.negSucc p, Int.ofNat q   => sorry
      | Int.negSucc p, Int.negSucc q => sorry

    theorem neg_mul_int_distrib [Group α] (a : α) (n : Int) : (-n)*a = -(n*a) :=
      match n with
      | Int.ofNat m   => sorry
      | Int.negSucc m => sorry

    theorem neg_mul_int_distrib' [Group α] (a : α) (n : Int) : (-n)*a = n*(-a) := sorry
    theorem neg_mul_int_distrib'' [Group α] (a : α) (n : Int) : n*(-a) = -(n*a) := sorry
/-
  ### Instances
-/
    instance GroupInhabited [Group α] : Inhabited α where default := 0
    instance SingletonGroup [Singleton α] : Group α where
      zero := Inhabited.default
      add := fun _ _ => Inhabited.default
      neg := fun _ => Inhabited.default
      add_zero := by intro a; rw [Singleton.single a]; rfl
      add_assoc := by intro a b c; rw [Singleton.single a, Singleton.single b, Singleton.single c]; rfl
      add_neg := by intro a; rfl

  end Group
end M4R
