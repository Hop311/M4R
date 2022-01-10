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
      (add_zero a).trans (zero_add a).symm
      
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

    theorem sub_right [Group α] {a b c : α} : a + c = b ↔ a = b + -c :=
      ⟨by intro h; rw [←h, add_assoc, add_neg, add_zero],
      by intro h; rw [h, add_assoc, neg_add, add_zero]⟩

    theorem neg_neg [Group α] (a : α) : - - a = a := by
      rw [←add_right_cancel _ _ (-a), neg_add, add_neg]
      
    theorem neg_add_distrib [Group α] (a b : α) : -(a + b) = -b + -a := by
      rw [←add_right_cancel _ _ (a + b), neg_add, add_assoc, ←add_assoc (-a), neg_add, zero_add, neg_add]

    theorem neg_inj [g : Group α] : Function.injective g.neg := by
      intro x y h; rw [←neg_neg x, ←neg_neg y]; exact congrArg g.neg h

  end Group
end M4R
