import M4R.Algebra.Group.Monoid

namespace M4R
  namespace Group
    open Monoid

    protected instance Product (α₁ : Type _) (α₂ : Type _) [Group α₁] [Group α₂] : Group (α₁ × α₂) where
      neg := fun (x₁, x₂) => (-x₁, -x₂)
      add_neg := fun (a₁, a₂) => by simp [HAdd.hAdd, Add.add, product_zero]; exact ⟨add_neg a₁, add_neg a₂⟩

    theorem neg_add [Group α] (a : α) : -a + a = 0 := by
      calc
        -a + a = -a + a + (-a + - -a) := by rw [add_neg, add_zero]
        _      = -a + (a + -a) + - -a := by rw [←add_assoc (-a + a), add_assoc (-a)]
        _      = (0 : α)              := by rw [add_neg, add_zero, add_neg]
    theorem add_neg_comm [Group α] (a : α) : a + (-a) = (-a) + a :=
      Eq.trans (add_neg a) (Eq.symm (neg_add a))
      
    theorem neg_zero [Group α] : -(0 : α) = 0 := by
      rw [←zero_add (-0), add_neg];

    theorem add_right_cancel [Group α] (a b c : α) : a + c = b + c ↔ a = b  := by
      have : ∀ (x y z : α), x = y → x + z = y + z := fun x y z => congrArg (· + z)
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

    protected class constructor_g (α : Type _) extends Zero α, Add α, Neg α where
      add_zero  : ∀ a : α, a + 0 = a
      add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
      add_neg   : ∀ a : α, a + (-a) = 0

    protected instance construct {α : Type _} (c : Group.constructor_g α) : Group α where
      add_zero := c.add_zero
      zero_add := fun a => by
        rw [←c.add_neg a, c.add_assoc]
        (conv => lhs rhs rhs rw [←c.add_zero a, ←c.add_neg (-a), ←c.add_assoc, c.add_neg])
        rw [←c.add_assoc (-a), c.add_zero, c.add_neg, c.add_zero]
      add_assoc := c.add_assoc
      add_neg := c.add_neg
  
  end Group

  namespace AbelianGroup

    protected instance Product (α₁ : Type _) (α₂ : Type _) [AbelianGroup α₁] [AbelianGroup α₂] : AbelianGroup (α₁ × α₂) where
      add_comm := (CommMonoid.Product α₁ α₂).add_comm

    protected class constructor_ab (α : Type _) extends Group.constructor_g α, CommMonoid.constructor_cm α

    protected instance construct {α : Type _} (c : AbelianGroup.constructor_ab α) : AbelianGroup α where
      toGroup := Group.construct c.toconstructor_g
      add_comm := c.add_comm

  end AbelianGroup

  instance IntGroup : AbelianGroup Int := AbelianGroup.construct
  {
    add_zero  := Int.add_zero
    add_assoc := Int.add_assoc
    add_neg   := Int.add_neg
    add_comm  := Int.add_comm
  }

end M4R
