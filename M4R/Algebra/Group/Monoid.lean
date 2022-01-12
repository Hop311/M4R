import M4R.Algebra.Group.Defs

namespace M4R
  namespace Monoid

    protected instance Product (α₁ : Type _) (α₂ : Type _) [Monoid α₁] [Monoid α₂] : Monoid (α₁ × α₂) where
      zero := (0, 0)
      add := fun (x₁, x₂) (y₁, y₂) => (x₁ + y₁, x₂ + y₂)
      add_zero := fun (a₁, a₂) => by simp [HAdd.hAdd, Add.add]; exact ⟨add_zero a₁, add_zero a₂⟩
      zero_add := fun (a₁, a₂) => by simp [HAdd.hAdd, Add.add]; exact ⟨zero_add a₁, zero_add a₂⟩
      add_assoc := fun (a₁, a₂) (b₁, b₂) (c₁, c₂) => by simp [HAdd.hAdd, Add.add]; exact ⟨add_assoc a₁ b₁ c₁, add_assoc a₂ b₂ c₂⟩

    theorem product_zero (α₁ : Type _) (α₂ : Type _) [Monoid α₁] [Monoid α₂] : (0 : α₁ × α₂) = (0, 0) := rfl

  end Monoid

  namespace CommMonoid

    protected instance Product (α₁ : Type _) (α₂ : Type _) [CommMonoid α₁] [CommMonoid α₂] : CommMonoid (α₁ × α₂) where
      add_comm := fun (a₁, a₂) (b₁, b₂) => by simp [HAdd.hAdd, Add.add]; exact ⟨add_comm a₁ b₁, add_comm a₂ b₂⟩

    theorem add_right_comm [CommMonoid α] (a b c : α) : a + b + c = a + c + b := by
      rw [Monoid.add_assoc, add_comm b, ←Monoid.add_assoc]
    theorem add_left_comm [CommMonoid α] (a b c : α) : a + (b + c) = b + (a + c) := by
      rw [←Monoid.add_assoc, add_comm a, Monoid.add_assoc]

    protected class constructor_cm (α : Type _) extends Zero α, Add α where
      add_zero  : ∀ a : α, a + 0 = a
      add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
      add_comm  : ∀ a b : α, a + b = b + a

    protected instance construct {α : Type _} (c : CommMonoid.constructor_cm α) : CommMonoid α where
      add_zero := c.add_zero
      zero_add := fun a => by rw [c.add_comm]; exact c.add_zero a
      add_assoc := c.add_assoc
      add_comm := c.add_comm
  
  end CommMonoid

  instance NatMonoid : CommMonoid Nat := CommMonoid.construct
    {
      add_zero  := Nat.add_zero
      add_assoc := Nat.add_assoc
      add_comm  := Nat.add_comm
    }

end M4R
