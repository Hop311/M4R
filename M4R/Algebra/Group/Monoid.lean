import M4R.Algebra.Group.Defs

namespace M4R
  namespace Monoid

    protected instance Product (α₁ : Type _) (α₂ : Type _) [Monoid α₁] [Monoid α₂] : Monoid (α₁ × α₂) where
      zero      := (0, 0)
      add       := fun (x₁, x₂) (y₁, y₂) => (x₁ + y₁, x₂ + y₂)
      add_zero  := fun (a₁, a₂) => by simp only [HAdd.hAdd, Add.add, Prod.mk.injEq]; exact ⟨add_zero a₁, add_zero a₂⟩
      zero_add  := fun (a₁, a₂) => by simp only [HAdd.hAdd, Add.add, Prod.mk.injEq]; exact ⟨zero_add a₁, zero_add a₂⟩
      add_assoc := fun (a₁, a₂) (b₁, b₂) (c₁, c₂) => by
        simp only [HAdd.hAdd, Add.add, Prod.mk.injEq]
        exact ⟨add_assoc a₁ b₁ c₁, add_assoc a₂ b₂ c₂⟩

    theorem product_zero (α₁ : Type _) (α₂ : Type _) [Monoid α₁] [Monoid α₂] : (0 : α₁ × α₂) = (0, 0) := rfl

    protected instance multi_product.Zero {ι : Type _} (fι : ι → Type _) [∀ i, Zero (fι i)] : Zero (MultiProd fι) where
      zero := fun _ => 0
    protected theorem multi_product.Zero_def {ι : Type _} {fι : ι → Type _} [∀ i, Zero (fι i)] : ∀ i, (0 : MultiProd fι) i = 0 :=
      fun _ => rfl
    
    protected instance multi_product.Add {ι : Type _} (fι : ι → Type _) [∀ i, Add (fι i)] : Add (MultiProd fι) where
      add := fun a b i => a i + b i
    protected theorem multi_product.Add_def {ι : Type _} {fι : ι → Type _} [∀ i, Add (fι i)] (a b : MultiProd fι) :
      ∀ i, (a + b) i = a i + b i := fun _ => rfl

    protected instance multi_product {ι : Type _} (fι : ι → Type _) [∀ i, Monoid (fι i)] : Monoid (MultiProd fι) where
      add_zero  := fun a => funext fun i => Monoid.add_zero (a i)
      zero_add  := fun a => funext fun i => Monoid.zero_add (a i)
      add_assoc := fun a b c => funext fun i => Monoid.add_assoc (a i) (b i) (c i)

  end Monoid

  namespace CommMonoid

    protected instance Product (α₁ : Type _) (α₂ : Type _) [CommMonoid α₁] [CommMonoid α₂] : CommMonoid (α₁ × α₂) where
      add_comm := fun (a₁, a₂) (b₁, b₂) => by simp [HAdd.hAdd, Add.add]; exact ⟨add_comm a₁ b₁, add_comm a₂ b₂⟩

    protected instance multi_product {ι : Type _} (fι : ι → Type _) [∀ i, CommMonoid (fι i)] : CommMonoid (MultiProd fι) where
      add_comm := fun a b => funext fun i => CommMonoid.add_comm (a i) (b i)

    theorem add_right_comm [CommMonoid α] (a b c : α) : a + b + c = a + c + b := by
      rw [Monoid.add_assoc, add_comm b, ←Monoid.add_assoc]
    theorem add_left_comm [CommMonoid α] (a b c : α) : a + (b + c) = b + (a + c) := by
      rw [←Monoid.add_assoc, add_comm a, Monoid.add_assoc]

    protected class constructor_cm (α : Type _) extends Zero α, Add α where
      add_zero  : ∀ a : α, a + 0 = a
      add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
      add_comm  : ∀ a b : α, a + b = b + a

    protected instance construct {α : Type _} (c : CommMonoid.constructor_cm α) : CommMonoid α where
      add_zero  := c.add_zero
      zero_add  := fun a => by rw [c.add_comm]; exact c.add_zero a
      add_assoc := c.add_assoc
      add_comm  := c.add_comm

    protected def to_constructor (α : Type _) [CommMonoid α] : CommMonoid.constructor_cm α where
      add_zero  := Monoid.add_zero
      add_assoc := Monoid.add_assoc
      add_comm  := CommMonoid.add_comm

  end CommMonoid

  instance NatMonoid : CommMonoid Nat := CommMonoid.construct
    {
      add_zero  := Nat.add_zero
      add_assoc := Nat.add_assoc
      add_comm  := Nat.add_comm
    }

end M4R
