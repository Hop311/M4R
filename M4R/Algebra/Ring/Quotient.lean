import M4R.Algebra.Ring.Basic

namespace M4R

  structure Ideal (α : Type _) [Ring α] where
    subset : Set α
    nonempty : 0 ∈ subset
    closed_add : ∀ a b : α, a ∈ subset → b ∈ subset → a + b ∈ subset
    closed_mul : ∀ a b : α, a ∈ subset → a * b ∈ subset
  
  namespace Ideal
    open Group
    open AbelianGroup
    open Ring
  
    instance ZeroIdeal [Ring α] : Ideal α where
      subset := Set.SingletonSet.mk 0
      nonempty := rfl
      closed_add := by intro x y xz yz; rw [xz, yz, add_zero]; rfl
      closed_mul := by intro _ _ h; rw [h, zero_mul]; trivial
      
    instance UnitIdeal [Ring α] : Ideal α where
      subset := Set.Universal
      nonempty := trivial
      closed_add := by intros; trivial
      closed_mul := by intros; trivial

    def contained [Ring α] (I J: Ideal α) : Prop := I.subset ⊆ J.subset
    instance IdealSubset [Ring α] : Subset (Ideal α) where subset := contained
    
    protected def equivalent [Ring α] (I J: Ideal α) : Prop := I.subset = J.subset
    protected theorem ext [Ring α] (I J : Ideal α) : Ideal.equivalent I J ↔ I = J := by
      match I, J with
      | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ =>
        apply Iff.intro;
        { intro eq; rw [Ideal.mk.injEq]; exact eq }
        { simp [Ideal.equivalent]; exact id }

    protected def add [Ring α] (I J : Ideal α) : Ideal α where
      subset := {x | ∃ i : I.subset, ∃ j : J.subset, i.val + j.val = x }
      nonempty := ⟨⟨0, I.nonempty⟩, ⟨0, J.nonempty⟩, show 0 + 0 = 0 by rw [add_zero 0]⟩
      closed_add := fun _ _ ⟨ia, ⟨ja, ija⟩⟩ ⟨ib, ⟨jb, ijb⟩⟩ => ⟨
          ⟨ia.val+ib.val, I.closed_add ia.val ib.val ia.property ib.property⟩,
          ⟨ja.val+jb.val, J.closed_add ja.val jb.val ja.property jb.property⟩, by
          rw [add_assoc, add_comm ib.val, add_assoc, add_comm jb.val, ←add_assoc, ija, ijb]
        ⟩
      closed_mul := fun _ b ⟨ia, ⟨ja, ija⟩⟩ => ⟨
          ⟨ia.val*b, I.closed_mul ia.val b ia.property⟩,
          ⟨ja.val*b, J.closed_mul ja.val b ja.property⟩, by
          simp; rw [←ija, mul_distrib_right]
        ⟩
    instance IdealAdd [Ring α] : Add (Ideal α) where add := Ideal.add
    
    def coprime [Ring α] (I J : Ideal α) : Prop := I + J = UnitIdeal

    def principal [Ring α] (a : α) : Ideal α where
      subset := {x | a ÷ x}
      nonempty := divides_zero a;
      closed_add := divides_add a
      closed_mul := divides_mul a

    def is_principal [Ring α] (I : Ideal α) : Prop :=
      ∃ a, a ∈ I.subset ∧ ∀ x, x ∈ I.subset → a ÷ x

    def is_prime [Ring α] (I : Ideal α) : Prop :=
      ∀ r s, r * s ∈ I.subset → r ∈ I.subset ∨ s ∈ I.subset

    theorem principal_principal [Ring α] (a : α) : is_principal (principal a) :=
      ⟨a, ⟨divides_self a, by intro _ h; exact h⟩⟩

    theorem principal_of_is_principal [Ring α] (I : Ideal α) (h : is_principal I) : ∃ a, I = principal a := by
      let ⟨a, ⟨aI, ha⟩⟩ := h;
      exact ⟨a, by apply (Ideal.ext _ _).mp; apply Set.subset.antisymm ha;
                    intro x xp; let ⟨b, ab⟩ := xp; rw [←ab]; exact I.closed_mul a b aI⟩

  end Ideal
end M4R