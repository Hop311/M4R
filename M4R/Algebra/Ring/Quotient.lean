import M4R.Algebra.Ring.Basic

namespace M4R

  structure Ideal (α : Type _) [Ring α] where
    subset : Set α
    has_zero : 0 ∈ subset
    closed_add : ∀ a b : α, a ∈ subset → b ∈ subset → a + b ∈ subset
    closed_mul : ∀ a b : α, b ∈ subset → a * b ∈ subset

  namespace Ideal
    open Group
    open AbelianGroup
    open NonCommutativeRing
    open Ring

    theorem closed_mul' [Ring α] (I : Ideal α) : ∀ a b : α, a ∈ I.subset → a * b ∈ I.subset := by
      intro a b as; rw [mul_comm]; exact I.closed_mul b a as
    theorem closed_neg [Ring α] (I : Ideal α) : ∀ a : α, a ∈ I.subset → -a ∈ I.subset := by
      intro a as; rw [←mul_one a, ←mul_neg, mul_comm]; exact I.closed_mul (-1) a as

    protected def image [Ring α] (I : Ideal α) (a : α) (p : a ∈ I.subset) : ↑I.subset := ⟨a, p⟩
    protected theorem image_eq [Ring α] (I : Ideal α) (a b : ↑I.subset) :
      a = b ↔ Set.inclusion a = Set.inclusion b :=
        ⟨congrArg Set.inclusion, Set.elementExt a b⟩

    instance ZeroIdeal [Ring α] : Ideal α where
      subset := Set.SingletonSet.mk 0
      has_zero := rfl
      closed_add := by intro x y xz yz; rw [xz, yz, add_zero]; rfl
      closed_mul := by intro _ _ h; rw [h, mul_zero]; trivial
      
    instance UnitIdeal [Ring α] : Ideal α where
      subset := Set.Universal
      has_zero := trivial
      closed_add := by intros; trivial
      closed_mul := by intros; trivial

    instance IdealAbelianGroup [r : Ring α] (I : Ideal α) : AbelianGroup ↑I.subset where
      zero := ⟨0, I.has_zero⟩
      add := fun ⟨x, xs⟩ ⟨y, ys⟩ => ⟨x + y, I.closed_add x y xs ys⟩
      neg := fun ⟨x, xs⟩ => ⟨-x, I.closed_neg x xs⟩
      add_zero  := by intro ⟨a, _⟩; simp [Ideal.image_eq]; exact r.add_zero a
      add_assoc := by intro ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩; simp [Ideal.image_eq]; exact r.add_assoc a b c
      add_neg   := by intro ⟨a, _⟩; simp [Ideal.image_eq]; exact r.add_neg a
      add_comm  := by intro ⟨a, _⟩ ⟨b, _⟩; simp [Ideal.image_eq]; exact r.add_comm a b
    
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
      has_zero := ⟨⟨0, I.has_zero⟩, ⟨0, J.has_zero⟩, show 0 + 0 = 0 by rw [add_zero 0]⟩
      closed_add := fun _ _ ⟨ia, ⟨ja, ija⟩⟩ ⟨ib, ⟨jb, ijb⟩⟩ => ⟨
          ⟨ia.val+ib.val, I.closed_add ia.val ib.val ia.property ib.property⟩,
          ⟨ja.val+jb.val, J.closed_add ja.val jb.val ja.property jb.property⟩, by
          rw [add_assoc, add_comm ib.val, add_assoc, add_comm jb.val, ←add_assoc, ija, ijb]
        ⟩
      closed_mul := fun a b ⟨ia, ⟨ja, ija⟩⟩ => ⟨
          ⟨a*ia.val, I.closed_mul a ia.val ia.property⟩,
          ⟨a*ja.val, J.closed_mul a ja.val ja.property⟩,
          by rw [←mul_distrib_left, ija]
        ⟩
    instance IdealAdd [Ring α] : Add (Ideal α) where add := Ideal.add
    
    def coprime [Ring α] (I J : Ideal α) : Prop := I + J = UnitIdeal

    def principal [r : Ring α] (a : α) : Ideal α where
      subset := {x | a ÷ x}
      has_zero := divides_zero a;
      closed_add := divides_add a
      closed_mul := divides_mul' a

    def is_principal [Ring α] (I : Ideal α) : Prop :=
      ∃ a, a ∈ I.subset ∧ ∀ x, x ∈ I.subset → a ÷ x

    def is_prime [Ring α] (I : Ideal α) : Prop :=
      ∀ r s, r * s ∈ I.subset → r ∈ I.subset ∨ s ∈ I.subset

    theorem principal_principal [Ring α] (a : α) : is_principal (principal a) :=
      ⟨a, ⟨divides_self a, by intro _ h; exact h⟩⟩

    theorem principal_of_is_principal [Ring α] (I : Ideal α) (h : is_principal I) : ∃ a, I = principal a := by
      let ⟨a, ⟨aI, ha⟩⟩ := h;
      exact ⟨a, by apply (Ideal.ext _ _).mp; apply Set.subset.antisymm ha;
                    intro x xp; let ⟨b, ab⟩ := xp; rw [←ab]; exact I.closed_mul' a b aI⟩

  end Ideal
end M4R