import M4R.Algebra.Ring.RMorphism

namespace M4R
  open Group
  open AbelianGroup
  open NonCommutativeRing
  open Ring

  structure Ideal (α : Type _) [Ring α] where
    subset : Set α
    has_zero : 0 ∈ subset
    add_closed : ∀ {a b : α}, a ∈ subset → b ∈ subset → a + b ∈ subset
    mul_closed : ∀ (a : α) {b : α}, b ∈ subset → a * b ∈ subset

  namespace Ideal

    theorem mul_closed' [Ring α] (I : Ideal α) : ∀ {a : α} (b : α), a ∈ I.subset → a * b ∈ I.subset := by
      intro a b as; rw [mul_comm]; exact I.mul_closed b as
    theorem neg_closed [Ring α] (I : Ideal α) : ∀ {a : α}, a ∈ I.subset → -a ∈ I.subset := by
      intro a as; rw [←mul_one a, ←mul_neg, mul_comm]; exact I.mul_closed (-1) as

    protected def image [Ring α] (I : Ideal α) (a : α) (p : a ∈ I.subset) : ↑I.subset := ⟨a, p⟩
    protected theorem image_eq [Ring α] (I : Ideal α) (a b : ↑I.subset) :
      a = b ↔ Set.inclusion a = Set.inclusion b :=
        ⟨congrArg Set.inclusion, Set.elementExt a b⟩

    instance ZeroIdeal [Ring α] : Ideal α where
      subset := Set.SingletonSet.mk 0
      has_zero := rfl
      add_closed := by intro x y xz yz; rw [xz, yz, add_zero]; rfl
      mul_closed := by intro _ _ h; rw [h, mul_zero]; trivial
      
    instance UnitIdeal [Ring α] : Ideal α where
      subset := Set.Universal
      has_zero := trivial
      add_closed := by intros; trivial
      mul_closed := by intros; trivial

    instance IdealAbelianGroup [r : Ring α] (I : Ideal α) : AbelianGroup ↑I.subset where
      zero := ⟨0, I.has_zero⟩
      add := fun ⟨x, xs⟩ ⟨y, ys⟩ => ⟨x + y, I.add_closed xs ys⟩
      neg := fun ⟨x, xs⟩ => ⟨-x, I.neg_closed xs⟩
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
      add_closed := fun ⟨ia, ⟨ja, ija⟩⟩ ⟨ib, ⟨jb, ijb⟩⟩ => ⟨
          ⟨ia.val+ib.val, I.add_closed ia.property ib.property⟩,
          ⟨ja.val+jb.val, J.add_closed ja.property jb.property⟩, by
          rw [add_assoc, add_comm ib.val, add_assoc, add_comm jb.val, ←add_assoc, ija, ijb]
        ⟩
      mul_closed := fun a b ⟨ia, ⟨ja, ija⟩⟩ => ⟨
          ⟨a*ia.val, I.mul_closed a ia.property⟩,
          ⟨a*ja.val, J.mul_closed a ja.property⟩,
          by rw [←mul_distrib_left, ija]
        ⟩
    instance IdealAdd [Ring α] : Add (Ideal α) where add := Ideal.add
    
    def coprime [Ring α] (I J : Ideal α) : Prop := I + J = UnitIdeal

    def principal [r : Ring α] (a : α) : Ideal α where
      subset := {x | a ÷ x}
      has_zero := divides_zero a;
      add_closed := divides_add
      mul_closed := fun x => divides_mul' x

    def is_principal [Ring α] (I : Ideal α) : Prop :=
      ∃ a, a ∈ I.subset ∧ ∀ x, x ∈ I.subset → a ÷ x

    def is_prime [Ring α] (I : Ideal α) : Prop :=
      ∀ r s, r * s ∈ I.subset → r ∈ I.subset ∨ s ∈ I.subset

    theorem principal_principal [Ring α] (a : α) : is_principal (principal a) :=
      ⟨a, ⟨divides_self a, by intro _ h; exact h⟩⟩

    theorem principal_of_is_principal [Ring α] (I : Ideal α) (h : is_principal I) : ∃ a, I = principal a := by
      let ⟨a, ⟨aI, ha⟩⟩ := h;
      exact ⟨a, by apply (Ideal.ext _ _).mp; apply Set.subset.antisymm ha;
                    intro x xp; let ⟨b, ab⟩ := xp; rw [←ab]; exact I.mul_closed' b aI⟩

  end Ideal

  namespace QuotientRing

    def QuotientRelation [Ring α] (I : Ideal α) (a b : α) : Prop := -a + b ∈ I.subset

    theorem QuotientRelation.refl [Ring α] (I : Ideal α) (a : α) : QuotientRelation I a a := by
      simp [QuotientRelation]; rw [neg_add]; exact I.has_zero;

    def QuotClass [Ring α] (I : Ideal α) : Type _ :=
      Quot (QuotientRelation I)

    def QuotAdd [Ring α] (I : Ideal α) : QuotClass I → QuotClass I → QuotClass I :=
      Function.Quotient.map₂ (QuotientRelation I) (QuotientRelation I) (QuotientRelation I)
        (QuotientRelation.refl I) (QuotientRelation.refl I) (fun x y => x + y) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp [QuotientRelation] at *;
          rw [neg_add_distrib, add_comm (-b₁), add_assoc, ←add_assoc (-b₁), add_comm (-b₁), add_assoc, ←add_assoc];
          exact I.add_closed ha hb)

    def QuotNeg [Ring α] (I : Ideal α) : QuotClass I → QuotClass I :=
      Function.Quotient.map (QuotientRelation I) (QuotientRelation I) (fun x => -x)
        (fun x y hxy => by
          simp [QuotientRelation] at *; rw [←neg_add_distrib, add_comm]; exact I.neg_closed hxy)

    def QuotMul [Ring α] (I : Ideal α) : QuotClass I → QuotClass I → QuotClass I := by
      apply Function.Quotient.map₂ (QuotientRelation I) (QuotientRelation I) (QuotientRelation I)
        (QuotientRelation.refl I) (QuotientRelation.refl I) (fun x y => x * y) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp [QuotientRelation] at *;
          have := I.add_closed (I.mul_closed b₁ ha) (I.mul_closed a₂ hb);
          rw [mul_distrib_left, mul_distrib_left, mul_neg, mul_comm, mul_comm b₁, add_assoc, ←add_assoc (a₂ * b₁),
            mul_neg, add_neg, zero_add] at this; exact this)

    instance QuotientRing (α : Type _) [Ring α] (I : Ideal α) : Ring (QuotClass I) where
      zero := Quot.mk (QuotientRelation I) 0
      one := Quot.mk (QuotientRelation I) 1
      add := QuotAdd I
      neg := QuotNeg I
      mul := QuotMul I
      add_zero := by
        apply Quot.ind; intros; apply Quot.sound; simp [QuotientRelation];
        rw [add_zero, neg_add]; exact I.has_zero
      add_assoc := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp [QuotientRelation];
        rw [add_assoc, neg_add]; exact I.has_zero
      add_neg := by
        apply Quot.ind; intros; apply Quot.sound; simp [QuotientRelation];
        rw [add_neg, neg_add]; exact I.has_zero
      add_comm := by
        apply Function.Quotient.ind₂; intro a _; apply Quot.sound; simp [QuotientRelation];
        rw [add_comm a, neg_add]; exact I.has_zero
      mul_one := by
        apply Quot.ind; intros; apply Quot.sound; simp [QuotientRelation];
        rw [mul_one, neg_add]; exact I.has_zero
      one_mul := by
        apply Quot.ind; intros; apply Quot.sound; simp [QuotientRelation];
        rw [one_mul, neg_add]; exact I.has_zero
      mul_assoc := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp [QuotientRelation];
        rw [mul_assoc, neg_add]; exact I.has_zero
      mul_distrib_left := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp [QuotientRelation];
        rw [mul_distrib_left, neg_add]; exact I.has_zero
      mul_distrib_right := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp [QuotientRelation];
        rw [mul_distrib_right, neg_add]; exact I.has_zero
      mul_comm := by
        apply Function.Quotient.ind₂; intros; apply Quot.sound; simp [QuotientRelation];
        rw [mul_comm, neg_add]; exact I.has_zero

  end QuotientRing
end M4R