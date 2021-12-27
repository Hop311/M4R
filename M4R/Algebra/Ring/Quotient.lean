import M4R.Algebra.Ring.RMorphism
import M4R.Set

namespace M4R
  open Group
  open AbelianGroup
  open NCRing
  open Ring

  structure Ideal (α : Type _) [Ring α] where
    subset : Set α
    has_zero : 0 ∈ subset
    add_closed : ∀ {a b : α}, a ∈ subset → b ∈ subset → a + b ∈ subset
    mul_closed : ∀ (a : α) {b : α}, b ∈ subset → a * b ∈ subset

  namespace Ideal
    instance IdealMem [Ring α] : Mem α (Ideal α) where mem := fun x I => x ∈ I.subset

    theorem mul_closed' [Ring α] (I : Ideal α) : ∀ {a : α} (b : α), a ∈ I → a * b ∈ I := by
      intro a b as; rw [mul_comm]; exact I.mul_closed b as
    theorem neg_closed [Ring α] (I : Ideal α) : ∀ {a : α}, a ∈ I → -a ∈ I := by
      intro a as; rw [←mul_one a, ←mul_neg, mul_comm]; exact I.mul_closed (-1) as

    protected def image [Ring α] (I : Ideal α) (a : α) (p : a ∈ I) : ↑I.subset := ⟨a, p⟩
    protected theorem image_eq [Ring α] (I : Ideal α) (a b : ↑I.subset) :
      a = b ↔ Set.inclusion a = Set.inclusion b :=
        ⟨congrArg Set.inclusion, Set.elementExt⟩

    instance ZeroIdeal [Ring α] : Ideal α where
      subset := Set.SingletonSet.mk 0
      has_zero := rfl
      add_closed := by intro x y xz yz; rw [xz, yz, add_zero]; rfl
      mul_closed := by intro _ _ h; rw [h, mul_zero]; trivial
      
    instance UnitIdeal (α : Type _) [Ring α] : Ideal α where
      subset := Set.Universal
      has_zero := trivial
      add_closed := by intros; trivial
      mul_closed := by intros; trivial

    instance IdealAbelianGroup [r : Ring α] (I : Ideal α) : AbelianGroup ↑I.subset where
      zero := ⟨0, I.has_zero⟩
      add := fun ⟨x, xs⟩ ⟨y, ys⟩ => ⟨x + y, I.add_closed xs ys⟩
      neg := fun ⟨x, xs⟩ => ⟨-x, I.neg_closed xs⟩
      add_zero  := by intro ⟨a, _⟩; simp only [Ideal.image_eq]; exact r.add_zero a
      add_assoc := by intro ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩; simp only [Ideal.image_eq]; exact r.add_assoc a b c
      add_neg   := by intro ⟨a, _⟩; simp only [Ideal.image_eq]; exact r.add_neg a
      add_comm  := by intro ⟨a, _⟩ ⟨b, _⟩; simp only [Ideal.image_eq]; exact r.add_comm a b
    
    protected def equivalent [Ring α] (I J: Ideal α) : Prop := I.subset = J.subset
    protected theorem ext [Ring α] (I J : Ideal α) : Ideal.equivalent I J ↔ I = J := by
      match I, J with
      | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ =>
        apply Iff.intro;
        { intro eq; rw [Ideal.mk.injEq]; exact eq }
        { simp [Ideal.equivalent]; exact id }
    protected theorem antisymm [Ring α] {I J : Ideal α} (h₁ : I ⊆ J) (h₂ : J ⊆ I) : I = J := by
      rw [←Ideal.ext]; simp only [Ideal.equivalent]; rw [←Set.ext]; simp only [Set.equivalent];
      exact fun x => ⟨fun h => h₁ h, fun h => h₂ h⟩

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
    
    def coprime [Ring α] (I J : Ideal α) : Prop := I + J = UnitIdeal α

    def principal [r : Ring α] (a : α) : Ideal α where
      subset := {x | a ÷ x}
      has_zero := divides_zero a;
      add_closed := divides_add
      mul_closed := fun x => divides_mul' x

    def is_principal [Ring α] (I : Ideal α) : Prop :=
      ∃ a, a ∈ I ∧ ∀ x, x ∈ I → a ÷ x

    def is_prime [Ring α] (I : Ideal α) : Prop :=
      ∀ r s, r * s ∈ I → r ∈ I ∨ s ∈ I

    def is_maximal [Ring α] (I : Ideal α) : Prop :=
      ∀ J : Ideal α, I ⊆ J → J = I ∨ J = UnitIdeal α

    def proper_ideal [Ring α] (I : Ideal α) : Prop :=
      I ≠ UnitIdeal α

    theorem generator_in_principal [Ring α] (a : α) : a ∈ principal a := ⟨1, mul_one a⟩
    theorem principal_principal [Ring α] (a : α) : is_principal (principal a) :=
      ⟨a, ⟨divides_self a, by intro _ h; exact h⟩⟩

    theorem principal_of_is_principal [Ring α] (I : Ideal α) (h : is_principal I) : ∃ a, I = principal a := by
      let ⟨a, ⟨aI, ha⟩⟩ := h;
      exact ⟨a, by apply (Ideal.ext _ _).mp; apply Set.subset.antisymm ha;
                    intro x xp; let ⟨b, ab⟩ := xp; rw [←ab]; exact I.mul_closed' b aI⟩
                    
    theorem in_unit_ideal [Ring α] : ∀ I : Ideal α, I ⊆ UnitIdeal α := by
      intro; simp only [Subset.subset]; intros; trivial
    theorem principal_in [Ring α] (I : Ideal α) : ∀ a, a ∈ I → principal a ⊆ I := by
      intro _ aI _ ⟨y, ayx⟩; rw [←ayx]; exact mul_closed' _ _ aI;
    theorem unit_principal [Ring α] : ∀ u, isUnit u → (principal u) = UnitIdeal α := by
      intro u hu; exact Ideal.antisymm (in_unit_ideal _) (fun y _ => unit_divides u y hu);

    theorem is_unit_ideal [Ring α] {I : Ideal α} : I = UnitIdeal α ↔ 1 ∈ I := by
      apply Iff.intro (fun h => by rw [h]; trivial); intro h;
      exact Ideal.antisymm (in_unit_ideal I) (by rw [←unit_principal (1 : α) isUnit_1]; exact principal_in I 1 h);

    def ideal_chain [Ring α] (S : Set (Ideal α)) (hS : Nonempty S) (hc : Zorn.Chain Subset.subset S) : Ideal α where
      subset := ⋃₀ (Set.toSetSet S Ideal.subset)
      has_zero :=
        let ⟨⟨x, xS⟩, _⟩ := Classical.exists_true_of_nonempty hS
        ⟨x.subset, ⟨x, xS, rfl⟩, x.has_zero⟩
      add_closed := by
        intro a b ⟨i, ⟨I, IS, Ii⟩, ai⟩ ⟨j, ⟨J, JS, Jj⟩, bj⟩
        cases Classical.em (I = J) with
        | inl h =>
          rw [←Ii] at ai; rw [←h] at Jj; rw [←Jj] at bj
          exact ⟨I.subset, ⟨I, IS, rfl⟩, I.add_closed ai bj⟩
        | inr h =>
          cases hc I IS J JS h with
          | inl h =>
            rw [←Ii] at ai; rw [←Jj] at bj
            exact ⟨J.subset, ⟨J, JS, rfl⟩, J.add_closed (h ai) bj⟩
          | inr h =>
            rw [←Ii] at ai; rw [←Jj] at bj
            exact ⟨I.subset, ⟨I, IS, rfl⟩, I.add_closed ai (h bj)⟩
      mul_closed := by
        intro a b ⟨i, ⟨I, IS, Ii⟩, bi⟩
        rw [←Ii] at bi
        exact ⟨I.subset, ⟨I, IS, rfl⟩, I.mul_closed a bi⟩

    theorem ideal_chain_subset [Ring α] (S : Set (Ideal α)) {I : Ideal α} (IS : I ∈ S)
      (hc : Zorn.Chain Subset.subset S) : I ⊆ ideal_chain S ⟨I, IS⟩ hc :=
        fun x xI => ⟨I.subset, ⟨I, IS, rfl⟩, xI⟩

    theorem ideal_chain_proper [Ring α] (S : Set (Ideal α)) (hS : Nonempty S) (hc : Zorn.Chain Subset.subset S) :
      (∀ I ∈ S, I.proper_ideal) → (ideal_chain S hS hc).proper_ideal := by
        intro h hU;
        let ⟨_, ⟨I, IS, hI⟩, hIu⟩ := is_unit_ideal.mp hU;
        rw [←hI] at hIu;
        exact absurd (is_unit_ideal.mpr hIu) (h I IS)
        
  end Ideal

  namespace QuotientRing

    def QuotientRelation [Ring α] (I : Ideal α) (a b : α) : Prop := -a + b ∈ I

    theorem QuotientRelation.refl [Ring α] (I : Ideal α) (a : α) : QuotientRelation I a a := by
      simp only [QuotientRelation]; rw [neg_add]; exact I.has_zero

    def QuotClass [Ring α] (I : Ideal α) : Type _ :=
      Quot (QuotientRelation I)

    def QuotAdd [Ring α] (I : Ideal α) : QuotClass I → QuotClass I → QuotClass I :=
      Function.Quotient.map₂ (QuotientRelation I) (QuotientRelation I) (QuotientRelation I)
        (QuotientRelation.refl I) (QuotientRelation.refl I) (fun x y => x + y) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp only [QuotientRelation] at *
          rw [neg_add_distrib, add_comm (-b₁), add_assoc, ←add_assoc (-b₁), add_comm (-b₁), add_assoc, ←add_assoc];
          exact I.add_closed ha hb)

    def QuotNeg [Ring α] (I : Ideal α) : QuotClass I → QuotClass I :=
      Function.Quotient.map (QuotientRelation I) (QuotientRelation I) (fun x => -x)
        (fun x y hxy => by
          simp only [QuotientRelation] at *; rw [←neg_add_distrib, add_comm]; exact I.neg_closed hxy)

    def QuotMul [Ring α] (I : Ideal α) : QuotClass I → QuotClass I → QuotClass I := by
      apply Function.Quotient.map₂ (QuotientRelation I) (QuotientRelation I) (QuotientRelation I)
        (QuotientRelation.refl I) (QuotientRelation.refl I) (fun x y => x * y) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp only [QuotientRelation] at *
          have := I.add_closed (I.mul_closed b₁ ha) (I.mul_closed a₂ hb)
          rw [mul_distrib_left, mul_distrib_left, mul_neg, mul_comm, mul_comm b₁, add_assoc, ←add_assoc (a₂ * b₁),
            mul_neg, add_neg, zero_add] at this; exact this)

    instance QuotientRing {α : Type _} [Ring α] (I : Ideal α) : Ring (QuotClass I) where
      zero := Quot.mk (QuotientRelation I) 0
      one := Quot.mk (QuotientRelation I) 1
      add := QuotAdd I
      neg := QuotNeg I
      mul := QuotMul I
      add_zero := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QuotientRelation]
        rw [add_zero, neg_add]; exact I.has_zero
      add_assoc := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QuotientRelation]
        rw [add_assoc, neg_add]; exact I.has_zero
      add_neg := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QuotientRelation]
        rw [add_neg, neg_add]; exact I.has_zero
      add_comm := by
        apply Function.Quotient.ind₂; intro a _; apply Quot.sound; simp only [QuotientRelation]
        rw [add_comm a, neg_add]; exact I.has_zero
      mul_one := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QuotientRelation]
        rw [mul_one, neg_add]; exact I.has_zero
      one_mul := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QuotientRelation]
        rw [one_mul, neg_add]; exact I.has_zero
      mul_assoc := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QuotientRelation]
        rw [mul_assoc, neg_add]; exact I.has_zero
      mul_distrib_left := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QuotientRelation]
        rw [mul_distrib_left, neg_add]; exact I.has_zero
      mul_distrib_right := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QuotientRelation]
        rw [mul_distrib_right, neg_add]; exact I.has_zero
      mul_comm := by
        apply Function.Quotient.ind₂; intros; apply Quot.sound; simp only [QuotientRelation]
        rw [mul_comm, neg_add]; exact I.has_zero

  end QuotientRing
end M4R