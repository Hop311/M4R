import M4R.Algebra.Ring.Basic
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

    theorem mul_closed' [Ring α] (I : Ideal α) : ∀ {a : α},  a ∈ I → (b : α) → a * b ∈ I := by
      intro a as b; rw [mul_comm]; exact I.mul_closed b as

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
    protected theorem ext [Ring α] {I J : Ideal α} : Ideal.equivalent I J ↔ I = J := by
      match I, J with
      | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ =>
        apply Iff.intro;
        { intro eq; rw [Ideal.mk.injEq]; exact eq }
        { simp [Ideal.equivalent]; exact id }
    protected theorem antisymm [Ring α] {I J : Ideal α} (h₁ : I ⊆ J) (h₂ : J ⊆ I) : I = J := by
      rw [←Ideal.ext]; simp only [Ideal.equivalent]; rw [←Set.ext]; simp only [Set.equivalent];
      exact fun x => ⟨fun h => h₁ h, fun h => h₂ h⟩

    protected def add [Ring α] (I J : Ideal α) : Ideal α where
      subset := {x | ∃ i ∈ I, ∃ j ∈ J, i + j = x }
      has_zero := ⟨0, I.has_zero, 0, J.has_zero, show 0 + 0 = 0 by rw [add_zero 0]⟩
      add_closed := fun ⟨ia, hia, ja, hja, hija⟩ ⟨ib, hib, jb, hjb, hijb⟩ =>
        ⟨
          ia + ib, I.add_closed hia hib,
          ja + jb, J.add_closed hja hjb,
          by rw [add_assoc, add_comm ib, add_assoc, add_comm jb, ←add_assoc, hija, hijb]
        ⟩
      mul_closed := fun a b ⟨i, hi, j, hj, hij⟩ =>
        ⟨
          a*i, I.mul_closed a hi,
          a*j, J.mul_closed a hj,
          by rw [←mul_distrib_left, hij]
        ⟩
    instance IdealAdd [Ring α] : Add (Ideal α) where add := Ideal.add

    protected theorem add.comm [Ring α] (I J : Ideal α) : I + J = J + I :=
      have : ∀ {K L : Ideal α}, K + L ⊆ L + K := by
        intro K L x ⟨i, hi, j, hj, hij⟩;
        exact ⟨j, hj, i, hi, by rw [add_comm]; exact hij⟩
      Ideal.antisymm this this

    protected theorem add.subset [Ring α] (I J : Ideal α) : I ⊆ I + J :=
      fun x hx => ⟨x, hx, 0, J.has_zero, add_zero x⟩
    protected theorem add.of_subset [Ring α] {I J : Ideal α} (h : I ⊆ J) : I + J = J := by
      apply Ideal.antisymm
      intro x ⟨i, iI, j, jJ, hij⟩; rw [←hij]; exact J.add_closed (h iI) jJ
      rw [Ideal.add.comm]; exact Ideal.add.subset J I

    def coprime [Ring α] (I J : Ideal α) : Prop := I + J = UnitIdeal α

    def principal [r : Ring α] (a : α) : Ideal α where
      subset := {x | a ÷ x}
      has_zero := divides_zero a;
      add_closed := divides_add
      mul_closed := fun x => divides_mul' x

    def is_principal [Ring α] (I : Ideal α) : Prop :=
      ∃ a, a ∈ I ∧ ∀ x, x ∈ I → a ÷ x

    def proper_ideal [Ring α] (I : Ideal α) : Prop :=
      I ≠ UnitIdeal α

    theorem generator_in_principal [Ring α] (a : α) : a ∈ principal a := ⟨1, mul_one a⟩
    theorem principal_principal [Ring α] (a : α) : is_principal (principal a) :=
      ⟨a, ⟨divides_self a, by intro _ h; exact h⟩⟩

    theorem principal_of_is_principal [Ring α] (I : Ideal α) (h : is_principal I) : ∃ a, I = principal a := by
      let ⟨a, ⟨aI, ha⟩⟩ := h;
      exact ⟨a, by apply Ideal.ext.mp; apply Set.subset.antisymm ha;
                    intro x xp; let ⟨b, ab⟩ := xp; rw [←ab]; exact I.mul_closed' aI b⟩

    theorem in_unit_ideal [Ring α] : ∀ I : Ideal α, I ⊆ UnitIdeal α := by
      intro; simp only [Subset.subset]; intros; trivial
    theorem principal_in [Ring α] (I : Ideal α) : ∀ a ∈ I, principal a ⊆ I := by
      intro _ aI _ ⟨y, ayx⟩; rw [←ayx]; exact mul_closed' _ aI _;
    theorem unit_principal [Ring α] : ∀ u, isUnit u → (principal u) = UnitIdeal α := by
      intro u hu; exact Ideal.antisymm (in_unit_ideal _) (fun y _ => unit_divides u y hu);

    theorem is_unit_ideal [Ring α] {I : Ideal α} : I = UnitIdeal α ↔ 1 ∈ I := by
      apply Iff.intro (fun h => by rw [h]; trivial); intro h;
      exact Ideal.antisymm (in_unit_ideal I) (by rw [←unit_principal (1 : α) isUnit_1]; exact principal_in I 1 h);

  end Ideal
end M4R