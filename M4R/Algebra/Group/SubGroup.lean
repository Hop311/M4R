import M4R.Algebra.Group.Group

namespace M4R
  open Monoid CommMonoid Group AbelianGroup

  namespace SubMonoid

    def Self (α : Type _) [Monoid α] : SubMonoid α where
      subset   := Set.Universal
      has_zero := trivial
      add_closed := by intros; trivial

    def Trivial (α : Type _) [Monoid α] : SubMonoid α where
      subset     := {x | x = 0}
      has_zero   := by trivial
      add_closed := fun _ a0 _ b0 => by rw [a0, b0, add_zero]; trivial

    protected theorem ext [Monoid α] (s₁ s₂ : SubMonoid α) : s₁.subset = s₂.subset ↔ s₁ = s₂ :=
      ⟨match s₁, s₂ with | ⟨_, _, _⟩, ⟨_, _, _⟩ => by rw [SubMonoid.mk.injEq]; exact id,
      fun h => by rw [h]⟩

    protected instance toMonoid [Monoid α] (s : SubMonoid α) : Monoid ↑s.subset where
      zero := ⟨0, s.has_zero⟩
      add := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, s.add_closed x hx y hy⟩
      add_zero := fun ⟨a, _⟩ => Set.elementExt (add_zero a)
      zero_add := fun ⟨a, _⟩ => Set.elementExt (zero_add a)
      add_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (add_assoc a b c)

    protected instance toCommMonoid [CommMonoid α] (s : SubMonoid α) : CommMonoid ↑s.subset where
      add_comm := fun ⟨a, _⟩ ⟨b, _⟩ => Set.elementExt (add_comm a b)

  end SubMonoid

  namespace SubGroup

    def Self (α : Type _) [Group α] : SubGroup α where
      toSubMonoid := SubMonoid.Self α
      neg_closed := by intros; trivial

    def Trivial (α : Type _) [Group α] : SubGroup α where
      toSubMonoid := SubMonoid.Trivial α
      neg_closed := fun a a0 => by rw[a0, neg_zero]; trivial

    protected theorem ext [Group α] (s₁ s₂ : SubGroup α) : s₁.subset = s₂.subset ↔ s₁ = s₂ :=
      ⟨match s₁, s₂ with | ⟨_, _⟩, ⟨_, _⟩ => by rw [SubGroup.mk.injEq]; exact (SubMonoid.ext _ _).mp,
      fun h => by rw [h]⟩

    theorem trivialExt [Group α] (s : SubGroup α) : s = Trivial α ↔ (∀ x ∈ s, x = 0) := by
      rw [←(SubGroup.ext s (Trivial α))]; exact ⟨fun hs => by
        simp only [Mem.mem]; rw [hs]; exact (fun _ => id),
        fun hx => by rw [←Set.ext]; exact fun x => ⟨hx x,
          fun x0 => by rw [x0]; exact s.has_zero⟩⟩

    protected instance toGroup [Group α] (s : SubGroup α) : Group ↑s.subset where
      neg := fun ⟨x, hx⟩ => ⟨-x, s.neg_closed x hx⟩
      add_neg := fun ⟨a, _⟩ => Set.elementExt (add_neg a)

    protected instance toAbelianGroup [AbelianGroup α] (s : SubGroup α) : AbelianGroup ↑s.subset where
      add_comm := s.toCommMonoid.add_comm

  end SubGroup

  def SubGroup.is_normal [Group α] (s : SubGroup α) : Prop :=
    ∀ a : α, a ∈ s → ∀ g, -g + a + g ∈ s

  namespace QuotientGroup
    variable [Group α] (s : SubGroup α)

    -- i.e. left coset equivalence
    def QuotientRelation (a b : α) : Prop := -a + b ∈ s
    theorem QuotientRelation.refl [Group α] (s : SubGroup α) (a : α) : QuotientRelation s a a := by
      simp only [QuotientRelation]; rw [neg_add]; exact s.has_zero;

    def QuotClass : Type _ :=
      Quot (QuotientRelation s)

    def QuotAdd (N : s.is_normal) : QuotClass s → QuotClass s → QuotClass s :=
      Function.Quotient.map₂ (QuotientRelation s) (QuotientRelation s) (QuotientRelation s)
        (QuotientRelation.refl s) (QuotientRelation.refl s) (fun x y => x + y) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp only [QuotientRelation] at *; rw [neg_add_distrib, ←add_zero (-b₁), ←add_neg b₂, ←add_assoc (-b₁),
          add_assoc, add_assoc]; apply s.add_closed; exact hb; rw [←add_assoc, ←add_assoc, add_assoc (-b₂)];
          exact N (-a₁ + a₂) ha b₂)

    def QuotNeg (N : s.is_normal) : QuotClass s → QuotClass s :=
      Function.Quotient.map (QuotientRelation s) (QuotientRelation s) (fun x => -x)
        (fun x y hxy => by
          simp only [QuotientRelation] at *; rw [←neg_add_distrib]; apply s.neg_closed;
          rw[←zero_add y, ←neg_add (-x), add_assoc (- -x)]; exact N (-x + y) hxy (-x))

    protected instance toGroup (α : Type _) (N : s.is_normal) : Group (QuotClass s) := Group.construct
    {
      zero := Quot.mk (QuotientRelation s) 0
      add := QuotAdd s N
      neg := QuotNeg s N
      add_zero := by
        apply Quot.ind; intro a; apply Quot.sound; simp only [QuotientRelation];
        rw [neg_add_distrib, neg_zero, zero_add, neg_add]; exact s.has_zero
      add_assoc := by
        apply Function.Quotient.ind₃; intro a b c; apply Quot.sound; simp only [QuotientRelation];
        rw [neg_add_distrib, neg_add_distrib, ←add_assoc, add_assoc (-c), add_assoc (-b), neg_add,
        add_zero, ←add_assoc, add_assoc (-c), neg_add, add_zero, neg_add]; exact s.has_zero
      add_neg := by
        apply Quot.ind; intro a; apply Quot.sound; simp only [QuotientRelation];
        rw [add_neg, neg_add]; exact s.has_zero
    }
    def LeftCoset (a : α) (s : Set α) : Set α := {x | -a + x ∈ s}
    def RightCoset (s : Set α) (a : α) : Set α := {x | x + -a ∈ s}

    namespace LeftCoset
      instance LeftCosetHAddInt : HAdd α (Set α) (Set α) where hAdd := LeftCoset
      theorem comp (a b : α) (s : Set α) : a + (b + s) = (a + b) + s := by
        simp only [HAdd.hAdd, LeftCoset]
        apply funext; intro x; apply propext; apply Iff.intro
        { intro h; have : Add.add (-Add.add a b) x = -(a + b) + x := rfl
        rw [this, neg_add_distrib, add_assoc]; exact h }
        intro h; simp only [Mem.mem, Set.mem]; have : Add.add (-b) (Add.add (-a) x) = -b + (-a + x) := rfl
        rw [this, ←add_assoc, ←neg_add_distrib]; exact h
    end LeftCoset

    namespace RightCoset
      instance RightCosetHAddInt : HAdd (Set α) α (Set α) where hAdd := RightCoset
      theorem comp (s : Set α) (a b : α) : (s + a) + b = s + (a + b) := by
        simp only [HAdd.hAdd, RightCoset]
        apply funext; intro x; apply propext; apply Iff.intro
        { intro h; have : Add.add x (-Add.add a b) = x + -(a + b) := rfl
        rw [this, neg_add_distrib, ←add_assoc]; exact h }
        intro h; simp only [Mem.mem, Set.mem]; have : Add.add (Add.add x (-b)) (-a) = (x + -b) + -a := rfl
        rw [this, add_assoc, ←neg_add_distrib]; exact h
    end RightCoset
  end QuotientGroup
end M4R
