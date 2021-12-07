import M4R.Algebra.Group.Basic

namespace M4R
  namespace SubGroup
  
    instance SubGroupToSet {α : Type u} [Group α] : CoeSort (SubGroup α) (Set α) where
      coe := fun s => s.subset

    def Self (α : Type _) [Group α] : SubGroup α where
      subset   := Set.Universal
      has_zero := trivial
      add_closed := by intros; trivial
      neg_closed := by intros; trivial

    def Trivial (α : Type _) [g : Group α] : SubGroup α where
      subset     := {x | x = 0}
      has_zero   := by trivial
      add_closed := by intro _ _ a0 b0; rw [a0, b0, g.add_zero]; trivial
      neg_closed := by intro a a0; rw[a0, g.neg_zero]; trivial

    protected theorem ext [Group α] (s₁ s₂ : SubGroup α) : s₁.subset = s₂.subset ↔ s₁ = s₂ :=
      ⟨match s₁, s₂ with
      | ⟨ss₁, h0₁, ha₁, hn₁⟩, ⟨ss₂, h0₂, ha₂, hn₂⟩ => by rw [SubGroup.mk.injEq]; exact id,
      by intro h; rw [h]⟩

    theorem trivialExt [Group α] (s : SubGroup α) : s = Trivial α ↔ (∀ x ∈ s.subset, x = 0) := by
      rw [←(SubGroup.ext s (Trivial α))]; exact ⟨fun hs => by rw [hs]; exact (fun _ xs => xs),
        fun hx => by rw [←Set.ext]; exact (fun x => ⟨fun xs => hx x xs,
          fun x0 => by rw [x0]; exact s.has_zero⟩)⟩

    protected def image [Group α] (s : SubGroup α) (a : α) (p : a ∈ s.subset) : ↑s.subset := ⟨a, p⟩
    protected theorem image_eq [Group α] (s : SubGroup α) (a b : ↑s.subset) :
      a = b ↔ Set.inclusion a = Set.inclusion b :=
        ⟨congrArg Set.inclusion, Set.elementExt a b⟩
    
    instance SubGroupGroup [Group α] (s : SubGroup α) : Group ↑s.subset where
      zero := ⟨0, s.has_zero⟩
      add := fun x y => ⟨x.val + y.val, s.add_closed x.val y.val x.property y.property⟩
      neg := fun x => ⟨-x.val, s.neg_closed x.val x.property⟩
      add_zero := by
        intro a; rw [SubGroup.image_eq] exact Group.add_zero a.val
      add_assoc := by
        intro a b c; rw [SubGroup.image_eq]; exact Group.add_assoc a.val b.val c.val
      add_neg := by
        intro a; rw [SubGroup.image_eq]; exact Group.add_neg a.val
      
  end SubGroup

  class NormalSubGroup [Group α] (s : SubGroup α) where
    normal : ∀ a, a ∈ s.subset → ∀ g, -g + a + g ∈ s.subset

  -- i.e. left coset equivalence
  def QuotientRelation [Group α] (s : SubGroup α) (a b : α) : Prop := -a + b ∈ s.subset
  theorem QuotientRelation.refl [g : Group α] (s : SubGroup α) (a : α) : QuotientRelation s a a := by
    simp [QuotientRelation]; rw [g.neg_add]; exact s.has_zero;

  def QuotClass [Group α] (s : SubGroup α) : Type _ :=
    Quot (QuotientRelation s)

  def QuotAdd [g : Group α] (s : SubGroup α) [N : NormalSubGroup s] : QuotClass s → QuotClass s → QuotClass s :=
    Function.Quotient.map₂ (QuotientRelation s) (QuotientRelation s) (QuotientRelation s)
      (QuotientRelation.refl s) (QuotientRelation.refl s) (fun x y => x + y) (fun a₁ a₂ b₁ b₂ ha hb => by
        simp [QuotientRelation] at *; rw [g.neg_add_distrib, ←g.add_zero (-b₁), ←g.add_neg b₂, ←g.add_assoc (-b₁),
        g.add_assoc, g.add_assoc]; apply s.add_closed; exact hb; rw [←g.add_assoc, ←g.add_assoc, g.add_assoc (-b₂)];
        exact N.normal (-a₁ + a₂) ha b₂)

  def QuotInv [g : Group α] (s : SubGroup α) [N : NormalSubGroup s] : QuotClass s → QuotClass s :=
    Function.Quotient.map (QuotientRelation s) (QuotientRelation s) (fun x => -x)
      (fun x y hxy => by
        simp [QuotientRelation] at *; rw [←g.neg_add_distrib]; apply s.neg_closed;
        rw[←g.zero_add y, ←g.neg_add (-x), g.add_assoc (- -x)]; exact N.normal (-x + y) hxy (-x))

  instance QuotientGroup (α : Type _) [g : Group α] (s : SubGroup α) [N : NormalSubGroup s] : Group (QuotClass s) where
    zero := Quot.mk (QuotientRelation s) 0
    add := QuotAdd s
    neg := QuotInv s
    add_zero := by
      apply Quot.ind; intro a; apply Quot.sound; simp [QuotientRelation];
      rw [g.neg_add_distrib, g.neg_zero, g.zero_add, g.neg_add]; exact s.has_zero
    add_assoc := by
      apply Function.Quotient.ind₃; intro a b c; apply Quot.sound; simp [QuotientRelation];
      rw [g.neg_add_distrib, g.neg_add_distrib, ←g.add_assoc, g.add_assoc (-c), g.add_assoc (-b), g.neg_add,
      g.add_zero, ←g.add_assoc, g.add_assoc (-c), g.neg_add, g.add_zero, g.neg_add]; exact s.has_zero
    add_neg := by
      apply Quot.ind; intro a; apply Quot.sound; simp [QuotientRelation];
      rw [g.add_neg, g.neg_add]; exact s.has_zero

  def LeftCoset [Group α] (a : α) (s : Set α) : Set α := {x | -a + x ∈ s}
  def RightCoset [Group α] (s : Set α) (a : α) : Set α := {x | x + -a ∈ s}
  
  namespace LeftCoset
    instance LeftCosetHAddInt [Group α] : HAdd α (Set α) (Set α) where hAdd := LeftCoset
    theorem comp [g : Group α] (a b : α) (s : Set α) : a + (b + s) = (a + b) + s := by
      simp [HAdd.hAdd, LeftCoset]
      apply funext; intro x; apply propext; apply Iff.intro
      { intro h; have : Add.add (-Add.add a b) x = -(a + b) + x := rfl
      rw [this, g.neg_add_distrib, g.add_assoc]; exact h }
      intro h; simp [Mem.mem, Set.mem]; have : Add.add (-b) (Add.add (-a) x) = -b + (-a + x) := rfl
      rw [this, ←g.add_assoc, ←g.neg_add_distrib]; exact h
  end LeftCoset

  namespace RightCoset
    instance RightCosetHAddInt [Group α] : HAdd (Set α) α (Set α) where hAdd := RightCoset
    theorem comp [g : Group α] (s : Set α) (a b : α) : (s + a) + b = s + (a + b) := by
      simp [HAdd.hAdd, RightCoset]
      apply funext; intro x; apply propext; apply Iff.intro
      { intro h; have : Add.add x (-Add.add a b) = x + -(a + b) := rfl
      rw [this, g.neg_add_distrib, ←g.add_assoc]; exact h }
      intro h; simp [Mem.mem, Set.mem]; have : Add.add (Add.add x (-b)) (-a) = (x + -b) + -a := rfl
      rw [this, g.add_assoc, ←g.neg_add_distrib]; exact h
  end RightCoset
end M4R