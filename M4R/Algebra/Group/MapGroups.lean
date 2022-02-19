import M4R.Algebra.Group.GMorphism

namespace M4R

  section Map

    instance MapZero (α : Type _) (β : Type _) [Zero β] : Zero (α → β) where zero := fun _ => 0

    protected theorem MapZero.def {α : Type _} {β : Type _} [Zero β] (a : α) :
      (0 : α → β) a = 0 := rfl

    instance MapAdd (α : Type _) (β : Type _) [Monoid β] : Add (α → β) where add := fun x y a => x a + y a

    protected theorem MapAdd.def {α : Type _} {β : Type _} [Monoid β] {x y : α → β} (a : α) :
      (x + y) a = x a + y a := rfl

    instance MapMonoid (α : Type _) (β : Type _) [Monoid β] : Monoid (α → β) where
      add_zero := fun x => funext fun _ => Monoid.add_zero _
      zero_add := fun x => funext fun a => by conv => rhs rw [←Monoid.zero_add (x a)]
      add_assoc := fun x y z => funext fun a => Monoid.add_assoc _ _ _

    instance MapCommMonoid (α : Type _) (β : Type _) [CommMonoid β] : CommMonoid (α → β) where
      add_comm := fun x y => funext fun a => CommMonoid.add_comm _ _

    instance MapNeg (α : Type _) (β : Type _) [Group β] : Neg (α → β) where neg := fun x a => - x a

    protected theorem MapNeg.def {α : Type _} {β : Type _} [Group β] {x : α → β} (a : α) :
      (- x) a = - x a := rfl

    instance MapGroup (α : Type _) (β : Type _) [Group β] : Group (α → β) where
      add_neg := fun _ => funext fun _ => Group.add_neg _

    instance MapAbelianGroup (α : Type _) (β : Type _) [AbelianGroup β] : AbelianGroup (α → β) where
      add_comm := (MapCommMonoid α β).add_comm

  end Map

  section MHomomorphism

    instance MHomomorphismZero (α : Type _) (β : Type _) [Monoid α] [Monoid β] : Zero (α →₊ β) where
      zero := {
        hom           := 0
        preserve_zero := rfl
        preserve_add  := by intros; simp only [MapZero.def, Monoid.add_zero]
      }

    protected theorem MHomomorphismZero.def {α : Type _} {β : Type _} [Monoid α] [Monoid β] (a : α) :
      (0 : α →₊ β) a = 0 := rfl

    instance MHomomorphismAdd (α : Type _) (β : Type _) [Monoid α] [CommMonoid β] : Add (α →₊ β) where
      add := fun x y => {
        hom := x.hom + y.hom
        preserve_zero := by rw [MapAdd.def, x.preserve_zero, y.preserve_zero, Monoid.add_zero]
        preserve_add := by
          intros; simp only [MapAdd.def]
          rw [x.preserve_add, y.preserve_add, ←Monoid.add_assoc, ←Monoid.add_assoc,
            CommMonoid.add_right_comm (x _)]
      }

    protected theorem MHomomorphismAdd.def {α : Type _} {β : Type _} [Monoid α] [CommMonoid β] {x y : α →₊ β} (a : α) :
      (x + y) a = x a + y a := rfl

    instance MHomomorphismCommMonoid (α : Type _) (β : Type _) [Monoid α] [CommMonoid β] : CommMonoid (α →₊ β) where
      add_zero := fun x => by
        apply MHomomorphism.ext.mpr; apply funext; intro a;
        rw [MHomomorphismAdd.def, MHomomorphismZero.def]; exact Monoid.add_zero _
      zero_add := fun x => by
        apply MHomomorphism.ext.mpr; apply funext; intro a;
        rw [MHomomorphismAdd.def, MHomomorphismZero.def]; exact Monoid.zero_add _
      add_assoc := fun x y z => by
        apply MHomomorphism.ext.mpr; apply funext; intro a;
        simp only [MHomomorphismAdd.def]; exact Monoid.add_assoc _ _ _
      add_comm := fun x y => by
        apply MHomomorphism.ext.mpr; apply funext; intro a;
        simp only [MHomomorphismAdd.def]; exact CommMonoid.add_comm _ _

  end MHomomorphism

  section GHomomorphism

    instance GHomomorphismZero (α : Type _) (β : Type _) [Group α] [AbelianGroup β] : Zero (α →₋ β) where
      zero := {
        toMHomomorphism := 0
        preserve_neg := by
          intros; simp only [MHomomorphismZero.def]; exact Group.neg_zero.symm
      }

    protected theorem GHomomorphismZero.def {α : Type _} {β : Type _} [Group α] [AbelianGroup β] (a : α) :
      (0 : α →₋ β) a = 0 := rfl

    instance GHomomorphismAdd (α : Type _) (β : Type _) [Group α] [AbelianGroup β] : Add (α →₋ β) where
      add := fun x y => {
        toMHomomorphism := x.toMHomomorphism + y.toMHomomorphism
        preserve_neg := by
          intros; simp only [MHomomorphismAdd.def]
          rw [x.preserve_neg, y.preserve_neg, AbelianGroup.neg_add_distrib]
      }

    protected theorem GHomomorphismAdd.def {α : Type _} {β : Type _} [Group α] [AbelianGroup β] {x y : α →₋ β} (a : α) :
      (x + y) a = x a + y a := rfl

    instance GHomomorphismNeg (α : Type _) (β : Type _) [Group α] [AbelianGroup β] : Neg (α →₋ β) where
      neg := fun x => {
        hom := -x.hom
        preserve_zero := by rw [MapNeg.def, x.preserve_zero]; exact Group.neg_zero
        preserve_add := by intros; simp only [MapNeg.def]; rw [x.preserve_add, AbelianGroup.neg_add_distrib]
        preserve_neg := by intros; simp only [MapNeg.def]; rw [x.preserve_neg]
      }

    protected theorem GHomomorphismNeg.def {α : Type _} {β : Type _} [Group α] [AbelianGroup β] {x : α →₋ β} (a : α) :
      (-x) a = - x a := rfl

    instance GHomomorphismAbelianGroup (α : Type _) (β : Type _) [Group α] [AbelianGroup β] : AbelianGroup (α →₋ β) where
      add_zero := fun x => by
        apply GHomomorphism.ext.mpr; apply funext; intro a
        rw [GHomomorphismAdd.def, GHomomorphismZero.def]; exact Monoid.add_zero _
      zero_add := fun x => by
        apply GHomomorphism.ext.mpr; apply funext; intro a
        rw [GHomomorphismAdd.def, GHomomorphismZero.def]; exact Monoid.zero_add _
      add_assoc := fun x y z => by
        apply GHomomorphism.ext.mpr; exact Monoid.add_assoc _ _ _
      add_comm := fun x y => by
        apply GHomomorphism.ext.mpr; exact CommMonoid.add_comm _ _
      add_neg := fun x => by
        apply GHomomorphism.ext.mpr; apply funext; intro a
        rw [GHomomorphismAdd.def, GHomomorphismNeg.def, GHomomorphismZero.def]; exact Group.add_neg _


  end GHomomorphism

end M4R