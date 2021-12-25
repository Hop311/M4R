import M4R.Algebra.Ring.Basic

namespace M4R
  open NonCommutativeRing

  namespace SubRing

    def Self (α : Type _) [NonCommutativeRing α] : SubRing α where
      toSubGroup := SubGroup.Self α
      has_one := trivial
      mul_closed := by intros; trivial

    protected theorem ext [NonCommutativeRing α] (s₁ s₂ : SubRing α) : s₁.subset = s₂.subset ↔ s₁ = s₂ := by
      rw [SubGroup.ext s₁.toSubGroup s₂.toSubGroup];
      exact ⟨match s₁, s₂ with
      | ⟨_, _, _⟩, ⟨_, _, _⟩ => by rw [SubRing.mk.injEq]; exact id,
      by intro h; rw [h]⟩

    protected def image [NonCommutativeRing α] (s : SubRing α) (a : α) (p : a ∈ s.subset) : ↑s.subset := ⟨a, p⟩
    protected theorem image_eq [NonCommutativeRing α] (s : SubRing α) (a b : ↑s.subset) :
      a = b ↔ Set.inclusion a = Set.inclusion b :=
        ⟨congrArg Set.inclusion, Set.elementExt⟩
        
    instance SubRingRing [NonCommutativeRing α] (s : SubRing α) : NonCommutativeRing ↑s.subset where
      toAbelianGroup := AbelianGroup.SubGroupAbelian s.toSubGroup
      one               := ⟨1, s.has_one⟩
      mul               := fun x y => ⟨x.val * y.val, s.mul_closed x.val y.val x.property y.property⟩
      mul_one           := by intro a; rw [SubRing.image_eq]; exact mul_one a.val
      one_mul           := by intro a; rw [SubRing.image_eq]; exact one_mul a.val
      mul_assoc         := by intro a b c; rw [SubRing.image_eq]; exact mul_assoc a.val b.val c.val
      mul_distrib_left  := by intro a b c; rw [SubRing.image_eq]; exact mul_distrib_left a.val b.val c.val
      mul_distrib_right := by intro a b c; rw [SubRing.image_eq]; exact mul_distrib_right a.val b.val c.val
      
  end SubRing
end M4R