import M4R.Algebra.Ring.Basic

namespace M4R
  open NCRing
  open Ring

  namespace SubRing

    def Self (α : Type _) [NCRing α] : SubRing α where
      toSubGroup := SubGroup.Self α
      has_one := trivial
      mul_closed := by intros; trivial

    protected theorem ext [NCRing α] (s₁ s₂ : SubRing α) : s₁.subset = s₂.subset ↔ s₁ = s₂ := by
      rw [SubGroup.ext s₁.toSubGroup s₂.toSubGroup];
      exact ⟨match s₁, s₂ with | ⟨_, _, _⟩, ⟨_, _, _⟩ => by rw [SubRing.mk.injEq]; exact id,
        by intro h; rw [h]⟩

    protected instance toNCRing [NCRing α] (s : SubRing α) : NCRing ↑s.subset where
      toAbelianGroup := s.toAbelianGroup
      one               := ⟨1, s.has_one⟩
      mul               := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, s.mul_closed x hx y hy⟩
      mul_one           := fun ⟨a, _⟩ => Set.elementExt (mul_one a)
      one_mul           := fun ⟨a, _⟩ => Set.elementExt (one_mul a)
      mul_assoc         := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_assoc a b c)
      mul_distrib_left  := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_distrib_left a b c)
      mul_distrib_right := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_distrib_right a b c)
    
    protected instance toRing [Ring α] (s : SubRing α) : Ring ↑(s.subset) where
      toNCRing := s.toNCRing
      mul_comm := fun ⟨a, _⟩ ⟨b, _⟩ => Set.elementExt (mul_comm a b)

  end SubRing
end M4R