import M4R.Algebra.Ring.Defs

namespace M4R
  open NCSemiring
  open Semiring

  namespace SubSemiring

    def Self (α : Type _) [NCSemiring α] : SubSemiring α where
      toSubMonoid := SubMonoid.Self α
      has_one := trivial
      mul_closed := by intros; trivial

    protected theorem ext [NCSemiring α] (s₁ s₂ : SubSemiring α) : s₁.subset = s₂.subset ↔ s₁ = s₂ :=
      ⟨match s₁, s₂ with | ⟨_, _, _⟩, ⟨_, _, _⟩ => by rw [SubSemiring.mk.injEq]; exact (SubMonoid.ext _ _).mp,
      fun h => by rw [h]⟩

    protected instance toNCSemiring [NCSemiring α] (s : SubSemiring α) : NCSemiring ↑s.subset where
      one := ⟨1, s.has_one⟩
      mul := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, s.mul_closed x hx y hy⟩
      mul_one := fun ⟨a, _⟩ => Set.elementExt (mul_one a)
      one_mul := fun ⟨a, _⟩ => Set.elementExt (one_mul a)
      mul_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_assoc a b c)
      mul_distrib_left := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_distrib_left a b c)
      mul_distrib_right := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_distrib_right a b c)
      mul_zero := fun ⟨a, _⟩ => Set.elementExt (mul_zero a)
      zero_mul := fun ⟨a, _⟩ => Set.elementExt (zero_mul a)

    protected instance toSemiring [Semiring α] (s : SubSemiring α) : Semiring ↑s.subset where
      toNCSemiring := s.toNCSemiring
      mul_comm := fun ⟨a, _⟩ ⟨b, _⟩ => Set.elementExt (mul_comm a b)
  
  end SubSemiring

  namespace SubRing

    def Self (α : Type _) [NCRing α] : SubRing α where
      toSubSemiring := SubSemiring.Self α
      neg_closed := (SubGroup.Self α).neg_closed

    protected theorem ext [NCRing α] (s₁ s₂ : SubRing α) : s₁.subset = s₂.subset ↔ s₁ = s₂ :=
      ⟨match s₁, s₂ with | ⟨a, b⟩, ⟨c, d⟩ => by rw [SubRing.mk.injEq]; exact (SubSemiring.ext _ _).mp, by intro h; rw [h]⟩

    protected instance toNCRing [NCRing α] (s : SubRing α) : NCRing ↑s.subset where
      toNeg := s.toSubGroup.toGroup.toNeg
      add_neg := s.toSubGroup.toGroup.add_neg
    
    protected instance toRing [Ring α] (s : SubRing α) : Ring ↑(s.subset) where
      mul_comm := s.toSemiring.mul_comm

  end SubRing
end M4R