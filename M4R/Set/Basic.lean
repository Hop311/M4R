import M4R.Set.Defs

namespace M4R
  namespace Set

    protected theorem ext {s : Set α} : ∀ a b : s, inclusion a = inclusion b → a = b
    | ⟨_, _⟩, ⟨_, _⟩, heq => by rw [Subtype.mk.injEq]; exact heq

    /- Set instances -/
    instance EmptySet : Set α := Set.Empty
    instance SetInhabited : Inhabited (Set α) where default := EmptySet
    instance UniversalSet : Set α := Set.Universal
    instance SingletonSet [Singleton α] : Set α := UniversalSet
    def SingletonSet.mk {α : Type _} (a : α) : Set α := {x | x = a}

    namespace equivalent
    
      protected theorem refl (s : Set α) : Set.equivalent s s := by
        intro _; exact Iff.rfl
      protected theorem symm {s₁ s₂ : Set α} : Set.equivalent s₁ s₂ → Set.equivalent s₂ s₁ := by
        intro heq a; exact Iff.symm (heq a)
      protected theorem trans {s₁ s₂ s₃ : Set α} : Set.equivalent s₁ s₂ → Set.equivalent s₂ s₃ → Set.equivalent s₁ s₃ := by
        intro h12 h23 a; exact Iff.trans (h12 a) (h23 a)

      instance SetEquivalence : Equivalence (@Set.equivalent α) where
        refl := equivalent.refl
        symm := equivalent.symm
        trans := equivalent.trans

      theorem ext {s₁ s₂ : Set α} : Set.equivalent s₁ s₂ ↔ s₁ = s₂ := by
          apply Iff.intro
          { intro hiff; apply funext; intro a; exact propext (hiff a) }
          { intro heq a; rw [heq]; exact Iff.refl (s₂ a) }
    
    end equivalent
    
    namespace subset

      protected theorem refl (s : Set α) : s ⊆ s := by
        intro _ as; exact as
        
      protected theorem antisymmIff {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a := by
        rw [Subset.ext a b, ←Set.equivalent.ext]; simp [Set.equivalent]
      
      protected theorem antisymm {a b : Set α} (hab : a ⊆ b) (hba : b ⊆ a) : a = b :=
        Set.subset.antisymmIff.mpr ⟨hab, hba⟩

      theorem subUniversal (s : Set α) : s ⊆ Set.Universal := by
        intro _ _; trivial
        
    end subset
  end Set
end M4R