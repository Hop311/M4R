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

      protected theorem antisymm {a b : Set α} (hab : a ⊆ b) (hba : b ⊆ a) : a = b := by
        apply Set.equivalent.ext.mp; intro x; apply Iff.intro
        { intro hxa; exact hab x hxa }
        { intro hxb; exact hba x hxb }
        
      protected theorem antisymmIff {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a := by
        apply Iff.intro
        { intro heq; rw [heq, and_self]; exact Set.subset.refl b }
        { intro ⟨hab, hba⟩; exact Set.subset.antisymm hab hba }
      
      theorem neqEq (s₁ s₂ : Set α) : s₁ ⊊ s₂ → s₁ ⊆ s₂ := by
        intro h a; exact h.left a
      theorem inSubset (s₁ s₂ : Set α) (a : α) : a ∈ s₁ ∧ s₁ ⊆ s₂ → a ∈ s₂ := by
        intro ⟨hsa, hsub⟩; exact hsub a hsa

      theorem subUniversal (s : Set α) : s ⊆ Set.Universal := by
        intro _ _; trivial

    end subset
  end Set
end M4R