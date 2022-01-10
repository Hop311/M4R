import M4R.Set.Defs
import M4R.Logic

namespace M4R
  namespace Set

    protected theorem elementExt {s : Set α} : ∀ {a b : ↑s}, inclusion a = inclusion b → a = b
    | ⟨_, _⟩, ⟨_, _⟩, heq => by rw [Subtype.mk.injEq]; exact heq

    /- Set instances -/
    def SetInhabited : Inhabited (Set α) where default := Set.Empty
    def SingletonSet [Singleton α] : Set α := Set.Universal
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

    end equivalent

    protected theorem ext {s₁ s₂ : Set α} : Set.equivalent s₁ s₂ ↔ s₁ = s₂ := by
          apply Iff.intro
          { intro hiff; apply funext; intro a; exact propext (hiff a) }
          { intro heq a; rw [heq]; exact Iff.refl (s₂ a) }

    protected theorem nonempty {s : Set α} : s ≠ ∅ ↔ Nonempty s :=
      ⟨fun h =>
        have : ∃ x, x ∈ s := Classical.byContradiction fun hn =>
          h (Set.ext.mp fun x =>
            ⟨fun xs => hn ⟨x, xs⟩, by intros; contradiction⟩)
        Nonempty.intro (Classical.indefiniteDescription s this),
      fun h₁ h₂ => by
        have ⟨x, xs⟩ := Classical.choice h₁
        rw [h₂] at xs
        contradiction⟩

    namespace subset

      protected theorem refl (s : Set α) : s ⊆ s := by
        intro _ as; exact as
        
      protected theorem antisymmIff {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a := by
        rw [Subset.ext a b, ←Set.ext]; exact Iff.refl _
      
      protected theorem antisymm {a b : Set α} (hab : a ⊆ b) (hba : b ⊆ a) : a = b :=
        Set.subset.antisymmIff.mpr ⟨hab, hba⟩

      theorem subUniversal (s : Set α) : s ⊆ Set.Universal := by
        intro _ _; trivial

      theorem proper_neq {a b : Set α} : a ⊊ b → a ≠ b :=
        fun ⟨_, x, nxa, xb⟩ ab => nxa ((Set.ext.mpr ab x).mpr xb)

      theorem neq_proper {a b : Set α} : a ⊆ b → a ≠ b → a ⊊ b :=
        fun h₁ h₂ => ⟨h₁, Classical.byContradiction fun h' => by
            have := not_exists.mp h'
            simp only [not_and_iff_or_not, iff_not_not] at this
            apply h₂; apply Set.ext.mp fun x => ⟨@h₁ x, (this x).neg_resolve_right⟩⟩

      protected theorem insert (s : Set α) (a : α) : s ⊆ s.insert a :=
        fun _ => Or.inr

      protected theorem insert_neq {s : Set α} {a : α} (h : a ∉ s) : s ⊊ s.insert a :=
        ⟨subset.insert s a, ⟨a, h, Or.inl rfl⟩⟩

    end subset

    namespace union

      protected theorem comm (s₁ s₂ : Set α) : s₁ ∪ s₂ = s₂ ∪ s₁ := by
        have : ∀ (t₁ t₂ : Set α), t₁ ∪ t₂ ⊆ t₂ ∪ t₁ := fun _ _ _ => Or.comm
        exact Set.subset.antisymm (this s₁ s₂) (this s₂ s₁)

    end union
    
    namespace intersection

      protected theorem comm (s₁ s₂ : Set α) : s₁ ∩ s₂ = s₂ ∩ s₁ := by
        have : ∀ (t₁ t₂ : Set α), t₁ ∩ t₂ ⊆ t₂ ∩ t₁ :=  fun _ _ _ => And.comm
        exact Set.subset.antisymm (this s₁ s₂) (this s₂ s₁)

    end intersection

    namespace minus

      theorem nonempty {s₁ s₂ : Set α} (h : s₁ ⊊ s₂) : Nonempty ↑(s₂ ∖ s₁) :=
        let ⟨x, nxs₁, xs₂⟩ := h.right
        ⟨x, xs₂, nxs₁⟩

      theorem proper {s₁ s₂ : Set α} (h₁ : s₁ ⊆ s₂) (h₂ : Nonempty ↑(s₂ ∖ s₁)) : s₁ ⊊ s₂ :=
        ⟨h₁, let ⟨x, xs₂, nxs₁⟩ := Classical.choice h₂
          ⟨x, nxs₁, xs₂⟩⟩

    end minus

    namespace complement

      theorem comp_comp (s : Set α) : sᶜᶜ = s :=
        Set.ext.mp (fun  x => iff_not_not)

    end complement

    namespace disjoint

      protected theorem comm {s₁ s₂ : Set α} : disjoint s₁ s₂ → disjoint s₂ s₁ := by
          intro dis; simp only [disjoint]; rw [←dis]; exact Set.intersection.comm _ _

      protected theorem comm' {s₁ s₂ : Set α} : disjoint s₁ s₂ ↔ disjoint s₂ s₁ :=
        ⟨disjoint.comm, disjoint.comm⟩

      theorem elementwise {s₁ s₂ : Set α} : disjoint s₁ s₂ ↔ ∀ a ∈ s₁, a ∉ s₂ := by
        apply Iff.intro;
        { intro dis x xs₁ xs₂; have : x ∈ s₁ ∩ s₂ := ⟨xs₁, xs₂⟩; rw [dis] at this; contradiction }
        { exact fun h => Set.subset.antisymm (fun x xs => h x xs.left xs.right) (fun _ _ => by contradiction) }

    end disjoint

    namespace SoSUnion

      protected theorem subset {S : Set (Set α)} {t : Set α} (h : ∀ s ∈ S, s ⊆ t) : (⋃₀ S) ⊆ t :=
        fun _ ⟨s, sS, xs⟩ => h s sS xs

      protected theorem subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀ S :=
        fun _ xt => ⟨t, ⟨tS, xt⟩⟩

      protected theorem subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀ s ⊆ t ↔ ∀t' ∈ s, t' ⊆ t :=
        ⟨fun h t' ht' => Subset.trans (SoSUnion.subset_of_mem ht') h, SoSUnion.subset⟩

    end SoSUnion

    namespace SoSIntersection

      protected theorem subset {S : Set (Set α)} {t : Set α} (h : ∀ s ∈ S, t ⊆ s) : t ⊆ (⋂₀ S) :=
        fun _ xt s sS => h s sS xt

      protected theorem subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
        fun _ xIS => xIS t tS

      protected theorem subset_iff {s : Set (Set α)} {t : Set α} : t ⊆ ⋂₀ s ↔ ∀t' ∈ s, t ⊆ t' :=
        ⟨fun h t' ht' => Subset.trans h (SoSIntersection.subset_of_mem ht'), SoSIntersection.subset⟩

    end SoSIntersection

  end Set
end M4R