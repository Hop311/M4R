import M4R.Algebra.Group.SubGroup

namespace M4R
  namespace GHomomorphism

    theorem hom_inj [ga : Group α] [Group β] (gh : GHomomorphism α β) :
      Function.injective gh.hom ↔ kernel gh = {x | x = 0} := by
        simp [kernel, Function.fibre];
        apply Iff.intro;
          { intro inj; apply funext; intro x; have h := @inj x 0; rw [←gh.preserve_zero];
          apply propext (Iff.intro h (by intro xz; rw [xz])) };
          { intro hzero x y ghxy; rw [←ga.add_right_cancel _ _ (-y), ga.add_neg, ←congrFun hzero (x + -y),
            gh.preserve_add, ghxy, ←gh.preserve_add, ga.add_neg, gh.preserve_zero] }

    protected theorem comp [Group α] [Group β] [Group γ] (hbc : GHomomorphism β γ)
      (hab : GHomomorphism α β) : GHomomorphism α γ where
      hom           := Function.comp hbc.hom hab.hom
      preserve_zero := by simp [Function.comp]; rw [hab.preserve_zero, hbc.preserve_zero]
      preserve_add  := by intro a b; simp [Function.comp]; rw [hab.preserve_add, hbc.preserve_add]
      preserve_neg  := by intro a; simp [Function.comp]; rw [hab.preserve_neg, hbc.preserve_neg]

    instance GHomImageSubGroup [Group α] [Group β] (gh : GHomomorphism α β) : SubGroup β where
      subset     := Function.image gh.hom
      has_zero   := ⟨0, gh.preserve_zero⟩
      add_closed := by
        intro _ _ ⟨a, hax⟩ ⟨b, hby⟩; rw [←hax, ←hby]; exact ⟨a+b, gh.preserve_add a b⟩
      neg_closed := by
        intro x ⟨a, hax⟩; rw [←hax]; exact ⟨-a, gh.preserve_neg a⟩

  end GHomomorphism

  namespace GIsomorphism
  
    protected theorem comp [Group α] [Group β] [Group γ] (hbc : GIsomorphism β γ) (hab : GIsomorphism α β) :
      GIsomorphism α γ where
      hom           := hbc.hom ∘ hab.hom
      preserve_zero := by simp [Function.comp]; rw [hab.preserve_zero, hbc.preserve_zero]
      preserve_add  := by intro a b; simp [Function.comp]; rw [hab.preserve_add, hbc.preserve_add]
      preserve_neg  := by intro a; simp [Function.comp]; rw [hab.preserve_neg, hbc.preserve_neg]
      bij           := by have := Function.bijective.comp hbc.bij hab.bij; exact this

    instance IdentityGIsomorphism [Group α] : GIsomorphism α α where
      hom := id
      preserve_zero := rfl
      preserve_add := by intros; rfl
      preserve_neg := by intros; rfl
      bij := Function.id_bijective

  end GIsomorphism
end M4R