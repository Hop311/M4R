import M4R.Algebra.Group.SubGroup

namespace M4R

  structure GHomomorphism (α : Type _) (β : Type _) [Group α] [Group β] where
    hom           : α → β
    preserve_zero : hom 0 = 0
    preserve_add  : ∀ a b, hom (a + b) = hom a + hom b
    preserve_neg  : ∀ a, hom (-a) = -hom a

  structure GIsomorphism (α : Type _) (β : Type _) [Group α] [Group β] extends GHomomorphism α β where
    bij : Function.bijective hom

  instance GHomomorphismFun [Group α] [Group β] : CoeFun (GHomomorphism α β) (fun _ => α → β) where
    coe := GHomomorphism.hom

  def GHomomorphism.kernel [Group α] [gb : Group β] (gh : GHomomorphism α β) : SubGroup α where
    subset := Function.fibre gh.hom 0
    has_zero := gh.preserve_zero
    add_closed := by
      intro _ x0 _ y0; simp only [Mem.mem, Set.mem, Function.fibre]; rw [gh.preserve_add, x0, y0, gb.add_zero]
    neg_closed := by
      intro x x0; simp only [Mem.mem, Set.mem, Function.fibre]; rw [gh.preserve_neg, x0, gb.neg_zero]

  namespace GHomomorphism

    theorem hom_inj [ga : Group α] [gb : Group β] (gh : GHomomorphism α β) :
      Function.injective gh.hom ↔ kernel gh = SubGroup.Trivial α := by
        simp only [kernel, Function.fibre];
        apply Iff.intro;
          { intro inj; apply (SubGroup.trivialExt (kernel gh)).mpr;
             intro x; have h := @inj x 0; rw [gh.preserve_zero] at h; exact fun x => h x }
          { intro kertriv x y ghxy; rw [←ga.add_right_cancel _ _ (-y), ga.add_neg];
            rw [←gb.add_right_cancel _ _ (gh (-y)), gh.preserve_neg, gb.add_neg,
              ←gh.preserve_neg, ←gh.preserve_add] at ghxy;
            exact (SubGroup.trivialExt (kernel gh)).mp kertriv (x + -y) ghxy }

    protected theorem comp [Group α] [Group β] [Group γ] (hbc : GHomomorphism β γ)
      (hab : GHomomorphism α β) : GHomomorphism α γ where
      hom           := Function.comp hbc.hom hab.hom
      preserve_zero := by simp only [Function.comp]; rw [hab.preserve_zero, hbc.preserve_zero]
      preserve_add  := by intro a b; simp only [Function.comp]; rw [hab.preserve_add, hbc.preserve_add]
      preserve_neg  := by intro a; simp only [Function.comp]; rw [hab.preserve_neg, hbc.preserve_neg]

    instance GHomImageSubGroup [Group α] [Group β] (gh : GHomomorphism α β) : SubGroup β where
      subset     := Function.image gh.hom
      has_zero   := ⟨0, gh.preserve_zero⟩
      add_closed := by
        intro _ ⟨a, hax⟩ _ ⟨b, hby⟩; rw [←hax, ←hby]; exact ⟨a+b, gh.preserve_add a b⟩
      neg_closed := by
        intro x ⟨a, hax⟩; rw [←hax]; exact ⟨-a, gh.preserve_neg a⟩

  end GHomomorphism

  namespace GIsomorphism
  
    protected theorem comp [Group α] [Group β] [Group γ] (hbc : GIsomorphism β γ) (hab : GIsomorphism α β) :
      GIsomorphism α γ where
      hom           := hbc.hom ∘ hab.hom
      preserve_zero := by simp only [Function.comp]; rw [hab.preserve_zero, hbc.preserve_zero]
      preserve_add  := by intro a b; simp only [Function.comp]; rw [hab.preserve_add, hbc.preserve_add]
      preserve_neg  := by intro a; simp only [Function.comp]; rw [hab.preserve_neg, hbc.preserve_neg]
      bij           := by have := Function.bijective.comp hbc.bij hab.bij; exact this

    instance IdentityGIsomorphism [Group α] : GIsomorphism α α where
      hom := id
      preserve_zero := rfl
      preserve_add := by intros; rfl
      preserve_neg := by intros; rfl
      bij := Function.id_bijective

  end GIsomorphism
end M4R