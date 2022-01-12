import M4R.Algebra.Ring.SubRing

namespace M4R

  structure SHomomorphism (α : Type _) (β : Type _) [NCSemiring α] [NCSemiring β] extends MHomomorphism α β where
    preserve_one  : hom 1 = 1
    preserve_mul  : ∀ a b, hom (a * b) = hom a * hom b
  
  structure SIsomorphism (α : Type _) (β : Type _) [NCSemiring α] [NCSemiring β] extends SHomomorphism α β, MIsomorphism α β

  structure RHomomorphism (α : Type _) (β : Type _) [NCRing α] [NCRing β] extends SHomomorphism α β, GHomomorphism α β

  structure RIsomorphism (α : Type _) (β : Type _) [NCRing α] [NCRing β] extends RHomomorphism α β, MIsomorphism α β

  instance SHomomorphismFun [NCSemiring α] [NCSemiring β] : CoeFun (SHomomorphism α β) (fun _ => α → β) where coe := fun f => f.hom
  instance SIsomorphismFun  [NCSemiring α] [NCSemiring β] : CoeFun (SIsomorphism  α β) (fun _ => α → β) where coe := fun f => f.hom
  instance RHomomorphismFun [NCRing     α] [NCRing     β] : CoeFun (RHomomorphism α β) (fun _ => α → β) where coe := fun f => f.hom
  instance RIsomorphismFun  [NCRing     α] [NCRing     β] : CoeFun (RIsomorphism  α β) (fun _ => α → β) where coe := fun f => f.hom

  namespace SHomomorphism

    protected def comp [NCSemiring α] [NCSemiring β] [NCSemiring γ] (hbc : SHomomorphism β γ) (hab : SHomomorphism α β) : SHomomorphism α γ where
      toMHomomorphism := MHomomorphism.comp hbc.toMHomomorphism hab.toMHomomorphism
      preserve_one := by simp only [MHomomorphism.comp, Function.comp]; rw [hab.preserve_one, hbc.preserve_one]
      preserve_mul := fun a b => by simp only [MHomomorphism.comp, Function.comp]; rw [hab.preserve_mul, hbc.preserve_mul]

    instance ImageSubSemiring [NCSemiring α] [NCSemiring β] (gh : SHomomorphism α β) : SubSemiring β where
      toSubMonoid := gh.ImageSubMonoid
      has_one := ⟨1, gh.preserve_one⟩
      mul_closed := fun _ ⟨a, hax⟩ _ ⟨b, hby⟩ => by rw [←hax, ←hby]; exact ⟨a * b, gh.preserve_mul a b⟩

    protected instance Identity [NCSemiring α] : SHomomorphism α α where
      toMHomomorphism := MHomomorphism.Identity
      preserve_one := by simp [MHomomorphism.Identity]
      preserve_mul := by intros; rfl

  end SHomomorphism

  namespace SIsomorphism
  
    protected theorem comp [NCSemiring α] [NCSemiring β] [NCSemiring γ] (hbc : SIsomorphism β γ) (hab : SIsomorphism α β) :
      SIsomorphism α γ where
        toSHomomorphism := SHomomorphism.comp hbc.toSHomomorphism hab.toSHomomorphism
        bij             := by have := Function.bijective.comp hbc.bij hab.bij; exact this

    protected instance Identity [NCSemiring α] : SIsomorphism α α where
      toSHomomorphism := SHomomorphism.Identity
      bij             := MIsomorphism.Identity.bij

  end SIsomorphism

  namespace RHomomorphism

    protected def comp [NCRing α] [NCRing β] [NCRing γ] (hbc : RHomomorphism β γ) (hab : RHomomorphism α β) : RHomomorphism α γ where
      toSHomomorphism := SHomomorphism.comp hbc.toSHomomorphism hab.toSHomomorphism
      preserve_neg  := fun a => by
        simp only [SHomomorphism.comp, MHomomorphism.comp, Function.comp]
        rw [hab.preserve_neg, hbc.preserve_neg]

    instance ImageSubRing [NCRing α] [NCRing β] (gh : RHomomorphism α β) : SubRing β where
      toSubSemiring := gh.ImageSubSemiring
      neg_closed := gh.toGHomomorphism.ImageSubGroup.neg_closed

    protected instance Identity [NCRing α] : RHomomorphism α α where
      toSHomomorphism := SHomomorphism.Identity
      preserve_neg    := GHomomorphism.Identity.preserve_neg

  end RHomomorphism

  namespace RIsomorphism

    protected def comp [NCRing α] [NCRing β] [NCRing γ] (hbc : RIsomorphism β γ) (hab : RIsomorphism α β) :
      RIsomorphism α γ where
        toRHomomorphism := RHomomorphism.comp hbc.toRHomomorphism hab.toRHomomorphism
        bij             := by have := Function.bijective.comp hbc.bij hab.bij; exact this

    instance Identity [NCRing α] : RIsomorphism α α where
      toRHomomorphism := RHomomorphism.Identity
      bij             := MIsomorphism.Identity.bij

  end RIsomorphism
end M4R