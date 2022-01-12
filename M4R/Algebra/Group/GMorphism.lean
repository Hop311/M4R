import M4R.Algebra.Group.Group

namespace M4R

  structure MHomomorphism (α : Type _) (β : Type _) [Monoid α] [Monoid β] where
    hom           : α → β
    preserve_zero : hom 0 = 0
    preserve_add  : ∀ a b, hom (a + b) = hom a + hom b

  structure MIsomorphism (α : Type _) (β : Type _) [Monoid α] [Monoid β] extends MHomomorphism α β where
    bij : Function.bijective hom

  structure GHomomorphism (α : Type _) (β : Type _) [Group α] [Group β] extends MHomomorphism α β where
    preserve_neg  : ∀ a, hom (-a) = -hom a

  structure GIsomorphism (α : Type _) (β : Type _) [Group α] [Group β] extends GHomomorphism α β, MIsomorphism α β

  instance MHomomorphismFun [Monoid α] [Monoid β] : CoeFun (MHomomorphism α β) (fun _ => α → β) where coe := MHomomorphism.hom
  instance MIsomorphismFun  [Monoid α] [Monoid β] : CoeFun (MIsomorphism  α β) (fun _ => α → β) where coe := fun f => f.hom
  instance GHomomorphismFun [Group  α] [Group  β] : CoeFun (GHomomorphism α β) (fun _ => α → β) where coe := fun f => f.hom
  instance GIsomorphismFun  [Group  α] [Group  β] : CoeFun (GIsomorphism  α β) (fun _ => α → β) where coe := fun f => f.hom

  def MHomomorphism.kernel [Monoid α] [mb : Monoid β] (mh : MHomomorphism α β) : SubMonoid α where
    subset     := Function.fibre mh.hom 0
    has_zero   := mh.preserve_zero
    add_closed := fun _ x0 _ y0 => by simp only [Mem.mem, Set.mem, Function.fibre]; rw [mh.preserve_add, x0, y0, mb.add_zero]

  def GHomomorphism.kernel [Group α] [gb : Group β] (gh : GHomomorphism α β) : SubGroup α where
    toSubMonoid := MHomomorphism.kernel gh.toMHomomorphism
    neg_closed  := fun x x0 => by
      simp only [MHomomorphism.kernel, Mem.mem, Set.mem, Function.fibre]
      rw [gh.preserve_neg, x0, gb.neg_zero]

  namespace MHomomorphism

    protected def comp [Monoid α] [Monoid β] [Monoid γ] (hbc : MHomomorphism β γ) (hab : MHomomorphism α β) : MHomomorphism α γ where
      hom           := Function.comp hbc.hom hab.hom
      preserve_zero := by simp only [Function.comp]; rw [hab.preserve_zero, hbc.preserve_zero]
      preserve_add  := fun a b => by simp only [Function.comp]; rw [hab.preserve_add, hbc.preserve_add]

    instance ImageSubMonoid [Monoid α] [Monoid β] (gh : MHomomorphism α β) : SubMonoid β where
      subset     := Function.image gh.hom
      has_zero   := ⟨0, gh.preserve_zero⟩
      add_closed := fun _ ⟨a, hax⟩ _ ⟨b, hby⟩ => by rw [←hax, ←hby]; exact ⟨a + b, gh.preserve_add a b⟩

    protected instance Identity [Monoid α] : MHomomorphism α α where
      hom           := id
      preserve_zero := rfl
      preserve_add  := by intros; rfl

  end MHomomorphism

  namespace MIsomorphism
  
    protected theorem comp [Monoid α] [Monoid β] [Monoid γ] (hbc : MIsomorphism β γ) (hab : MIsomorphism α β) : MIsomorphism α γ where
        toMHomomorphism := MHomomorphism.comp hbc.toMHomomorphism hab.toMHomomorphism
        bij             := by have := Function.bijective.comp hbc.bij hab.bij; exact this

    protected instance Identity [Monoid α] : MIsomorphism α α where
      toMHomomorphism := MHomomorphism.Identity
      bij             := Function.id_bijective

  end MIsomorphism

  namespace GHomomorphism

    protected def comp [Group α] [Group β] [Group γ] (hbc : GHomomorphism β γ) (hab : GHomomorphism α β) : GHomomorphism α γ where
      toMHomomorphism := MHomomorphism.comp hbc.toMHomomorphism hab.toMHomomorphism
      preserve_neg  := fun a => by simp only [MHomomorphism.comp, Function.comp]; rw [hab.preserve_neg, hbc.preserve_neg]

    instance ImageSubGroup [Group α] [Group β] (gh : GHomomorphism α β) : SubGroup β where
      toSubMonoid := gh.ImageSubMonoid
      neg_closed := fun x ⟨a, hax⟩ => by rw [←hax]; exact ⟨-a, gh.preserve_neg a⟩

    protected instance Identity [Group α] : GHomomorphism α α where
      toMHomomorphism := MHomomorphism.Identity
      preserve_neg    := by intros; rfl

  end GHomomorphism

  namespace GIsomorphism

    protected def comp [Group α] [Group β] [Group γ] (hbc : GIsomorphism β γ) (hab : GIsomorphism α β) : GIsomorphism α γ where
        toGHomomorphism := GHomomorphism.comp hbc.toGHomomorphism hab.toGHomomorphism
        bij             := by have := Function.bijective.comp hbc.bij hab.bij; exact this

    instance Identity [Group α] : GIsomorphism α α where
      toGHomomorphism := GHomomorphism.Identity
      bij             := MIsomorphism.Identity.bij

  end GIsomorphism
end M4R