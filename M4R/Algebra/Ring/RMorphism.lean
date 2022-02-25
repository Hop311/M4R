import M4R.Algebra.Ring.Ring
import M4R.Algebra.Ring.SubRing

namespace M4R

  structure SHomomorphism (α : Type _) (β : Type _) [NCSemiring α] [NCSemiring β] extends α →₊ β where
    preserve_one  : hom 1 = 1
    preserve_mul  : ∀ a b, hom (a * b) = hom a * hom b

  infixr:25 " →* " => SHomomorphism
  instance SHomomorphismFun [NCSemiring α] [NCSemiring β] : CoeFun (α →* β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure SIsomorphism (α : Type _) (β : Type _) [NCSemiring α] [NCSemiring β] extends α →* β, α ≅₊ β

  infixr:25 " ≅* " => SIsomorphism
  instance SIsomorphismFun  [NCSemiring α] [NCSemiring β] : CoeFun (α ≅* β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure RHomomorphism (α : Type _) (β : Type _) [NCRing α] [NCRing β] extends α →* β, α →₋ β

  infixr:25 " →ᵣ " => RHomomorphism
  instance RHomomorphismFun [NCRing α] [NCRing β] : CoeFun (α →ᵣ β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure RIsomorphism (α : Type _) (β : Type _) [NCRing α] [NCRing β] extends α →ᵣ β, α ≅₊ β

  infixr:25 " ≅ᵣ " => RIsomorphism
  instance RIsomorphismFun  [NCRing α] [NCRing β] : CoeFun (α ≅ᵣ β) (fun _ => α → β) where
    coe := fun f => f.hom

  namespace SHomomorphism

    protected def comp [NCSemiring α] [NCSemiring β] [NCSemiring γ] (hbc : β →* γ) (hab : α →* β) : α →* γ where
      toMHomomorphism := hbc.toMHomomorphism.comp hab.toMHomomorphism
      preserve_one := by simp only [MHomomorphism.comp, Function.comp]; rw [hab.preserve_one, hbc.preserve_one]
      preserve_mul := fun a b => by simp only [MHomomorphism.comp, Function.comp]; rw [hab.preserve_mul, hbc.preserve_mul]

    def ImageSubSemiring [NCSemiring α] [NCSemiring β] (gh : α →* β) : SubSemiring β where
      toSubMonoid := gh.ImageSubMonoid
      has_one := ⟨1, gh.preserve_one⟩
      mul_closed := fun _ ⟨a, hax⟩ _ ⟨b, hby⟩ => by rw [←hax, ←hby]; exact ⟨a * b, gh.preserve_mul a b⟩

    protected def Identity [NCSemiring α] : α →* α where
      toMHomomorphism := MHomomorphism.Identity
      preserve_one := by simp [MHomomorphism.Identity]
      preserve_mul := by intros; rfl

  end SHomomorphism

  namespace SIsomorphism

    protected def inv_hom [NCSemiring α] [NCSemiring β] (f : α ≅* β) : β →* α where
      toMHomomorphism := f.toMIsomorphism.inv_hom
      preserve_one := by
        conv => lhs rw [←f.preserve_one]
        have : f.toMIsomorphism.inv_hom.hom (f.toSHomomorphism.toMHomomorphism.hom 1) = f.inv (f 1)  := rfl
        rw [this, f.left_inv]
      preserve_mul := fun a b => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        let ⟨_, hb⟩ := f.right_inv.surjective b
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [←ha, ←hb, this, ←f.preserve_mul, f.left_inv, f.left_inv, f.left_inv]

    protected def symm [NCSemiring α] [NCSemiring β] (f : α ≅* β) : β ≅* α where
      toSHomomorphism := f.inv_hom
      inv := f
      left_inv := f.right_inv
      right_inv := f.left_inv

    protected theorem comp [NCSemiring α] [NCSemiring β] [NCSemiring γ] (hbc : β ≅* γ) (hab : α ≅* β) : α ≅* γ where
      toSHomomorphism := hbc.toSHomomorphism.comp hab.toSHomomorphism
      inv := hab.inv ∘ hbc.inv
      left_inv := by
        intro a
        have : hbc.toSHomomorphism.comp hab.toSHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv := by
        intro a
        have : hbc.toSHomomorphism.comp hab.toSHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection [NCSemiring α] [NCSemiring β] {f : α →* β}
      (hf : Function.bijective f.hom) : α ≅* β where
        toSHomomorphism := f
        inv := fun b => Classical.choose (hf.surj b)
        left_inv := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
        right_inv := fun a => Classical.choose_spec (hf.surj a)

    protected noncomputable def Identity [NCSemiring α] : α ≅* α :=
      SIsomorphism.of_bijection (by apply Function.id_bijective : Function.bijective SHomomorphism.Identity.hom)

    protected def SelfInverse [NCSemiring α] (f : α →* α) (h : ∀ a, f (f a) = a) : α ≅* α where
      toSHomomorphism := f
      inv := f.hom
      left_inv := h
      right_inv := h

  end SIsomorphism

  namespace RHomomorphism

    protected def comp [NCRing α] [NCRing β] [NCRing γ] (hbc : β →ᵣ γ) (hab : α →ᵣ β) : α →ᵣ γ where
      toSHomomorphism := hbc.toSHomomorphism.comp hab.toSHomomorphism
      preserve_neg  := fun a => by
        simp only [SHomomorphism.comp, MHomomorphism.comp, Function.comp]
        rw [hab.preserve_neg, hbc.preserve_neg]

    def ImageSubRing [NCRing α] [NCRing β] (gh : α →ᵣ β) : SubRing β where
      toSubSemiring := gh.ImageSubSemiring
      neg_closed := gh.toGHomomorphism.ImageSubGroup.neg_closed

    protected def Identity [NCRing α] : α →ᵣ α where
      toSHomomorphism := SHomomorphism.Identity
      preserve_neg    := GHomomorphism.Identity.preserve_neg

  end RHomomorphism

  namespace RIsomorphism

    protected def inv_hom [NCRing α] [NCRing β] (f : α ≅ᵣ β) : β →ᵣ α where
      toMHomomorphism := f.toMIsomorphism.inv_hom
      preserve_neg := fun a => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [this, ←ha, ←f.preserve_neg, f.left_inv, f.left_inv]
      preserve_one := by
        conv => lhs rw [←f.preserve_one]
        have : f.toMIsomorphism.inv_hom.hom (f.toSHomomorphism.toMHomomorphism.hom 1) = f.inv (f 1)  := rfl
        rw [this, f.left_inv]
      preserve_mul := fun a b => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        let ⟨_, hb⟩ := f.right_inv.surjective b
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [←ha, ←hb, this, ←f.preserve_mul, f.left_inv, f.left_inv, f.left_inv]

    protected def symm [NCRing α] [NCRing β] (f : α ≅ᵣ β) : β ≅ᵣ α where
      toRHomomorphism := f.inv_hom
      inv := f
      left_inv := f.right_inv
      right_inv := f.left_inv

    protected theorem comp [NCRing α] [NCRing β] [NCRing γ] (hbc : β ≅ᵣ γ) (hab : α ≅ᵣ β) : α ≅ᵣ γ where
      toRHomomorphism := hbc.toRHomomorphism.comp hab.toRHomomorphism
      inv := hab.inv ∘ hbc.inv
      left_inv := by
        intro a
        have : hbc.toRHomomorphism.comp hab.toRHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv := by
        intro a
        have : hbc.toRHomomorphism.comp hab.toRHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection [NCRing α] [NCRing β] {f : α →ᵣ β}
      (hf : Function.bijective f.hom) : α ≅ᵣ β where
        toRHomomorphism := f
        inv := fun b => Classical.choose (hf.surj b)
        left_inv := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
        right_inv := fun a => Classical.choose_spec (hf.surj a)

    protected noncomputable def Identity [NCRing α] : α ≅ᵣ α :=
      RIsomorphism.of_bijection (by apply Function.id_bijective : Function.bijective RHomomorphism.Identity.hom)

    protected def SelfInverse [NCRing α] (f : α →ᵣ α) (h : ∀ a, f (f a) = a) : α ≅ᵣ α where
      toRHomomorphism := f
      inv := f.hom
      left_inv := h
      right_inv := h

  end RIsomorphism

  protected def NCSemiring.MulHomLeft [NCSemiring α] (a : α) : α →₊ α where
    hom := (a * ·)
    preserve_zero := by simp only [NCSemiring.mul_zero]
    preserve_add := fun _ _ => by simp only [NCSemiring.mul_distrib_left]
  
  protected def NCSemiring.MulHomRight [NCSemiring α] (a : α) : α →₊ α where
    hom := (· * a)
    preserve_zero := by simp only [NCSemiring.zero_mul]
    preserve_add := fun _ _ => by simp only [NCSemiring.mul_distrib_right]
  
  protected def NCRing.MulHomLeft [NCRing α] (a : α) : α →₋ α where
    toMHomomorphism := NCSemiring.MulHomLeft a
    preserve_neg := fun _ => by simp only [NCSemiring.MulHomLeft, NCRing.mul_neg]
  
  protected def NCRing.MulHomRight [NCRing α] (a : α) : α →₋ α where
    toMHomomorphism := NCSemiring.MulHomRight a
    preserve_neg := fun _ => by simp only [NCSemiring.MulHomRight, NCRing.neg_mul]

end M4R