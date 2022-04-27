import M4R.Algebra.Ring.Ring
import M4R.Algebra.Ring.SubRing

namespace M4R
  open NCSemiring

  structure SMulMap (α : Type _) (β : Type _) [NCSemiring α] [NCSemiring β] extends α →₊ β where
    preserve_mul : ∀ a b, hom (a * b) = hom a * hom b
  infixr:25 " →* " => SMulMap
  instance SMulMapFun [NCSemiring α] [NCSemiring β] : CoeFun (α →* β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure SHomomorphism (α : Type _) (β : Type _) [NCSemiring α] [NCSemiring β] extends α →* β where
    preserve_one  : hom 1 = 1
  infixr:25 " →*₁ " => SHomomorphism
  instance SHomomorphismFun [NCSemiring α] [NCSemiring β] : CoeFun (α →*₁ β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure SIsomorphism (α : Type _) (β : Type _) [NCSemiring α] [NCSemiring β] extends α →* β, α ≅₊ β
  infixr:25 " ≅* " => SIsomorphism
  instance SIsomorphismFun [NCSemiring α] [NCSemiring β] : CoeFun (α ≅* β) (fun _ => α → β) where
    coe := fun f => f.hom

  
  structure RMulMap (α : Type _) (β : Type _) [NCRing α] [NCRing β] extends α →* β, α →₋ β
  infixr:25 " →ᵣ " => RMulMap
  instance RMulMapFun  [NCRing α] [NCRing β] : CoeFun (α →ᵣ β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure RHomomorphism (α : Type _) (β : Type _) [NCRing α] [NCRing β] extends α →ᵣ β, α →*₁ β
  infixr:25 " →ᵣ₁ " => RHomomorphism
  instance RHomomorphismFun [NCRing α] [NCRing β] : CoeFun (α →ᵣ₁ β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure RIsomorphism (α : Type _) (β : Type _) [NCRing α] [NCRing β] extends α →ᵣ β, α ≅₊ β
  infixr:25 " ≅ᵣ " => RIsomorphism
  instance RIsomorphismFun [NCRing α] [NCRing β] : CoeFun (α ≅ᵣ β) (fun _ => α → β) where
    coe := fun f => f.hom

  namespace SMulMap
    variable [NCSemiring α] [NCSemiring β] [NCSemiring γ]

    def kernel (slm : α →* β) : SubMonoid α := slm.toMHomomorphism.kernel

    def image (slm : α →* β) : SubMonoid β := slm.toMHomomorphism.image

    protected def comp (hbc : β →* γ) (hab : α →* β) : α →* γ where
      toMHomomorphism := hbc.toMHomomorphism.comp hab.toMHomomorphism
      preserve_mul    := fun _ _ => by
        simp only [MHomomorphism.comp, Function.comp]
        rw [hab.preserve_mul, hbc.preserve_mul]

    protected def Identity : α →* α where
      toMHomomorphism := MHomomorphism.Identity
      preserve_mul    := fun _ _ => rfl

    protected theorem preserve_one_of_1_in_image {f : α →* β} (h1 : 1 ∈ Function.image f.hom) : f 1 = 1 := by
      let ⟨x, hx⟩ := h1
      rw [←hx, ←mul_one x, f.preserve_mul, hx, one_mul]

    protected theorem preserve_one_of_surjective {f : α →* β} (hf : Function.surjective f.hom) : f 1 = 1 :=
      SMulMap.preserve_one_of_1_in_image (hf 1)

  end SMulMap

  namespace SHomomorphism
    variable [NCSemiring α] [NCSemiring β] [NCSemiring γ]

    def kernel (sh : α →*₁ β) : SubMonoid α := sh.toSMulMap.kernel

    def image (sh : α →*₁ β) : SubSemiring β where
      toSubMonoid := sh.toSMulMap.image
      has_one     := ⟨1, sh.preserve_one⟩
      mul_closed  := fun _ ⟨a, ha⟩ _ ⟨b, hb⟩ => ⟨a * b, ha ▸ hb ▸ sh.preserve_mul a b⟩

    protected def comp (hbc : β →*₁ γ) (hab : α →*₁ β) : α →*₁ γ where
      toSMulMap := hbc.toSMulMap.comp hab.toSMulMap
      preserve_one := by
        simp only [SMulMap.comp, MHomomorphism.comp, Function.comp]
        rw [hab.preserve_one, hbc.preserve_one]

    protected def Identity : α →*₁ α where
      toSMulMap := SMulMap.Identity
      preserve_one := rfl

  end SHomomorphism

  namespace SIsomorphism
    variable [NCSemiring α] [NCSemiring β] [NCSemiring γ]

    protected theorem preserve_one (f : α ≅* β) : f 1 = 1 :=
      SMulMap.preserve_one_of_surjective f.toMIsomorphism.to_surjective

    def toSHomomorphism (f : α ≅* β) : α →*₁ β where
      toSMulMap := f.toSMulMap
      preserve_one := f.preserve_one

    protected def inv_hom (f : α ≅* β) : β →*₁ α where
      toMHomomorphism := f.toMIsomorphism.inv_hom
      preserve_one    := by
        have : f.toMIsomorphism.inv_hom (f 1) = f.inv (f 1)  := rfl
        rw [←f.preserve_one, this, f.left_inv]
      preserve_mul    := fun a b => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        let ⟨_, hb⟩ := f.right_inv.surjective b
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [←ha, ←hb, this, ←f.preserve_mul, f.left_inv, f.left_inv, f.left_inv]

    protected def symm (f : α ≅* β) : β ≅* α where
      toSMulMap := f.inv_hom.toSMulMap
      inv          := f
      left_inv     := f.right_inv
      right_inv    := f.left_inv

    protected theorem comp (hbc : β ≅* γ) (hab : α ≅* β) : α ≅* γ where
      toSMulMap := hbc.toSMulMap.comp hab.toSMulMap
      inv          := hab.inv ∘ hbc.inv
      left_inv     := fun _ => by
        have : hbc.toSMulMap.comp hab.toSMulMap = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv    := fun _ => by
        have : hbc.toSMulMap.comp hab.toSMulMap = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection (f : α →* β) (hf : Function.bijective f.hom) : α ≅* β where
        toSMulMap := f
        inv          := fun b => Classical.choose (hf.surj b)
        left_inv     := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
        right_inv    := fun a => Classical.choose_spec (hf.surj a)

    protected noncomputable def Identity : α ≅* α :=
      SIsomorphism.of_bijection _ (by apply Function.id_bijective : Function.bijective SHomomorphism.Identity.hom)

    protected def SelfInverse (f : α →* α) (h : ∀ a, f (f a) = a) : α ≅* α where
      toSMulMap := f
      inv          := f.hom
      left_inv     := h
      right_inv    := h

  end SIsomorphism

  namespace RMulMap
    variable [NCRing α] [NCRing β] [NCRing γ]

    def kernel (rlm : α →ᵣ β) : SubGroup α := rlm.toGHomomorphism.kernel

    def image (rlm : α →ᵣ β) : SubGroup β := rlm.toGHomomorphism.image

    protected def comp (hbc : β →ᵣ γ) (hab : α →ᵣ β) : α →ᵣ γ where
      toSMulMap := hbc.toSMulMap.comp hab.toSMulMap
      preserve_neg := (hbc.toGHomomorphism.comp hab.toGHomomorphism).preserve_neg

    protected def Identity : α →ᵣ α where
      toSMulMap := SMulMap.Identity
      preserve_neg := GHomomorphism.Identity.preserve_neg

    protected theorem preserve_one_of_1_in_image {f : α →ᵣ β} (h1 : 1 ∈ Function.image f.hom) : f 1 = 1 :=
      SMulMap.preserve_one_of_1_in_image h1

    protected theorem preserve_one_of_surjective {f : α →ᵣ β} (hf : Function.surjective f.hom) : f 1 = 1 :=
      SMulMap.preserve_one_of_surjective hf

  end RMulMap

  namespace RHomomorphism
    variable [NCRing α] [NCRing β] [NCRing γ]

    def kernel (rh : α →ᵣ₁ β) : SubGroup α := rh.toRMulMap.kernel

    def image (rh : α →ᵣ₁ β) : SubRing β where
      toSubSemiring := rh.toSHomomorphism.image
      neg_closed := rh.toGHomomorphism.image.neg_closed

    protected def comp (hbc : β →ᵣ₁ γ) (hab : α →ᵣ₁ β) : α →ᵣ₁ γ where
      toRMulMap := hbc.toRMulMap.comp hab.toRMulMap
      preserve_one := (hbc.toSHomomorphism.comp hab.toSHomomorphism).preserve_one

    protected def Identity : α →ᵣ₁ α where
      toRMulMap := RMulMap.Identity
      preserve_one := SHomomorphism.Identity.preserve_one

  end RHomomorphism

  namespace RIsomorphism
    variable [NCRing α] [NCRing β] [NCRing γ]

    protected theorem preserve_one (f : α ≅ᵣ β) : f 1 = 1 :=
      RMulMap.preserve_one_of_surjective f.toMIsomorphism.to_surjective

    def toSHomomorphism (f : α ≅ᵣ β) : α →ᵣ₁ β where
      toRMulMap := f.toRMulMap
      preserve_one := f.preserve_one

    protected def inv_hom [NCRing α] [NCRing β] (f : α ≅ᵣ β) : β →ᵣ₁ α where
      toMHomomorphism := f.toMIsomorphism.inv_hom
      preserve_neg := fun a => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [this, ←ha, ←f.preserve_neg, f.left_inv, f.left_inv]
      preserve_one := by
        have : f.toMIsomorphism.inv_hom (f 1) = f.inv (f 1) := rfl
        simp only; rw [←f.preserve_one, this, f.left_inv]
      preserve_mul := fun a b => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        let ⟨_, hb⟩ := f.right_inv.surjective b
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [←ha, ←hb, this, ←f.preserve_mul, f.left_inv, f.left_inv, f.left_inv]

    protected def symm [NCRing α] [NCRing β] (f : α ≅ᵣ β) : β ≅ᵣ α where
      toRMulMap := f.inv_hom.toRMulMap
      inv          := f
      left_inv     := f.right_inv
      right_inv    := f.left_inv

    protected theorem comp [NCRing α] [NCRing β] [NCRing γ] (hbc : β ≅ᵣ γ) (hab : α ≅ᵣ β) : α ≅ᵣ γ where
      toRMulMap := hbc.toRMulMap.comp hab.toRMulMap
      inv := hab.inv ∘ hbc.inv
      left_inv := fun _ => by
        have : hbc.toRMulMap.comp hab.toRMulMap = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv := fun _ => by
        have : hbc.toRMulMap.comp hab.toRMulMap = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection [NCRing α] [NCRing β] (f : α →ᵣ β)
      (hf : Function.bijective f.hom) : α ≅ᵣ β where
        toRMulMap := f
        inv          := fun b => Classical.choose (hf.surj b)
        left_inv     := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
        right_inv    := fun a => Classical.choose_spec (hf.surj a)

    protected noncomputable def Identity [NCRing α] : α ≅ᵣ α :=
      RIsomorphism.of_bijection _ (by apply Function.id_bijective : Function.bijective RHomomorphism.Identity.hom)

    protected def SelfInverse [NCRing α] (f : α →ᵣ α) (h : ∀ a, f (f a) = a) : α ≅ᵣ α where
      toRMulMap := f
      inv          := f.hom
      left_inv     := h
      right_inv    := h

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
