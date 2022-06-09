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
    variable [NCSemiring α] [NCSemiring β] [NCSemiring γ] [NCSemiring δ]

    def kernel (slm : α →* β) : SubMonoid α := slm.toMHomomorphism.kernel

    def image (slm : α →* β) : SubMonoid β := slm.toMHomomorphism.image

    protected def comp (hab : α →* β) (hbc : β →* γ) : α →* γ where
      toMHomomorphism := hab.toMHomomorphism.comp hbc.toMHomomorphism
      preserve_mul    := fun _ _ => by
        simp only [MHomomorphism.comp, Function.comp]
        rw [hab.preserve_mul, hbc.preserve_mul]

    protected def Identity : α →* α where
      toMHomomorphism := MHomomorphism.Identity
      preserve_mul    := fun _ _ => rfl

    protected theorem preserve_one_of_1_in_image {f : α →* β} (h1 : 1 ∈ Function.image f.hom) : f 1 = 1 := by
      let ⟨x, hx⟩ := h1; rw [←hx, ←mul_one x, f.preserve_mul, hx, one_mul]

    protected theorem preserve_one_of_surjective {f : α →* β} (hf : Function.surjective f.hom) : f 1 = 1 :=
      SMulMap.preserve_one_of_1_in_image (hf 1)

    protected theorem preserve_pow_ne_zero (f : α →* β) (x : α) {n : Nat} (hn : n ≠ 0) : f (x ^ n) = f x ^ n := by
      have : ∀ n : Nat, f (x ^ n.succ) = f x ^ n.succ := fun n => by
        induction n with
        | zero      => rw [pow_nat_1, pow_nat_1]
        | succ n ih => rw [pow_nat_succ, f.preserve_mul, ih, ←pow_nat_succ]
      cases n; contradiction; exact this _

    protected def Product (f : α →* γ) (g : β →* δ) : α × β →* γ × δ where
      toMHomomorphism := f.toMHomomorphism.Product g.toMHomomorphism
      preserve_mul    := fun (a₁, b₁) (a₂, b₂) => congr (congrArg Prod.mk (f.preserve_mul a₁ a₂)) (g.preserve_mul b₁ b₂)

    protected noncomputable def MultiProd_cons {ι : Type _} (fι : ι → Type _) [∀ i, NCSemiring (fι i)] {s : Finset ι} {a : ι} (ha : a ∉ s) :
      MultiProd (fun i : s => fι i.val) × fι a →* MultiProd (fun i : s.cons a ha => fι i.val) where
        toMHomomorphism := MHomomorphism.MultiProd_cons fι ha
        preserve_mul    := fun x y => funext fun ⟨i, hi⟩ => by
          simp only [MHomomorphism.MultiProd_cons, multi_product.Mul_def, product_mul]
          byCases h : i = a
          { subst h; simp only [dite_true] }
          { simp only [h, dite_false] }

  end SMulMap

  namespace SHomomorphism
    variable [NCSemiring α] [NCSemiring β] [NCSemiring γ]

    def kernel (sh : α →*₁ β) : SubMonoid α := sh.toSMulMap.kernel

    def image (sh : α →*₁ β) : SubSemiring β where
      toSubMonoid := sh.toSMulMap.image
      has_one     := ⟨1, sh.preserve_one⟩
      mul_closed  := fun _ ⟨a, ha⟩ _ ⟨b, hb⟩ => ⟨a * b, ha ▸ hb ▸ sh.preserve_mul a b⟩

    protected def comp (hab : α →*₁ β) (hbc : β →*₁ γ) : α →*₁ γ where
      toSMulMap    := hab.toSMulMap.comp hbc.toSMulMap
      preserve_one := by
        simp only [SMulMap.comp, MHomomorphism.comp, Function.comp]
        rw [hab.preserve_one, hbc.preserve_one]

    protected def Identity : α →*₁ α where
      toSMulMap    := SMulMap.Identity
      preserve_one := rfl

    protected theorem preserve_pow (f : α →*₁ β) (x : α) : (n : Nat) → f (x ^ n) = f x ^ n
    | 0   => f.preserve_one
    | n+1 => f.preserve_pow_ne_zero x n.succ_ne_zero

  end SHomomorphism

  namespace SIsomorphism
    variable [NCSemiring α] [NCSemiring β] [NCSemiring γ] [NCSemiring δ]

    protected theorem preserve_one (f : α ≅* β) : f 1 = 1 :=
      SMulMap.preserve_one_of_surjective f.toMIsomorphism.to_surjective

    def toSHomomorphism (f : α ≅* β) : α →*₁ β where
      toSMulMap    := f.toSMulMap
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
      inv       := f
      left_inv  := f.right_inv
      right_inv := f.left_inv

    protected theorem comp (hab : α ≅* β) (hbc : β ≅* γ) : α ≅* γ where
      toSMulMap := hab.toSMulMap.comp hbc.toSMulMap
      inv       := hab.inv ∘ hbc.inv
      left_inv  := fun _ => by
        have : hab.toSMulMap.comp hbc.toSMulMap = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv := fun _ => by
        have : hab.toSMulMap.comp hbc.toSMulMap = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection (f : α →* β) (hf : Function.bijective f.hom) : α ≅* β where
        toSMulMap := f
        inv       := fun b => Classical.choose (hf.surj b)
        left_inv  := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
        right_inv := fun a => Classical.choose_spec (hf.surj a)

    protected noncomputable def Identity : α ≅* α :=
      SIsomorphism.of_bijection _ (by apply Function.id_bijective : Function.bijective SHomomorphism.Identity.hom)

    protected def SelfInverse (f : α →* α) (h : ∀ a, f (f a) = a) : α ≅* α where
      toSMulMap := f
      inv       := f.hom
      left_inv  := h
      right_inv := h

    protected def Product (f : α ≅* γ) (g : β ≅* δ) : α × β ≅* γ × δ where
      toSMulMap := f.toSMulMap.Product g.toSMulMap
      inv       := (f.toMIsomorphism.Product g.toMIsomorphism).inv
      left_inv  := (f.toMIsomorphism.Product g.toMIsomorphism).left_inv
      right_inv := (f.toMIsomorphism.Product g.toMIsomorphism).right_inv

    protected noncomputable def MultiProd_cons {ι : Type _} (fι : ι → Type _) [∀ i, NCSemiring (fι i)] {s : Finset ι} {a : ι} (ha : a ∉ s) :
      MultiProd (fun i : s => fι i.val) × fι a ≅* MultiProd (fun i : s.cons a ha => fι i.val) where
        toSMulMap := SMulMap.MultiProd_cons fι ha
        inv       := (MIsomorphism.MultiProd_cons fι ha).inv
        left_inv  := (MIsomorphism.MultiProd_cons fι ha).left_inv
        right_inv := (MIsomorphism.MultiProd_cons fι ha).right_inv

  end SIsomorphism

  namespace RMulMap
    variable [NCRing α] [NCRing β] [NCRing γ] [NCRing δ]

    def kernel (rlm : α →ᵣ β) : SubGroup α := rlm.toGHomomorphism.kernel

    def image (rlm : α →ᵣ β) : SubGroup β := rlm.toGHomomorphism.image

    protected def comp (hab : α →ᵣ β) (hbc : β →ᵣ γ) : α →ᵣ γ where
      toSMulMap    := hab.toSMulMap.comp hbc.toSMulMap
      preserve_neg := (hab.toGHomomorphism.comp hbc.toGHomomorphism).preserve_neg

    protected def Identity : α →ᵣ α where
      toSMulMap    := SMulMap.Identity
      preserve_neg := GHomomorphism.Identity.preserve_neg

    protected theorem preserve_one_of_1_in_image {f : α →ᵣ β} (h1 : 1 ∈ Function.image f.hom) : f 1 = 1 :=
      SMulMap.preserve_one_of_1_in_image h1

    protected theorem preserve_one_of_surjective {f : α →ᵣ β} (hf : Function.surjective f.hom) : f 1 = 1 :=
      SMulMap.preserve_one_of_surjective hf

    protected theorem preserve_pow_ne_zero (f : α →ᵣ β) (x : α) {n : Nat} (hn : n ≠ 0) : f (x ^ n) = f x ^ n :=
      f.toSMulMap.preserve_pow_ne_zero x hn

    protected def Product (f : α →ᵣ γ) (g : β →ᵣ δ) : α × β →ᵣ γ × δ where
      toSMulMap    := f.toSMulMap.Product g.toSMulMap
      preserve_neg := (f.toGHomomorphism.Product g.toGHomomorphism).preserve_neg

    protected noncomputable def MultiProd_cons {ι : Type _} (fι : ι → Type _) [∀ i, NCRing (fι i)] {s : Finset ι} {a : ι} (ha : a ∉ s) :
      MultiProd (fun i : s => fι i.val) × fι a →ᵣ MultiProd (fun i : s.cons a ha => fι i.val) where
        toSMulMap    := SMulMap.MultiProd_cons fι ha
        preserve_neg := (GHomomorphism.MultiProd_cons fι ha).preserve_neg

  end RMulMap

  namespace RHomomorphism
    variable [NCRing α] [NCRing β] [NCRing γ]

    def kernel (rh : α →ᵣ₁ β) : SubGroup α := rh.toRMulMap.kernel

    def image (rh : α →ᵣ₁ β) : SubRing β where
      toSubSemiring := rh.toSHomomorphism.image
      neg_closed    := rh.toGHomomorphism.image.neg_closed

    protected def comp (hab : α →ᵣ₁ β) (hbc : β →ᵣ₁ γ) : α →ᵣ₁ γ where
      toRMulMap    := hab.toRMulMap.comp hbc.toRMulMap
      preserve_one := (hab.toSHomomorphism.comp hbc.toSHomomorphism).preserve_one

    protected def Identity : α →ᵣ₁ α where
      toRMulMap    := RMulMap.Identity
      preserve_one := SHomomorphism.Identity.preserve_one

    protected theorem preserve_pow (f : α →ᵣ₁ β) (x : α) (n : Nat) : f (x ^ n) = f x ^ n :=
      f.toSHomomorphism.preserve_pow x n

  end RHomomorphism

  namespace RIsomorphism
    variable [NCRing α] [NCRing β] [NCRing γ] [NCRing δ]

    protected theorem preserve_one (f : α ≅ᵣ β) : f 1 = 1 :=
      RMulMap.preserve_one_of_surjective f.toMIsomorphism.to_surjective

    def toSHomomorphism (f : α ≅ᵣ β) : α →ᵣ₁ β where
      toRMulMap    := f.toRMulMap
      preserve_one := f.preserve_one

    protected def inv_hom [NCRing α] [NCRing β] (f : α ≅ᵣ β) : β →ᵣ₁ α where
      toMHomomorphism := f.toMIsomorphism.inv_hom
      preserve_neg    := fun a => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [this, ←ha, ←f.preserve_neg, f.left_inv, f.left_inv]
      preserve_one    := by
        have : f.toMIsomorphism.inv_hom (f 1) = f.inv (f 1) := rfl
        simp only; rw [←f.preserve_one, this, f.left_inv]
      preserve_mul    := fun a b => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        let ⟨_, hb⟩ := f.right_inv.surjective b
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [←ha, ←hb, this, ←f.preserve_mul, f.left_inv, f.left_inv, f.left_inv]

    protected def symm [NCRing α] [NCRing β] (f : α ≅ᵣ β) : β ≅ᵣ α where
      toRMulMap := f.inv_hom.toRMulMap
      inv       := f
      left_inv  := f.right_inv
      right_inv := f.left_inv

    protected theorem comp [NCRing α] [NCRing β] [NCRing γ] (hab : α ≅ᵣ β) (hbc : β ≅ᵣ γ) : α ≅ᵣ γ where
      toRMulMap := hab.toRMulMap.comp hbc.toRMulMap
      inv       := hab.inv ∘ hbc.inv
      left_inv  := fun _ => by
        have : hab.toRMulMap.comp hbc.toRMulMap = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv := fun _ => by
        have : hab.toRMulMap.comp hbc.toRMulMap = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection [NCRing α] [NCRing β] (f : α →ᵣ β)
      (hf : Function.bijective f.hom) : α ≅ᵣ β where
        toRMulMap := f
        inv       := fun b => Classical.choose (hf.surj b)
        left_inv  := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
        right_inv := fun a => Classical.choose_spec (hf.surj a)

    protected noncomputable def Identity [NCRing α] : α ≅ᵣ α :=
      RIsomorphism.of_bijection _ (by apply Function.id_bijective : Function.bijective RHomomorphism.Identity.hom)

    protected def SelfInverse [NCRing α] (f : α →ᵣ α) (h : ∀ a, f (f a) = a) : α ≅ᵣ α where
      toRMulMap := f
      inv       := f.hom
      left_inv  := h
      right_inv := h

    protected def Product (f : α ≅ᵣ γ) (g : β ≅ᵣ δ) : α × β ≅ᵣ γ × δ where
      toRMulMap := f.toRMulMap.Product g.toRMulMap
      inv       := (f.toMIsomorphism.Product g.toMIsomorphism).inv
      left_inv  := (f.toMIsomorphism.Product g.toMIsomorphism).left_inv
      right_inv := (f.toMIsomorphism.Product g.toMIsomorphism).right_inv

    protected noncomputable def MultiProd_cons {ι : Type _} (fι : ι → Type _) [∀ i, NCRing (fι i)] {s : Finset ι} {a : ι} (ha : a ∉ s) :
      MultiProd (fun i : s => fι i.val) × fι a ≅ᵣ MultiProd (fun i : s.cons a ha => fι i.val) where
        toRMulMap := RMulMap.MultiProd_cons fι ha
        inv       := (MIsomorphism.MultiProd_cons fι ha).inv
        left_inv  := (MIsomorphism.MultiProd_cons fι ha).left_inv
        right_inv := (MIsomorphism.MultiProd_cons fι ha).right_inv

  end RIsomorphism

  protected def NCSemiring.MulHomLeft [NCSemiring α] (a : α) : α →₊ α where
    hom           := (a * ·)
    preserve_zero := by simp only [NCSemiring.mul_zero]
    preserve_add  := fun _ _ => by simp only [NCSemiring.mul_distrib_left]

  protected def NCSemiring.MulHomRight [NCSemiring α] (a : α) : α →₊ α where
    hom           := (· * a)
    preserve_zero := by simp only [NCSemiring.zero_mul]
    preserve_add  := fun _ _ => by simp only [NCSemiring.mul_distrib_right]

  protected def NCRing.MulHomLeft [NCRing α] (a : α) : α →₋ α where
    toMHomomorphism := NCSemiring.MulHomLeft a
    preserve_neg    := fun _ => by simp only [NCSemiring.MulHomLeft, NCRing.mul_neg]

  protected def NCRing.MulHomRight [NCRing α] (a : α) : α →₋ α where
    toMHomomorphism := NCSemiring.MulHomRight a
    preserve_neg    := fun _ => by simp only [NCSemiring.MulHomRight, NCRing.neg_mul]

end M4R
