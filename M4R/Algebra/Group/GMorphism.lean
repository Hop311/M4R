import M4R.Algebra.Group.Group
import M4R.Algebra.Group.Sum

namespace M4R

  structure MHomomorphism (α : Type _) (β : Type _) [Monoid α] [Monoid β] where
    hom           : α → β
    preserve_zero : hom 0 = 0
    preserve_add  : ∀ a b, hom (a + b) = hom a + hom b
  
  infixr:25 " →₊ " => MHomomorphism
  instance MHomomorphismFun [Monoid α] [Monoid β] : CoeFun (α →₊ β) (fun _ => α → β) where
    coe := MHomomorphism.hom

  structure MIsomorphism (α : Type _) (β : Type _) [Monoid α] [Monoid β] extends α →₊ β where
    inv : β → α
    left_inv : Function.left_inverse inv hom
    right_inv : Function.right_inverse inv hom

  infixr:25 " ≅₊ " => MIsomorphism
  instance MIsomorphismFun  [Monoid α] [Monoid β] : CoeFun (α ≅₊ β) (fun _ => α → β) where
    coe := fun f => f.hom
  
  structure GHomomorphism (α : Type _) (β : Type _) [Group α] [Group β] extends α →₊ β where
    preserve_neg  : ∀ a, hom (-a) = -hom a

  infixr:25 " →₋ " => GHomomorphism
  instance GHomomorphismFun [Group  α] [Group  β] : CoeFun (α →₋ β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure GIsomorphism (α : Type _) (β : Type _) [Group α] [Group β] extends α →₋ β, α ≅₊ β

  infixr:25 " ≅₋ " => GIsomorphism
  instance GIsomorphismFun  [Group  α] [Group  β] : CoeFun (α ≅₋ β) (fun _ => α → β) where
    coe := fun f => f.hom

  def MHomomorphism.kernel [Monoid α] [mb : Monoid β] (mh : α →₊ β) : SubMonoid α where
    subset     := Function.fibre mh.hom 0
    has_zero   := mh.preserve_zero
    add_closed := fun _ x0 _ y0 => by
      simp only [Mem.mem, Set.mem, Function.fibre]; rw [mh.preserve_add, x0, y0, mb.add_zero]

  def GHomomorphism.kernel [Group α] [gb : Group β] (gh : α →₋ β) : SubGroup α where
    toSubMonoid := MHomomorphism.kernel gh.toMHomomorphism
    neg_closed  := fun x x0 => by
      simp only [MHomomorphism.kernel, Mem.mem, Set.mem, Function.fibre]
      rw [gh.preserve_neg, x0, gb.neg_zero]

  namespace MHomomorphism

    protected def comp [Monoid α] [Monoid β] [Monoid γ] (hbc : β →₊ γ) (hab : α →₊ β) : α →₊ γ where
      hom           := Function.comp hbc.hom hab.hom
      preserve_zero := by simp only [Function.comp]; rw [hab.preserve_zero, hbc.preserve_zero]
      preserve_add  := fun a b => by simp only [Function.comp]; rw [hab.preserve_add, hbc.preserve_add]

    protected def comp.hom [Monoid α] [Monoid β] [Monoid γ] (hbc : β →₊ γ) (hab : α →₊ β) :
      (hbc.comp hab).hom = hbc.hom ∘ hab.hom := rfl

    def ImageSubMonoid [Monoid α] [Monoid β] (gh : α →₊ β) : SubMonoid β where
      subset     := Function.image gh.hom
      has_zero   := ⟨0, gh.preserve_zero⟩
      add_closed := fun _ ⟨a, hax⟩ _ ⟨b, hby⟩ => by rw [←hax, ←hby]; exact ⟨a + b, gh.preserve_add a b⟩

    protected def Identity [Monoid α] : α →₊ α where
      hom           := id
      preserve_zero := rfl
      preserve_add  := by intros; rfl

    protected theorem congr_fun [Monoid α] [Monoid β] {f g : α →₊ β} (h : f = g) (x : α) : f x = g x :=
      congrArg (· x) h

    theorem map_sum [CommMonoid β] [CommMonoid γ] (g : β →₊ γ) (f : α → β) (s : Finset α) :
      g (∑ f in s) = ∑ (g ∘ f) in s :=
        @Finset.induction_on α (fun t => g (∑ f in t) = ∑ (g ∘ f) in t) s g.preserve_zero (by
          intro _ _ h ih; rw [Finset.map_sum.sum_insert _ h, Finset.map_sum.sum_insert _ h,
            MHomomorphism.preserve_add, ih])

    protected theorem ext [Monoid α] [Monoid β] : ∀ {f g : α →₊ β}, f = g ↔ f.hom = g.hom
    | ⟨_, _, _⟩, ⟨_, _, _⟩ =>
      ⟨fun h => by rw [h], fun h => by rw [MHomomorphism.mk.injEq]; exact h⟩

  end MHomomorphism

  namespace MIsomorphism

    protected def inv_hom [Monoid α] [Monoid β] (f : α ≅₊ β) : β →₊ α where
      hom := f.inv
      preserve_zero := by
        conv => lhs rw [←f.preserve_zero]
        rw [f.left_inv]
      preserve_add := fun a b => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        let ⟨_, hb⟩ := f.right_inv.surjective b
        rw [←ha, ←hb, ←f.preserve_add, f.left_inv, f.left_inv, f.left_inv]

    protected def symm [Monoid α] [Monoid β] (f : α ≅₊ β) : β ≅₊ α where
      toMHomomorphism := f.inv_hom
      inv := f
      left_inv := f.right_inv
      right_inv := f.left_inv

    protected theorem comp [Monoid α] [Monoid β] [Monoid γ] (hbc : β ≅₊ γ) (hab : α ≅₊ β) : α ≅₊ γ where
      toMHomomorphism := hbc.toMHomomorphism.comp hab.toMHomomorphism
      inv := hab.inv ∘ hbc.inv
      left_inv := by
        intro a
        have : hbc.toMHomomorphism.comp hab.toMHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv := by
        intro a
        have : hbc.toMHomomorphism.comp hab.toMHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection [Monoid α] [Monoid β] {f : α →₊ β} (hf : Function.bijective f.hom) : α ≅₊ β where
      toMHomomorphism := f
      inv := fun b => Classical.choose (hf.surj b)
      left_inv := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
      right_inv := fun a => Classical.choose_spec (hf.surj a)

    protected def to_bijection [Monoid α] [Monoid β] (f : α ≅₊ β) : Function.bijective f.hom :=
      Function.bijective_of_inverse f.left_inv f.right_inv

    protected noncomputable def Identity [Monoid α] : α ≅₊ α :=
      MIsomorphism.of_bijection (by apply Function.id_bijective : Function.bijective MHomomorphism.Identity.hom)

    protected def SelfInverse [Monoid α] (f : α →₊ α) (h : ∀ a, f (f a) = a) : α ≅₊ α where
      toMHomomorphism := f
      inv := f.hom
      left_inv := h
      right_inv := h

  end MIsomorphism

  namespace GHomomorphism

    protected def comp [Group α] [Group β] [Group γ] (hbc : β →₋ γ) (hab : α →₋ β) : α →₋ γ where
      toMHomomorphism := hbc.toMHomomorphism.comp hab.toMHomomorphism
      preserve_neg  := fun a => by
        simp only [MHomomorphism.comp, Function.comp];
        rw [hab.preserve_neg, hbc.preserve_neg]

    def ImageSubGroup [Group α] [Group β] (gh : α →₋ β) : SubGroup β where
      toSubMonoid := gh.ImageSubMonoid
      neg_closed := fun x ⟨a, hax⟩ => by rw [←hax]; exact ⟨-a, gh.preserve_neg a⟩

    protected def Identity [Group α] : α →₋ α where
      toMHomomorphism := MHomomorphism.Identity
      preserve_neg    := by intros; rfl

    protected theorem ext [Group α] [Group β] : ∀ {f g : α →₋ β}, f = g ↔ f.hom = g.hom
    | ⟨_, _⟩, ⟨_, _⟩ =>
      ⟨fun h => by rw [h], fun h => by rw [GHomomorphism.mk.injEq]; exact MHomomorphism.ext.mpr h⟩

    protected structure constructor_gh (α : Type _) (β : Type _) [Group α] [Group β] where
      hom          : α → β
      preserve_add : ∀ a b, hom (a + b) = hom a + hom b
      preserve_neg : ∀ a, hom (-a) = -hom a

    protected def construct [Group α] [Group β] (c : GHomomorphism.constructor_gh α β) : GHomomorphism α β where
      hom := c.hom
      preserve_zero := by
        byCases h : ∃ x : α, x ≠ 0
        { cases h with | intro x hx =>
          rw [←Group.add_neg x, c.preserve_add, c.preserve_neg, Group.add_neg] }
        { simp only [not_exists, iff_not_not] at h; rw [←Monoid.add_zero 0, c.preserve_add];
          conv => lhs rhs rw [←Group.neg_zero]
          rw [c.preserve_neg, Group.add_neg] }
      preserve_add := c.preserve_add
      preserve_neg := c.preserve_neg

    protected def to_constructor [Group α] [Group β] (f : GHomomorphism α β): GHomomorphism.constructor_gh α β where
      hom          := f.hom
      preserve_add := f.preserve_add
      preserve_neg := f.preserve_neg

  end GHomomorphism

  namespace GIsomorphism

    protected def inv_hom [Group α] [Group β] (f : α ≅₋ β) : β →₋ α where
      toMHomomorphism := f.toMIsomorphism.inv_hom
      preserve_neg := fun a => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [this, ←ha, ←f.preserve_neg, f.left_inv, f.left_inv]

    protected def symm [Group α] [Group β] (f : α ≅₋ β) : β ≅₋ α where
      toGHomomorphism := f.inv_hom
      inv := f
      left_inv := f.right_inv
      right_inv := f.left_inv

    protected theorem comp [Group α] [Group β] [Group γ] (hbc : β ≅₋ γ) (hab : α ≅₋ β) : α ≅₋ γ where
      toGHomomorphism := hbc.toGHomomorphism.comp hab.toGHomomorphism
      inv := hab.inv ∘ hbc.inv
      left_inv := by
        intro a
        have : hbc.toGHomomorphism.comp hab.toGHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv := by
        intro a
        have : hbc.toGHomomorphism.comp hab.toGHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection [Group α] [Group β] {f : α →₋ β} (hf : Function.bijective f.hom) : α ≅₋ β where
      toGHomomorphism := f
      inv := fun b => Classical.choose (hf.surj b)
      left_inv := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
      right_inv := fun a => Classical.choose_spec (hf.surj a)

    protected noncomputable def Identity [Group α] : α ≅₋ α :=
      GIsomorphism.of_bijection (by apply Function.id_bijective : Function.bijective GHomomorphism.Identity.hom)

    protected def SelfInverse [Group α] (f : α →₋ α) (h : ∀ a, f (f a) = a) : α ≅₋ α where
      toGHomomorphism := f
      inv := f.hom
      left_inv := h
      right_inv := h

  end GIsomorphism

  protected def AbelianGroup.NegHom [AbelianGroup α] : α →₋ α where
    hom := (- ·)
    preserve_zero := by simp only [Group.neg_zero]
    preserve_add := fun _ _ => by simp only [AbelianGroup.neg_add_distrib]
    preserve_neg := fun _ => by rfl

  protected def AbelianGroup.NegIso [AbelianGroup α] : α ≅₋ α := GIsomorphism.SelfInverse
    AbelianGroup.NegHom (fun _ => by simp only [AbelianGroup.NegHom, Group.neg_neg])

end M4R