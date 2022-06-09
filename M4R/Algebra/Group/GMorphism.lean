import M4R.Algebra.Group.SubGroup
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
    inv       : β → α
    left_inv  : Function.left_inverse inv hom
    right_inv : Function.right_inverse inv hom
  infixr:25 " ≅₊ " => MIsomorphism
  instance MIsomorphismFun [Monoid α] [Monoid β] : CoeFun (α ≅₊ β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure GHomomorphism (α : Type _) (β : Type _) [Group α] [Group β] extends α →₊ β where
    preserve_neg  : ∀ a, hom (-a) = -hom a
  infixr:25 " →₋ " => GHomomorphism
  instance GHomomorphismFun [Group  α] [Group  β] : CoeFun (α →₋ β) (fun _ => α → β) where
    coe := fun f => f.hom

  structure GIsomorphism (α : Type _) (β : Type _) [Group α] [Group β] extends α →₋ β, α ≅₊ β
  infixr:25 " ≅₋ " => GIsomorphism
  instance GIsomorphismFun [Group  α] [Group  β] : CoeFun (α ≅₋ β) (fun _ => α → β) where
    coe := fun f => f.hom

  namespace MHomomorphism
    variable [Monoid α] [Monoid β] [Monoid γ] [Monoid δ]

    def kernel (mh : α →₊ β) : SubMonoid α where
      subset     := Function.fibre mh.hom 0
      has_zero   := mh.preserve_zero
      add_closed := fun _ x0 _ y0 => by
        simp only [Mem.mem, Set.mem, Function.fibre]; rw [mh.preserve_add, x0, y0, Monoid.add_zero]

    def image (mh : α →₊ β) : SubMonoid β where
      subset     := Function.image mh.hom
      has_zero   := ⟨0, mh.preserve_zero⟩
      add_closed := fun _ ⟨x, hx⟩ _ ⟨y, hy⟩ => ⟨x + y, hx ▸ hy ▸ mh.preserve_add x y⟩

    protected def comp (hab : α →₊ β) (hbc : β →₊ γ) : α →₊ γ where
      hom           := Function.comp hbc.hom hab.hom
      preserve_zero := by simp only [Function.comp]; rw [hab.preserve_zero, hbc.preserve_zero]
      preserve_add  := fun a b => by simp only [Function.comp]; rw [hab.preserve_add, hbc.preserve_add]

    protected def comp.hom (hab : α →₊ β) (hbc : β →₊ γ) :
      (hab.comp hbc).hom = hbc.hom ∘ hab.hom := rfl

    protected def Identity : α →₊ α where
      hom           := id
      preserve_zero := rfl
      preserve_add  := by intros; rfl

    protected theorem congr_fun {f g : α →₊ β} (h : f = g) (x : α) : f x = g x :=
      congrArg (· x) h

    protected theorem ext : ∀ {f g : α →₊ β}, f = g ↔ f.hom = g.hom
    | ⟨_, _, _⟩, ⟨_, _, _⟩ =>
      ⟨fun h => by rw [h], fun h => by rw [MHomomorphism.mk.injEq]; exact h⟩

    protected def Product (f : α →₊ γ) (g : β →₊ δ) : α × β →₊ γ × δ where
      hom           := fun (a, b) => (f a, g b)
      preserve_zero := congr (congrArg Prod.mk f.preserve_zero) g.preserve_zero
      preserve_add  := fun (a₁, b₁) (a₂, b₂) => congr (congrArg Prod.mk (f.preserve_add a₁ a₂)) (g.preserve_add b₁ b₂)

    open Classical

    protected noncomputable def MultiProd_cons {ι : Type _} (fι : ι → Type _) [∀ i, Monoid (fι i)] {s : Finset ι} {a : ι} (ha : a ∉ s) :
      MultiProd (fun i : s => fι i.val) × fι a →₊ MultiProd (fun i : s.cons a ha => fι i.val) where
        hom           := fun x ⟨i, hi⟩ => if h : i = a then by subst h; exact x.snd else x.fst ⟨i, (Finset.mem_cons.mp hi).resolve_left h⟩
        preserve_zero := funext fun ⟨i, hi⟩ => by
          byCases h : i = a
          { subst h; simp only [dite_true]; rfl }
          { simp only [h, dite_false]; rfl }
        preserve_add  := fun x y => funext fun ⟨i, hi⟩ => by
          simp only [Monoid.multi_product.Add_def, Monoid.product_add]
          byCases h : i = a
          { subst h; simp only [dite_true] }
          { simp only [h, dite_false] }

  end MHomomorphism

  theorem MHomomorphism.map_sum' [CommMonoid β] [CommMonoid γ] (g : β →₊ γ) (f : α → β) (s : UnorderedList α) :
    g (∑ f in s) = ∑ (g ∘ f) in s :=
      @UnorderedList.induction_on α (fun t => g (∑ f in t) = ∑ (g ∘ f) in t) s g.preserve_zero (by
        intro _ _ ih; rw [UnorderedList.map_sum.cons, UnorderedList.map_sum.cons,
          MHomomorphism.preserve_add, ih])

  theorem MHomomorphism.map_sum [CommMonoid β] [CommMonoid γ] (g : β →₊ γ) (f : α → β) (s : Finset α) :
    g (∑ f in s) = ∑ (g ∘ f) in s :=
      map_sum' g f s

  namespace MIsomorphism
    variable [Monoid α] [Monoid β] [Monoid γ] [Monoid δ]

    protected def inv_hom (f : α ≅₊ β) : β →₊ α where
      hom           := f.inv
      preserve_zero := by
        conv => lhs rw [←f.preserve_zero]
        rw [f.left_inv]
      preserve_add  := fun a b => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        let ⟨_, hb⟩ := f.right_inv.surjective b
        rw [←ha, ←hb, ←f.preserve_add, f.left_inv, f.left_inv, f.left_inv]

    protected def symm (f : α ≅₊ β) : β ≅₊ α where
      toMHomomorphism := f.inv_hom
      inv       := f
      left_inv  := f.right_inv
      right_inv := f.left_inv

    protected theorem comp (hab : α ≅₊ β) (hbc : β ≅₊ γ) : α ≅₊ γ where
      toMHomomorphism := hab.toMHomomorphism.comp hbc.toMHomomorphism
      inv := hab.inv ∘ hbc.inv
      left_inv := fun _ => by
        have : hab.toMHomomorphism.comp hbc.toMHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv := fun _ => by
        have : hab.toMHomomorphism.comp hbc.toMHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection (f : α →₊ β) (hf : Function.bijective f.hom) : α ≅₊ β where
      toMHomomorphism := f
      inv       := fun b => Classical.choose (hf.surj b)
      left_inv  := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
      right_inv := fun a => Classical.choose_spec (hf.surj a)

    protected def to_bijective (f : α ≅₊ β) : Function.bijective f.hom :=
      Function.bijective_of_inverse f.left_inv f.right_inv

    protected def to_injective (f : α ≅₊ β) : Function.injective f.hom :=
      (MIsomorphism.to_bijective f).left

    protected def to_surjective (f : α ≅₊ β) : Function.surjective f.hom :=
      (MIsomorphism.to_bijective f).right

    protected noncomputable def Identity : α ≅₊ α :=
      MIsomorphism.of_bijection _ (by apply Function.id_bijective : Function.bijective MHomomorphism.Identity.hom)

    protected def SelfInverse (f : α →₊ α) (h : ∀ a, f (f a) = a) : α ≅₊ α where
      toMHomomorphism := f
      inv       := f.hom
      left_inv  := h
      right_inv := h

    protected def Product (f : α ≅₊ γ) (g : β ≅₊ δ) : α × β ≅₊ γ × δ where
      toMHomomorphism := f.toMHomomorphism.Product g.toMHomomorphism
      inv             := fun (c, d) => (f.inv c, g.inv d)
      left_inv        := fun (a, b) => congr (congrArg Prod.mk (f.left_inv a)) (g.left_inv b)
      right_inv       := fun (c, d) => congr (congrArg Prod.mk (f.right_inv c)) (g.right_inv d)

    protected noncomputable def MultiProd_cons {ι : Type _} (fι : ι → Type _) [∀ i, Monoid (fι i)] {s : Finset ι} {a : ι} (ha : a ∉ s) :
      MultiProd (fun i : s => fι i.val) × fι a ≅₊ MultiProd (fun i : s.cons a ha => fι i.val) where
        toMHomomorphism := MHomomorphism.MultiProd_cons fι ha
        inv             := fun x => (fun ⟨i, hi⟩ => x ⟨i, Finset.mem_cons_self' ha hi⟩, x ⟨a, s.mem_cons_self ha⟩)
        left_inv        := fun (_, _) => congr (congrArg Prod.mk (funext fun ⟨i, hi⟩ => by
          have : i ≠ a := fun h => absurd (h ▸ hi) ha
          simp only [MHomomorphism.MultiProd_cons, this, dite_false]))
          (by simp only [MHomomorphism.MultiProd_cons, dite_true])
        right_inv       := fun x => funext fun ⟨i, hi⟩ => by
          simp only [MHomomorphism.MultiProd_cons]
          byCases h : i = a
          { subst h; simp only [dite_true] }
          { simp only [h, dite_false] }

  end MIsomorphism

  namespace GHomomorphism
    variable [Group α] [Group β] [Group γ] [Group δ]

    theorem preserve_sub (gh : α →₋ β) (a b : α) : gh (a - b) = gh a - gh b := by
      rw [Group.sub_def, gh.preserve_add, gh.preserve_neg]; rfl

    def kernel (gh : α →₋ β) : SubGroup α where
      toSubMonoid := MHomomorphism.kernel gh.toMHomomorphism
      neg_closed  := fun x x0 => by
        simp only [MHomomorphism.kernel, Mem.mem, Set.mem, Function.fibre]
        rw [gh.preserve_neg, x0, Group.neg_zero]

    def image (gh : α →₋ β) : SubGroup β where
      toSubMonoid := MHomomorphism.image gh.toMHomomorphism
      neg_closed  := fun _ ⟨x, hx⟩ => ⟨-x, hx ▸ gh.preserve_neg x⟩

    protected def comp (hab : α →₋ β) (hbc : β →₋ γ) : α →₋ γ where
      toMHomomorphism := hab.toMHomomorphism.comp hbc.toMHomomorphism
      preserve_neg  := fun a => by
        simp only [MHomomorphism.comp, Function.comp]
        rw [hab.preserve_neg, hbc.preserve_neg]

    protected def Identity : α →₋ α where
      toMHomomorphism := MHomomorphism.Identity
      preserve_neg    := by intros; rfl

    protected theorem ext : ∀ {f g : α →₋ β}, f = g ↔ f.hom = g.hom
    | ⟨_, _⟩, ⟨_, _⟩ =>
      ⟨fun h => by rw [h], fun h => by rw [GHomomorphism.mk.injEq]; exact MHomomorphism.ext.mpr h⟩

    theorem kernel_normal (f : α →₋ β) : f.kernel.is_normal :=
      fun a (ha : f a = 0) g => (by rw [MHomomorphism.preserve_add, MHomomorphism.preserve_add,
        GHomomorphism.preserve_neg, ha, Monoid.add_zero, Group.neg_add] : f _ = 0)

    protected def Product (f : α →₋ γ) (g : β →₋ δ) : α × β →₋ γ × δ where
      toMHomomorphism := f.toMHomomorphism.Product g.toMHomomorphism
      preserve_neg    := fun (a, b) => congr (congrArg Prod.mk (f.preserve_neg a)) (g.preserve_neg b)

    protected noncomputable def MultiProd_cons {ι : Type _} (fι : ι → Type _) [∀ i, Group (fι i)] {s : Finset ι} {a : ι} (ha : a ∉ s) :
      MultiProd (fun i : s => fι i.val) × fι a →₋ MultiProd (fun i : s.cons a ha => fι i.val) where
        toMHomomorphism := MHomomorphism.MultiProd_cons fι ha
        preserve_neg    := fun x => funext fun ⟨i, hi⟩ => by
          simp only [MHomomorphism.MultiProd_cons, Group.multi_product.Neg_def, Group.product_neg]
          byCases h : i = a
          { subst h; simp only [dite_true] }
          { simp only [h, dite_false] }

  end GHomomorphism

  namespace GIsomorphism
    variable [Group α] [Group β] [Group γ] [Group δ]

    protected def inv_hom (f : α ≅₋ β) : β →₋ α where
      toMHomomorphism := f.toMIsomorphism.inv_hom
      preserve_neg := fun a => by
        let ⟨_, ha⟩ := f.right_inv.surjective a
        have : f.toMIsomorphism.inv_hom.hom = f.inv := rfl
        rw [this, ←ha, ←f.preserve_neg, f.left_inv, f.left_inv]

    protected def symm (f : α ≅₋ β) : β ≅₋ α where
      toGHomomorphism := f.inv_hom
      inv := f
      left_inv := f.right_inv
      right_inv := f.left_inv

    protected theorem comp (hab : α ≅₋ β) (hbc : β ≅₋ γ) : α ≅₋ γ where
      toGHomomorphism := hab.toGHomomorphism.comp hbc.toGHomomorphism
      inv := hab.inv ∘ hbc.inv
      left_inv := fun _ => by
        have : hab.toGHomomorphism.comp hbc.toGHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hbc.left_inv, hab.left_inv]
      right_inv := fun _ => by
        have : hab.toGHomomorphism.comp hbc.toGHomomorphism = hbc.hom ∘ hab.hom := rfl
        rw [this, ←Function.comp_eq, ←Function.comp_eq, hab.right_inv, hbc.right_inv]

    protected noncomputable def of_bijection (f : α →₋ β) (hf : Function.bijective f.hom) : α ≅₋ β where
      toGHomomorphism := f
      inv := fun b => Classical.choose (hf.surj b)
      left_inv := fun a => hf.inj (Classical.choose_spec (hf.surj (f a)))
      right_inv := fun a => Classical.choose_spec (hf.surj a)

    protected noncomputable def Identity : α ≅₋ α :=
      GIsomorphism.of_bijection _ (by apply Function.id_bijective : Function.bijective GHomomorphism.Identity.hom)

    protected def SelfInverse (f : α →₋ α) (h : ∀ a, f (f a) = a) : α ≅₋ α where
      toGHomomorphism := f
      inv := f.hom
      left_inv := h
      right_inv := h

    protected def Product (f : α ≅₋ γ) (g : β ≅₋ δ) : α × β ≅₋ γ × δ where
      toGHomomorphism := f.toGHomomorphism.Product g.toGHomomorphism
      inv             := (f.toMIsomorphism.Product g.toMIsomorphism).inv
      left_inv        := (f.toMIsomorphism.Product g.toMIsomorphism).left_inv
      right_inv       := (f.toMIsomorphism.Product g.toMIsomorphism).right_inv

    protected noncomputable def MultiProd_cons {ι : Type _} (fι : ι → Type _) [∀ i, Group (fι i)] {s : Finset ι} {a : ι} (ha : a ∉ s) :
      MultiProd (fun i : s => fι i.val) × fι a ≅₋ MultiProd (fun i : s.cons a ha => fι i.val) where
        toGHomomorphism := GHomomorphism.MultiProd_cons fι ha
        inv             := (MIsomorphism.MultiProd_cons fι ha).inv
        left_inv        := (MIsomorphism.MultiProd_cons fι ha).left_inv
        right_inv       := (MIsomorphism.MultiProd_cons fι ha).right_inv

  end GIsomorphism

  protected def AbelianGroup.NegHom [AbelianGroup α] : α →₋ α where
    hom := (- ·)
    preserve_zero := by simp only [Group.neg_zero]
    preserve_add := fun _ _ => by simp only [AbelianGroup.neg_add_distrib]
    preserve_neg := fun _ => by rfl

  protected def AbelianGroup.NegIso [AbelianGroup α] : α ≅₋ α := GIsomorphism.SelfInverse
    AbelianGroup.NegHom (fun _ => by simp only [AbelianGroup.NegHom, Group.neg_neg])

end M4R
