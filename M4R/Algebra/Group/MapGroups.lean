import M4R.Algebra.Group.Group
import M4R.Algebra.Group.Sum

namespace M4R
 
  instance MapZero (α : Type _) (β : Type _) [Zero β] : Zero (α → β) where zero := fun _ => 0

  instance MapAdd (α : Type _) (β : Type _) [Monoid β] : Add (α → β) where add := fun x y a => x a + y a

  instance MapMonoid (α : Type _) (β : Type _) [Monoid β] : Monoid (α → β) where
    add_zero := fun x => funext fun _ => Monoid.add_zero _
    zero_add := fun x => funext fun a => by conv => rhs rw [←Monoid.zero_add (x a)]
    add_assoc := fun x y z => funext fun a => Monoid.add_assoc _ _ _
  
  instance MapCommMonoid (α : Type _) (β : Type _) [CommMonoid β] : CommMonoid (α → β) where
    add_comm := fun x y => funext fun a => CommMonoid.add_comm _ _

  instance MapNeg (α : Type _) (β : Type _) [Group β] : Neg (α → β) where neg := fun x a => - x a

  instance MapGroup (α : Type _) (β : Type _) [Group β] : Group (α → β) where
    add_neg := fun _ => funext fun _ => Group.add_neg _
  
  instance MapAbelianGroup (α : Type _) (β : Type _) [AbelianGroup β] : AbelianGroup (α → β) where
    add_comm := (MapCommMonoid α β).add_comm

  structure Finsupp (α : Type _) (β : Type _) [Zero β] :=
  (support            : Finset α)
  (to_fun             : α → β)
  (mem_support_to_fun : ∀a, a ∈ support ↔ to_fun a ≠ 0)

  infixr:25 " →₀ " => Finsupp
  
  namespace Finsupp

    instance FinsuppFun [Zero β] : CoeFun (α →₀ β) (fun (x : α →₀ β) => α → β) where coe := to_fun

    @[simp] theorem mem_support_iff [Zero β] {f : α →₀ β} {a : α} : a ∈ f.support ↔ f a ≠ 0 :=
      f.mem_support_to_fun a

    theorem not_mem_support_iff [Zero β] {f : α →₀ β} {a : α} : a ∉ f.support ↔ f a = 0 := by
      apply not_iff_not.mp
      simp only [iff_not_not]
      exact mem_support_iff

    protected theorem ext [Zero β] {x y : α →₀ β} : x.to_fun = y.to_fun → x = y :=
      match x, y with | ⟨xs, _, xc⟩, ⟨ys, _, yc⟩ => fun hf => by
        simp at hf
        rw [Finsupp.mk.injEq];
        exact ⟨Finset.ext fun _ => by rw [xc, yc, hf]; exact Iff.refl _, hf⟩

    protected theorem ext' [Zero β] {x y : α →₀ β} : x = y ↔ x.support = y.support ∧ ∀ a ∈ x.support, x a = y a :=
      ⟨fun h => by rw [h]; exact ⟨rfl, fun _ _ => rfl⟩, fun h => by
        apply Finsupp.ext; apply funext; intro a;
        byCases hx : a ∈ x.support;
        exact h.right a hx
        have hy : a ∉ y.support := by rw [h.left] at hx; exact hx
        rw [of_not_not (mt mem_support_iff.mpr hx),
          of_not_not (mt mem_support_iff.mpr hy)]⟩

    protected theorem ext_iff [Zero β] (x y : α →₀ β) : x = y ↔ x.to_fun = y.to_fun :=
      ⟨fun h => by rw [h], Finsupp.ext⟩

    protected instance zero (α : Type _) (β : Type _) [Zero β] : Zero (α →₀ β) where zero :=
    {
      support            := ∅
      to_fun             := fun _ => 0
      mem_support_to_fun := fun a => ⟨fun h _ => h, fun h => h rfl⟩
    }

    theorem empty_support [Zero β] {f : α →₀ β} (h : f.support = ∅) : f = 0 :=
      Finsupp.ext (funext fun x => by
        have : x ∉ f.support := fun h' => by rw [h] at h'; contradiction
        rw [of_not_not (mt mem_support_iff.mpr this)]; rfl)

    theorem zero_fun [Zero β] {f : α →₀ β} (h : ∀ a, f a = 0) : f = 0 :=
      Finsupp.ext (funext fun x => by rw [h x]; rfl)

    def support_set_of_fun [Zero β] (f : α → β) : Set α := {a | f a ≠ 0}

    theorem support_of_fun_finite [Zero β] (x y : α →₀ β) (f : α → β) (h : ∀ a, x a = 0 → y a = 0 → f a = 0) :
      finite (support_set_of_fun f) :=
        finite.subset (finite.union x.support.to_finite y.support.to_finite) fun a af =>
          Classical.byContradiction fun h' =>
            have h' := not_or_iff_and_not.mp h'
            af (h a
              (of_not_not (mt mem_support_iff.mpr h'.left))
              (of_not_not (mt mem_support_iff.mpr h'.right)))

    noncomputable def support_of_fun [Zero β] (x y : α →₀ β) (f : α → β) (h : ∀ a, x a = 0 → y a = 0 → f a = 0) : Finset α :=
      (support_of_fun_finite x y f h).to_finset

    theorem support_of_fun_complete [Zero β] (x y : α →₀ β) (f : α → β) (h : ∀ a, x a = 0 → y a = 0 → f a = 0) :
      ∀ a, a ∈ support_of_fun x y f h ↔ f a ≠ 0 := fun _ => by
        simp [support_of_fun]; exact Iff.refl _

    noncomputable def finsupp_fun [Zero β] (f : (α →₀ β) → (α →₀ β) → α → β)  
      (h : ∀ (x y : α →₀ β) (a : α), x a = 0 → y a = 0 → f x y a = 0) (x y : α →₀ β) : α →₀ β where
      to_fun := f x y
      support := support_of_fun x y (f x y) (h x y)
      mem_support_to_fun := support_of_fun_complete x y (f x y) (h x y)

    protected noncomputable instance add [Monoid β] : Add (α →₀ β) where
      add := finsupp_fun (·.to_fun + ·.to_fun) (fun x y a hx hy => by
        simp only [HAdd.hAdd, Add.add, add_eq]; rw [hx, hy, Monoid.add_zero])

    noncomputable instance toMonoid [Monoid β] : Monoid (α →₀ β) where
      add_zero := fun _ => Finsupp.ext (funext fun _ => Monoid.add_zero _)
      zero_add := fun _ => Finsupp.ext (funext fun _ => Monoid.zero_add _)
      add_assoc := fun _ _ _ => Finsupp.ext (funext fun _ => Monoid.add_assoc _ _ _)

    noncomputable instance toCommMonoid [CommMonoid β] : CommMonoid (α →₀ β) where
      add_comm := fun _ _ => Finsupp.ext (funext fun _ => CommMonoid.add_comm _ _)

    protected instance neg [Group β] : Neg (α →₀ β) where
      neg := fun x => {
        support := x.support
        to_fun := (- x ·)
        mem_support_to_fun := fun a =>
          have : x a ≠ 0 ↔ - x a ≠ 0 := by
            simp only [not_iff_not]
            exact ⟨fun h' => by rw [h', Group.neg_zero], fun h' => by
              rw [←Group.neg_zero] at h'
              exact Group.neg_inj h'⟩
          mem_support_iff.trans this
      }

    noncomputable instance toGroup [Group β] : Group (α →₀ β) where
      add_neg := fun _ => Finsupp.ext (funext fun _ => Group.add_neg _)

    noncomputable instance toAbelianGroup [AbelianGroup β] : AbelianGroup (α →₀ β) where
      add_comm := toCommMonoid.add_comm

    theorem add_apply [Monoid β] (f₁ f₂ : α →₀ β) (a : α) : (f₁ + f₂) a = f₁ a + f₂ a := rfl

    theorem support_add [Monoid β] {f₁ f₂ : α →₀ β} :
      (f₁ + f₂).support ⊆ f₁.support ∪ f₂.support := by
        intro x hx;
        apply Classical.byContradiction; intro h;
        simp only [Finset.mem_union, not_or_iff_and_not] at h
        have : (f₁ + f₂) x = f₁ x + f₂ x := rfl
        rw [not_mem_support_iff.mp h.left, not_mem_support_iff.mp h.right, Monoid.add_zero] at this
        exact absurd this (mem_support_iff.mp hx)

    open Classical

    noncomputable def single [Zero β] (a : α) (b : β) : α →₀ β where
      support := if b = 0 then ∅ else Finset.singleton a
      to_fun := fun a' => if a' = a then b else 0
      mem_support_to_fun := fun a' => by
        byCases hb : b = 0;
        exact ⟨fun h _ => by simp only [hb] at h; exact h,
          fun h => by
            simp only [hb] at h ⊢; apply h; byCases ha : a' = a;
            repeat { simp only [ha]; rfl }⟩
        exact ⟨fun h => by
            simp only [hb] at h; have := Finset.in_singleton h
            simp only [this]; exact hb,
          fun h => by
            byCases ha : a' = a;
            { simp only [hb, ha]; exact Finset.self_singleton a }
            { simp only [ha] at h; contradiction }⟩

    namespace single

      @[simp] protected theorem zero {α : Type _} (β : Type _) [Zero β] (a : α) : single a (0 : β) = 0 := by
        apply Finsupp.ext; apply funext; intro x; simp only [single]; byCases hx : x = a;
        repeat { simp only [hx]; rfl }

      @[simp] theorem eq_same [Zero β] (a : α) (b : β): single a b a = b :=
        if_pos rfl

      @[simp] theorem eq_of_ne [Zero β] {a a' : α} (b : β) (h : a' ≠ a) : single a b a' = 0 :=
        if_neg h

      @[simp] protected theorem add [Monoid β] (a : α) (b₁ b₂ : β) :
        single a (b₁ + b₂) = single a b₁ + single a b₂ := by
        apply Finsupp.ext; apply funext; intro x;
        byCases h : x = a;
        { rw [h, add_apply, eq_same, eq_same, eq_same] }
        { rw [add_apply, eq_of_ne (b₁ + b₂) h, eq_of_ne b₁ h, eq_of_ne b₂ h, Monoid.zero_add] }

    end single

    protected def map_sum [Zero β] [CommMonoid γ] (f : α →₀ β) (g : α → β → γ) : γ :=
      ∑ a in f.support, g a (f a)

    namespace map_sum

      theorem support_sum [Zero β] [CommMonoid γ] (x : α →₀ β) (f : α → β → γ) : (∑ f in x) = ∑ a in x.support, f a (x a) := rfl

      @[simp] protected theorem zero_sum [Zero β] [CommMonoid γ] (f : α → β → γ) : (∑ f in (0 : α →₀ β)) = 0 :=
        UnorderedList.map_sum.eq_zero fun _ _ => by contradiction

      @[simp] protected theorem sum_zero [Zero β] [CommMonoid γ] (x : α →₀ β) : (∑ fun _ _ => (0 : γ) in x) = 0 :=
        UnorderedList.map_sum.eq_zero fun _ _ => rfl

      @[simp] protected theorem map_eq_zero [Zero β] [CommMonoid γ] {x : α →₀ β} {f : α → β → γ}
        (h : ∀ a ∈ x.support, f a (x a) = 0) : (∑ f in x) = 0 :=
          UnorderedList.map_sum.eq_zero h

      @[simp] protected theorem congr [Zero β] [CommMonoid γ] {x : α →₀ β} {f g : α → β → γ}
        (h : ∀ a ∈ x.support, f a (x a) = g a (x a)) : (∑ f in x) = (∑ g in x) :=
          UnorderedList.map_sum.congr rfl h


      @[simp] protected theorem single [Zero β] [CommMonoid γ]
        (a : α) (b : β) (f : α → β → γ) (h : f a 0 = 0) : (∑ f in single a b) = f a b := by
          byCases hb : b = 0;
          { simp [support_sum, single, hb, h] }
          { simp [support_sum, Finset.map_sum, single, hb, Finset.singleton] }

      theorem support_subset [Zero β] [CommMonoid γ] (f : α →₀ β) {s : Finset α}
        (hs : f.support ⊆ s) (g : α → β → γ) (h : ∀ i ∈ s, g i 0 = 0) :
          (∑ g in f) = ∑ x in s, g x (f x) :=
            Finset.map_sum.subset hs (fun x hxs hx => by
              rw [of_not_not (mt mem_support_iff.mpr hx)]
              exact h x hxs)

      theorem sum_add [Zero β] [CommMonoid γ] {f : α →₀ β} {h₁ h₂ : α → β → γ} :
        (∑ (fun a b => h₁ a b + h₂ a b) in f) = (∑ h₁ in f) + (∑ h₂ in f) :=
          Finset.map_sum.distrib (fun a => h₁ a (f a)) (fun a => h₂ a (f a)) f.support

      protected theorem add_sum [Monoid β] [CommMonoid γ] (x y : α →₀ β) (f : α → β → γ)
        (h₁ : ∀ a, f a 0 = 0) (h₂ : ∀ a, f a ((x + y) a) = f a (x a) + f a (y a)) :
          (∑ f in x + y) = (∑ f in x) + (∑ f in y) := by
            have hx : (∑ f in x) = ∑ a in x.support ∪ y.support, f a (x a) :=
              support_subset x (Finset.subset_union_left _ _) f (fun a ha => h₁ a)
            have hy : (∑ f in y) = ∑ a in x.support ∪ y.support, f a (y a) :=
              support_subset y (Finset.subset_union_right _ _) f (fun a ha => h₁ a)
            have hxy : (∑ f in x + y) = ∑ a in x.support ∪ y.support, f a ((x + y) a) :=
              support_subset (x + y) support_add f (fun a ha => h₁ a)
            have := Finset.map_sum.distrib (fun a => f a (x a)) (fun a => f a (y a)) (x.support ∪ y.support)
            rw [hx, hy, hxy, ←this]
            exact Finset.map_sum.congr rfl fun a _ => h₂ a

      protected theorem id [CommMonoid β] (x : α →₀ β) :
        (∑ single in x) = x := by
        apply Finsupp.ext; apply funext; intro y;
        sorry

    end map_sum
  end Finsupp
end M4R
