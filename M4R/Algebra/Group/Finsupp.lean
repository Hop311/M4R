import M4R.Algebra.Group.MapGroups
import M4R.Algebra.Group.Sum

namespace M4R

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
        rw [Finsupp.mk.injEq]
        exact ⟨Finset.ext fun _ => by rw [xc, yc, hf]; exact Iff.rfl, hf⟩

    protected theorem ext' [Zero β] {x y : α →₀ β} : x = y ↔ x.support = y.support ∧ ∀ a ∈ x.support, x a = y a :=
      ⟨fun h => by rw [h]; exact ⟨rfl, fun _ _ => rfl⟩, fun h => by
        apply Finsupp.ext; apply funext; intro a
        byCases hx : a ∈ x.support
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
      mem_support_to_fun := fun _ => ⟨fun h _ => h, fun h => h rfl⟩
    }

    theorem zero_apply [Zero β] {a : α} : (0 : α →₀ β) a = 0 := rfl
    theorem zero_support [Zero β] : (0 : α →₀ β).support = ∅ := rfl

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
        simp [support_of_fun]; exact Iff.rfl

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
        intro x hx
        apply Classical.byContradiction; intro h
        simp only [Finset.mem_union, not_or_iff_and_not] at h
        have : (f₁ + f₂) x = f₁ x + f₂ x := rfl
        rw [not_mem_support_iff.mp h.left, not_mem_support_iff.mp h.right, Monoid.add_zero] at this
        exact absurd this (mem_support_iff.mp hx)

    open Classical

    noncomputable def single [Zero β] (a : α) (b : β) : α →₀ β where
      support := if b = 0 then ∅ else Finset.singleton a
      to_fun := fun a' => if a' = a then b else 0
      mem_support_to_fun := fun a' => by
        byCases hb : b = 0
        exact ⟨fun h _ => by simp only [hb] at h; exact h,
          fun h => by
            simp only [hb] at h ⊢; apply h; byCases ha : a' = a
            repeat { simp only [ha]; rfl }⟩
        exact ⟨fun h => by
            simp only [hb] at h; have := Finset.in_singleton h
            simp only [this]; exact hb,
          fun h => by
            byCases ha : a' = a
            { simp only [hb, ha]; exact Finset.self_singleton a }
            { simp only [ha] at h; contradiction }⟩

    namespace single

      @[simp] protected theorem zero {α : Type _} (β : Type _) [Zero β] (a : α) : single a (0 : β) = 0 := by
        apply Finsupp.ext; apply funext; intro x; simp only [single]; byCases hx : x = a
        repeat { simp only [hx]; rfl }

      @[simp] theorem eq_same [Zero β] (a : α) (b : β): single a b a = b :=
        if_pos rfl

      @[simp] theorem eq_of_ne [Zero β] {a a' : α} (b : β) (h : a' ≠ a) : single a b a' = 0 :=
        if_neg h

      @[simp] protected theorem add [Monoid β] (a : α) (b₁ b₂ : β) :
        single a (b₁ + b₂) = single a b₁ + single a b₂ := by
        apply Finsupp.ext; apply funext; intro x
        byCases h : x = a
        { rw [h, add_apply, eq_same, eq_same, eq_same] }
        { rw [add_apply, eq_of_ne (b₁ + b₂) h, eq_of_ne b₁ h, eq_of_ne b₂ h, Monoid.zero_add] }

    end single

    noncomputable instance UnitFinsuppMonoid [Monoid α] : (Unit →₀ α) ≅₊ α where
      hom := (· Unit.unit)
      preserve_zero := rfl
      preserve_add := fun _ _ => rfl
      inv := fun a => single Unit.unit a
      left_inv := fun x => Finsupp.ext (funext fun u => by cases u; simp only [single.eq_same])
      right_inv := fun a => by simp only [single.eq_same]

    noncomputable instance UnitFinsuppGroup [Group α] : (Unit →₀ α) ≅₋ α where
      toMHomomorphism := UnitFinsuppMonoid.toMHomomorphism
      preserve_neg := fun _ => rfl
      inv := UnitFinsuppMonoid.inv
      left_inv := UnitFinsuppMonoid.left_inv
      right_inv := UnitFinsuppMonoid.right_inv

    theorem UnitFinsupp.single [Zero α] (x : Unit →₀ α) : x = single Unit.unit (x Unit.unit) :=
      Finsupp.ext (funext fun u => by cases u; simp only [single.eq_same])

    section erase

      noncomputable def erase [Zero β] (a : α) (f : α →₀ β) : α →₀ β where
        support := f.support.erase a
        to_fun := fun a' => if a' = a then 0 else f a'
        mem_support_to_fun := fun a' => by
          rw [Finset.mem_erase, mem_support_iff]
          byCases h : a' = a
          { simp only [h, ite_true, ne_eq, false_and] }
          { simp only [h, ite_false, ne_eq, true_and]; exact Iff.rfl }

      @[simp] theorem support_erase [Zero β] {a : α} {f : α →₀ β} :
        (f.erase a).support = f.support.erase a := rfl

      @[simp] theorem erase_same [Zero β] {a : α} {f : α →₀ β} : (f.erase a) a = 0 :=
        if_pos rfl

      @[simp] theorem erase_ne [Zero β] {a a' : α} {f : α →₀ β} (h : a' ≠ a) : (f.erase a) a' = f a' :=
        if_neg h

      @[simp] theorem erase_single [Zero β] {a : α} {b : β} : (erase a (single a b)) = 0 := by
        apply Finsupp.ext; apply funext; intro x
        byCases h : x = a
        { rw [h, erase_same, zero_apply] }
        { rw [erase_ne h]; exact single.eq_of_ne b h }

      theorem erase_single_ne [Zero β] {a a' : α} {b : β} (h : a ≠ a') : (erase a (single a' b)) = single a' b := by
        apply Finsupp.ext; apply funext; intro x
        byCases h' : x = a
        { rw [h', erase_same, single.eq_of_ne b h] }
        { rw [erase_ne h'] }

      @[simp] theorem erase_of_not_mem_support [Zero β] {f : α →₀ β} {a} (haf : a ∉ f.support) : erase a f = f := by
        apply Finsupp.ext; apply funext; intro x
        byCases h : x = a
        { rw [h, erase_same]; exact (not_mem_support_iff.mp haf).symm }
        { rw [erase_ne h] }

      @[simp] theorem erase_zero [Zero β] (a : α) : erase a (0 : α →₀ β) = 0 := by
        apply empty_support; rw [support_erase, zero_support, Finset.erase_empty]

    end erase

    section update
      variable [Zero β] (f : α →₀ β)

      noncomputable def update (a : α) (b : β) : α →₀ β where
        support := if b = 0 then f.support.erase a else f.support.insert a
        to_fun := Function.update f a b
        mem_support_to_fun := fun i => by
          simp only [Function.update_apply, ne_eq]
          byCases hb : b = 0
          { simp only [hb, ite_true]
            byCases hi : i = a;
            { simp only [hi, ite_true, Finset.mem_erase, ne_eq, false_and] }
            { simp only [hi, ite_false, Finset.mem_erase, ne_eq, true_and]; exact Finsupp.mem_support_iff } }
          { simp only [hb, ite_false]
            byCases hi : i = a;
            { simp only [hi, ite_true, Finset.mem_insert_self, true_iff]; exact hb }
            { simp only [hi, ite_false, Finset.mem_insert, false_or]; exact Finsupp.mem_support_iff } }

      @[simp] theorem coe_update (a : α) (b : β) :
        (f.update a b : α → β) = Function.update f a b := rfl

      @[simp] theorem update_self (a : α) : f.update a (f a) = f := by
        apply Finsupp.ext; apply funext; intro x
        simp only [update, Function.update_apply]
        byCases hx : x = a
        { simp only [hx, ite_true] }
        { simp only [hx, ite_false] }

      theorem support_update (a : α) (b : β) : support (f.update a b) =
        if b = 0 then f.support.erase a else f.support.insert a := rfl

      @[simp] theorem support_update_zero (a : α) :
        support (f.update a 0) = f.support.erase a := if_pos rfl

      theorem support_update_ne_zero (a : α) {b : β} (h : b ≠ 0) :
        support (f.update a b) = f.support.insert a := if_neg h

    end update
    section
      variable [Monoid β] (f : α →₀ β)

      theorem update_eq_single_add_erase (a : α) (b : β) :
        f.update a b = (single a b) + (f.erase a) := by
          apply Finsupp.ext; apply funext; intro j
          simp only [update, Function.update_apply, add_apply]
          byCases h : j = a
          { simp only [h, ite_true, single.eq_same, erase_same, Monoid.add_zero] }
          { simp only [h, ite_false, single.eq_of_ne b h, erase_ne h, Monoid.zero_add] }

      theorem update_eq_erase_add_single (f : α →₀ β) (a : α) (b : β) :
        f.update a b = f.erase a + single a b := by
          apply Finsupp.ext; apply funext; intro j
          simp only [update, Function.update_apply, add_apply]
          byCases h : j = a
          { simp only [h, ite_true, single.eq_same, erase_same, Monoid.zero_add] }
          { simp only [h, ite_false, single.eq_of_ne b h, erase_ne h, Monoid.add_zero] }

      theorem single_add_erase (a : α) (f : α →₀ β) : single a (f a) + f.erase a = f := by
        rw [←update_eq_single_add_erase, update_self]

      theorem erase_add_single (a : α) (f : α →₀ β) : f.erase a + single a (f a) = f := by
        rw [←update_eq_erase_add_single, update_self]

    end

    protected theorem induction [Monoid β] (p : (α →₀ β) → Prop) (f : α →₀ β)
      (h0 : p 0) (ha : ∀ a b (f : α →₀ β), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
      p f := by
        have : ∀ s (f : α →₀ β), f.support = s → p f := fun s =>
          Finset.induction_on (∀ (f : α →₀ β), f.support = · → p f) s
            (fun f hf => empty_support hf ▸ h0)
            (fun a s has ih f hf => by
              have := ha a (f a) (f.erase a)
                (by rw [support_erase, Finset.mem_erase]; exact (·.left rfl))
                (by rw [← mem_support_iff, hf]; exact Finset.mem_insert_self _ _)
                (by apply ih _ _; rw [support_erase, hf, Finset.erase_insert has])
              rw [single_add_erase] at this
              exact this)
        exact this _ _ rfl

    noncomputable def single_add_hom [Monoid β] (a : α) : β →₊ α →₀ β where
      hom := single a
      preserve_zero := single.zero β a
      preserve_add := single.add a

    theorem add_hom_ext [Monoid β] [Monoid γ] ⦃f g : (α →₀ β) →₊ γ⦄
      (h : ∀ x y, f (single x y) = g (single x y)) :
      f = g := by
        apply MHomomorphism.ext.mpr; apply funext; intro x
        exact Finsupp.induction (fun s => f s = g s) x
          (by simp only [f.preserve_zero, g.preserve_zero])
          (fun a b y hay hb hy => by simp only [f.preserve_add, g.preserve_add, hy, h a b])

    theorem add_hom_ext' [Monoid β] [Monoid γ] ⦃f g : (α →₀ β) →₊ γ⦄
      (h : ∀ x, (single_add_hom x).comp f = (single_add_hom x).comp g) :
        f = g := add_hom_ext fun x => MHomomorphism.congr_fun (h x)

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

      def apply_add_hom [CommMonoid β] (a : α) : (α →₀ β) →₊ β where
        hom           := fun g => g a
        preserve_zero := zero_apply
        preserve_add  := (add_apply · · a)

      theorem finset_sum_apply [CommMonoid β] (S : Finset ι) (f : ι → α →₀ β) (a : α) :
        (∑ f in S) a = ∑ (f · a) in S :=
          (apply_add_hom a).map_sum f S

      @[simp] theorem sum_apply [Zero β] [CommMonoid β'] {f : α →₀ β} {g : α → β → α' →₀ β'} {a₂ : α'} :
        (∑ g in f) a₂ = ∑ (fun a₁ b => g a₁ b a₂) in f :=
          finset_sum_apply _ _ _

      @[simp] protected theorem single [Zero β] [CommMonoid γ]
        (a : α) (b : β) (f : α → β → γ) (h : f a 0 = 0) : (∑ f in single a b) = f a b := by
          byCases hb : b = 0
          { simp [support_sum, single, hb, h] }
          { simp [support_sum, Finset.map_sum, single, hb, Finset.singleton] }

      theorem unit_sum [Zero α] [CommMonoid β] {f : Unit → α → β} (x : Unit →₀ α) (h : f Unit.unit 0 = 0):
        (∑ f in x) = f Unit.unit (x Unit.unit) := by
          rw [UnitFinsupp.single x, map_sum.single Unit.unit (x Unit.unit) f h, single.eq_same]

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

      theorem sum_finset_sum_index [CommMonoid β] [CommMonoid γ] {s : Finset ι} {g : ι → α →₀ β}
        {h : α → β → γ} (h_zero : ∀ a, h a 0 = 0) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
          (∑ (∑ h in g ·) in s) = ∑ h in (∑ g in s) :=
            Finset.induction_on (fun f => (∑ (∑ h in g ·) in f) = ∑ h in (∑ g in f)) s rfl
              (fun a s has ih => by
                simp only at ih ⊢
                rw [Finset.map_sum.sum_insert _ has, ih, Finset.map_sum.sum_insert _ has,
                  map_sum.add_sum (g a) (∑ g in s) h h_zero (h_add · _ _)])

      theorem sum_sum {β : Type _} {β' : Type _} {γ : Type _} [CommMonoid β] [CommMonoid β'] [CommMonoid γ]
        {f : α →₀ β} {g : α → β → α' →₀ β'} {h : α' → β' → γ}
        (h_zero : ∀ a, h a 0 = 0) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
          (∑ h in (∑ g in f)) = ∑ (fun a b => ∑ h in g a b) in f :=
            (sum_finset_sum_index h_zero h_add).symm

      noncomputable def lift_add_hom [CommMonoid β] [CommMonoid γ] : (α → β →₊ γ) ≅₊ ((α →₀ β) →₊ γ) where
        hom := fun f => {
          hom := fun x => ∑ a in x, f a
          preserve_zero := map_sum.zero_sum _
          preserve_add := fun x y =>
            map_sum.add_sum x y _ (by intro; rw [MHomomorphism.preserve_zero])
              (by intro; rw [add_apply, MHomomorphism.preserve_add])
        }
        preserve_zero := by
          apply MHomomorphism.ext.mpr; apply funext; exact map_sum.sum_zero
        preserve_add := fun x y => by
          apply MHomomorphism.ext.mpr; apply funext; intros; exact map_sum.sum_add
        inv := fun f x => (single_add_hom x).comp f
        left_inv := by
          intro x; apply funext; intro a; apply MHomomorphism.ext.mpr; apply funext; intro b
          exact map_sum.single a b _ (x a).preserve_zero
        right_inv := fun x => add_hom_ext
          (fun a b => by
            simp only [single_add_hom]
            rw [map_sum.single a b _ (MHomomorphism.preserve_zero _), MHomomorphism.comp.hom])

      @[simp] theorem lift_add_hom_single_add_hom [CommMonoid β] :
        lift_add_hom (single_add_hom : α → β →₊ α →₀ β) = MHomomorphism.Identity := by
          apply MHomomorphism.ext.mpr; apply funext; intros; apply Finsupp.ext; apply funext; intros
          rw [←lift_add_hom.right_inv (MHomomorphism.Identity : (α →₀ β) →₊ α →₀ β)]; rfl

      @[simp] theorem sum_single [CommMonoid β] (f : α →₀ β) : (∑ single in f) = f :=
        MHomomorphism.congr_fun lift_add_hom_single_add_hom f

    end map_sum
  end Finsupp
end M4R
