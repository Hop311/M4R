import M4R.Algebra.Group.Monoid
import M4R.Set

namespace M4R
  open Monoid
  open CommMonoid

  def UnorderedList.fold_add [CommMonoid α] (init : α) (s : UnorderedList α) :=
    s.fold (· + ·) (fun _ _ _ => by apply add_right_comm) init

  namespace UnorderedList.fold_add

    @[simp] theorem empty [CommMonoid α] (init : α) : UnorderedList.fold_add init ∅ = init := rfl

    theorem cons [CommMonoid α] (init a : α) (s : UnorderedList α) : (s.cons a).fold_add init = s.fold_add init + a :=
      UnorderedList.fold.cons' _ _ init a s

    theorem init_change [CommMonoid α] (init a : α) (s : UnorderedList α) : s.fold_add (init + a) = s.fold_add init + a := by
      have : (s.cons a).fold_add init = s.fold_add (init + a) :=
        UnorderedList.fold.cons _ _ init a s
      rw [←this, cons]

    theorem init_swap [CommMonoid α] (a b : α) (s : UnorderedList α) : s.fold_add a + b = s.fold_add b + a := by
      rw [←init_change, ←init_change, add_comm]

    theorem append [CommMonoid α] (init : α) (s t : UnorderedList α) : (s + t).fold_add init + init = s.fold_add init + t.fold_add init := by
      have : (s + t).fold_add init = t.fold_add (s.fold_add init) := by
        simp only [fold_add, fold.append];
      rw [this, init_swap, add_comm]

  end UnorderedList.fold_add

  def UnorderedList.map_fold_add [CommMonoid α] (init : α) (f : β → α) (s : UnorderedList β) : α :=
    s.map_fold (· + ·) CommMonoid.add_comm Monoid.add_assoc init f

  namespace UnorderedList.map_fold_add

    @[simp] theorem empty [CommMonoid α] (init : α) (f : β → α) : UnorderedList.map_fold_add init f ∅ = init := rfl

    theorem distrib [CommMonoid α] (init : α) (f g : β → α) (s : UnorderedList β) :
      init + s.map_fold_add init (fun b => f b + g b) =
        (s.map_fold_add init f) + (s.map_fold_add init g) := by
          simp only [map_fold_add, map_fold.distrib]

    theorem congr_map [CommMonoid α] (init : α) {s : UnorderedList β} {f g : β → α} (H : ∀ x ∈ s, f x = g x) :
      s.map_fold_add init f = s.map_fold_add init g :=
        map_fold.congr_map (· + ·) CommMonoid.add_comm Monoid.add_assoc init H

  end UnorderedList.map_fold_add

  def UnorderedList.sum [CommMonoid α] (s : UnorderedList α) : α := 
    s.fold_add 0

  def UnorderedList.map_sum [CommMonoid β] (s : UnorderedList α) (f : α → β) : β :=
    s.map_fold_add 0 f

  namespace UnorderedList.sum

    @[simp] theorem empty [CommMonoid α] : (∑ (∅ : UnorderedList α)) = 0 := rfl

    theorem cons [CommMonoid α] (a : α) (s : UnorderedList α) : (∑ s.cons a) = (∑ s) + a :=
      fold_add.cons 0 a s

    @[simp] theorem cons_zero [CommMonoid α] (s : UnorderedList α) : (∑ s.cons 0) = ∑ s := by
      rw [←add_zero (∑ s)]; exact cons 0 s

    @[simp] theorem singleton [CommMonoid α] (a : α) : (∑ UnorderedList.singleton a) = a := by
      conv => rhs rw [←zero_add a]

    theorem eq_zero [CommMonoid α] {s : UnorderedList α} (h : ∀ x ∈ s, x = 0) : (∑ s) = 0 :=
      @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
        (∀ a ∈ l, a = 0) → (∑ l) = 0) s (fun l hl => by
          induction l with
          | nil => rfl
          | cons x l ih =>
            rw [UnorderedList.cons', cons, hl x (by rw [UnorderedList.cons']; exact UnorderedList.mem_cons_self _ _), add_zero]
            exact ih (fun a ha => hl a (UnorderedList.mem_cons_of_mem ha)))
        h

    theorem append [CommMonoid α] (s t : UnorderedList α) : (∑ s + t) = (∑ s) + (∑ t) := by
      have := fold_add.append 0 s t
      rw [add_zero] at this
      exact this

  end UnorderedList.sum
  namespace UnorderedList.map_sum

    @[simp] theorem empty [CommMonoid β] (f : α → β) : (∑ f in (∅ : UnorderedList α)) = 0 := rfl

    theorem congr [CommMonoid β] {f g : α → β} {s₁ s₂ : UnorderedList α} (h : s₁ = s₂) :
      (∀ x ∈ s₂, f x = g x) → (∑ f in s₁) = ∑ g in s₂ := by
        rw [h]; exact UnorderedList.map_fold_add.congr_map 0

    @[simp] theorem singleton [CommMonoid β] (f : α → β) (a : α) : (∑ f in UnorderedList.singleton a) = f a := by
      simp only [map_sum, map_fold_add, map_fold, map.singleton f a, fold.singleton, zero_add]

    theorem eq_zero [CommMonoid β] {f : α → β} {s : UnorderedList α} (h : ∀ x ∈ s, f x = 0) :
      (∑ f in s) = 0 :=
        UnorderedList.sum.eq_zero fun x hx =>
          let ⟨a, ha, he⟩ := UnorderedList.map.mem_map.mp hx
          he.symm.trans (h a ha)

    theorem distrib [CommMonoid β] (f g : α → β) (s : UnorderedList α) :
      (∑ x in s, f x + g x) = (∑ f in s) + ∑ g in s := by
        have := map_fold_add.distrib 0 f g s
        rw [zero_add] at this
        simp only [map_sum, this]

  end UnorderedList.map_sum

  def Finset.sum [CommMonoid α] (s : Finset α) : α := s.elems.sum
  def Finset.map_sum [CommMonoid β] (s : Finset α) (f : α → β) : β := s.elems.map_sum f
  
  namespace Finset.sum

    @[simp] theorem empty [CommMonoid α] : (∑ (∅ : Finset α)) = 0 := rfl

    theorem eq_zero [CommMonoid α] {s : Finset α} (h : ∀ x ∈ s, x = 0) : (∑ s) = 0 :=
      UnorderedList.sum.eq_zero h

    @[simp] theorem sum_insert [CommMonoid α] {a : α} {s : Finset α} : a ∉ s → (∑ insert a s) = a + ∑ s := by
      rw [add_comm]; exact fold.fold_insert (· + ·) (fun _ _ _ => by apply add_right_comm) 0

  end Finset.sum

  namespace Finset.map_sum

    @[simp] theorem empty [CommMonoid β] (f : α → β) : (∑ f in (∅ : Finset α)) = 0 := rfl

    theorem eq_zero [CommMonoid β] {f : α → β} {s : Finset α} (h : ∀ x ∈ s, f x = 0) :
      (∑ f in s) = 0 :=
        UnorderedList.map_sum.eq_zero h

    theorem distrib [CommMonoid β] (f g : α → β) (s : Finset α) :
      (∑ x in s, f x + g x) = (∑ f in s) + ∑ g in s := by
        exact UnorderedList.map_sum.distrib f g s

    theorem congr [CommMonoid β] {f g : α → β} {s₁ s₂ : Finset α} (h : s₁ = s₂) :
      (∀ x ∈ s₂, f x = g x) → (∑ f in s₁) = ∑ g in s₂ :=
        UnorderedList.map_sum.congr (val_inj.mpr h)

    theorem union_inter [CommMonoid β] {f : α → β} {s₁ s₂ : Finset α} :
      (∑ f in (s₁ ∪ s₂)) + (∑ f in (s₁ ∩ s₂)) = (∑ f in s₁) + (∑ f in s₂) :=
        Finset.map_fold.union_inter (· + ·) CommMonoid.add_comm Monoid.add_assoc f

    theorem union [CommMonoid β] {f : α → β} {s₁ s₂ : Finset α} (h : disjoint s₁ s₂) :
      (∑ f in (s₁ ∪ s₂)) = (∑ f in s₁) + (∑ f in s₂) := by
        rw [←union_inter, h, empty, add_zero]

    theorem sdiff [CommMonoid β] {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) {f : α → β} :
      (∑ f in (s₂ ∖ s₁)) + (∑ f in s₁) = (∑ f in s₂) := by
        rw [←union (((s₂ ∖ s₁).inter_comm s₁).trans (s₁.inter_sdiff_self s₂)), sdiff_union_of_subset h]

    theorem subset_zero_on_sdiff [CommMonoid β] {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) {f g : α → β}
      (hg : ∀ x ∈ (s₂ ∖ s₁), g x = 0) (hfg : ∀ x ∈ s₁, f x = g x) : (∑ f in s₁) = ∑ g in s₂ := by
        rw [←sdiff h, eq_zero hg, zero_add]
        exact congr rfl hfg

    theorem subset [CommMonoid β] {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) {f : α → β} (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 0) :
      (∑ f in s₁) = ∑ f in s₂ :=
        subset_zero_on_sdiff h (by simp only [mem_sdiff, and_imp]; exact hf) (fun _ _ => rfl)

    @[simp] theorem sum_insert [CommMonoid β] (f : α → β) {a : α} {s : Finset α} :
      a ∉ s → (∑ f in insert a s) = f a + ∑ f in s :=
        map_fold.fold_insert (· + ·) add_comm add_assoc 0 f

  end Finset.map_sum
end M4R