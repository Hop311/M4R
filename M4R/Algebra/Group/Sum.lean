import M4R.Algebra.Group.Monoid
import M4R.Set

namespace M4R
  open Monoid
  open CommMonoid

  def UnorderedList.fold_add [CommMonoid α] (init : α) (s : UnorderedList α) :=
    s.fold (· + ·) (fun _ _ _ => by simp only [add_right_comm]) init

  namespace UnorderedList.fold_add

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

    theorem distrib [CommMonoid α] (init : α) (f g : β → α) (s : UnorderedList β) :
      init + s.map_fold_add init (fun b => f b + g b) =
        (s.map_fold_add init f) + (s.map_fold_add init g) := by
          simp only [map_fold_add, map_fold.distrib]
  
  end UnorderedList.map_fold_add

  def UnorderedList.sum [CommMonoid α] (s : UnorderedList α) : α := 
    s.fold_add 0

  def UnorderedList.map_sum [CommMonoid β] (s : UnorderedList α) (f : α → β) : β :=
    s.map_fold_add 0 f

  def Finset.sum [CommMonoid α] (s : Finset α) : α := s.elems.sum
  def Finset.map_sum [CommMonoid β] (s : Finset α) (f : α → β) : β := s.elems.map_sum f

  namespace UnorderedList.sum

    theorem cons [CommMonoid α] (a : α) (s : UnorderedList α) : (∑ s.cons a) = (∑ s) + a :=
      fold_add.cons 0 a s

    @[simp] theorem cons_zero [CommMonoid α] (s : UnorderedList α) : (∑ s.cons 0) = ∑ s := by
      rw [←add_zero (∑ s)]; exact cons 0 s

    @[simp] theorem singleton [CommMonoid α] (a : α) : (∑ UnorderedList.singleton a) = a := by
      conv => rhs rw [←zero_add a]

    theorem all_zero [CommMonoid α] (s : UnorderedList α) (h : ∀ x ∈ s, x = 0) : (∑ s) = 0 :=
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

    @[simp] theorem singleton [CommMonoid β] (f : α → β) (a : α) : (∑ f in UnorderedList.singleton a) = f a := by
      simp only [map_sum, map_fold_add, map_fold, map.singleton f a, fold.singleton, zero_add]

    theorem all_zero [CommMonoid β] (f : α → β) (s : UnorderedList α) (h : ∀ x ∈ s, f x = 0) :
      (∑ f in s) = 0 :=
        UnorderedList.sum.all_zero _ fun x hx =>
          let ⟨a, ha, he⟩ := UnorderedList.map.mem_map.mp hx
          he.symm.trans (h a ha)

    theorem distrib [CommMonoid β] (f g : α → β) (s : UnorderedList α) :
      (∑ x in s, f x + g x) = (∑ f in s) + ∑ g in s := by
        have := map_fold_add.distrib 0 f g s
        rw [zero_add] at this
        simp only [map_sum, this]

  end UnorderedList.map_sum
end M4R