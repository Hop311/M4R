import M4R.Algebra.Group.SubGroup
import M4R.Set

namespace M4R
  open Group
  namespace AbelianGroup

    theorem add_right_comm [AbelianGroup α] (a b c : α) : a + b + c = a + c + b := by
      rw [add_assoc, add_comm b, ←add_assoc]

    theorem add_left_comm [AbelianGroup α] (a b c : α) : a + (b + c) = b + (a + c) := by
      rw [←add_assoc, add_comm a, add_assoc]

  end AbelianGroup

  open AbelianGroup

  def UnorderedList.fold_add [AbelianGroup α] (init : α) (s : UnorderedList α) :=
    s.fold (· + ·) (fun _ _ _ => by simp only [add_right_comm]) init

  namespace UnorderedList.fold_add

    theorem cons [AbelianGroup α] (init a : α) (s : UnorderedList α) : (s.cons a).fold_add init = s.fold_add init + a :=
      UnorderedList.fold.cons' _ _ init a s

    theorem init_change [AbelianGroup α] (init a : α) (s : UnorderedList α) : s.fold_add (init + a) = s.fold_add init + a := by
      have : (s.cons a).fold_add init = s.fold_add (init + a) :=
        UnorderedList.fold.cons _ _ init a s
      rw [←this, cons]

    theorem init_swap [AbelianGroup α] (a b : α) (s : UnorderedList α) : s.fold_add a + b = s.fold_add b + a := by
      rw [←init_change, ←init_change, add_comm]

    theorem append [AbelianGroup α] (init : α) (s t : UnorderedList α) : (s + t).fold_add init + init = s.fold_add init + t.fold_add init := by
      have : (s + t).fold_add init = t.fold_add (s.fold_add init) := by
        simp only [fold_add, fold.append];
      rw [this, init_swap, add_comm]

  end UnorderedList.fold_add

  def UnorderedList.sum [AbelianGroup α] (s : UnorderedList α) : α := 
    s.fold_add 0

  def UnorderedList.map_sum [AbelianGroup β] (s : UnorderedList α) (f : α → β) : β :=
    (s.map f).sum

  def Finset.sum [AbelianGroup α] (s : Finset α) : α := s.elems.sum
  def Finset.map_sum [AbelianGroup β] (s : Finset α) (f : α → β) : β := s.elems.map_sum f

  namespace UnorderedList.sum

    theorem cons [AbelianGroup α] (a : α) (s : UnorderedList α) : (∑ s.cons a) = (∑ s) + a :=
      fold_add.cons 0 a s

    @[simp] theorem cons_zero [AbelianGroup α] (s : UnorderedList α) : (∑ s.cons 0) = ∑ s := by
      rw [←add_zero (∑ s)]; exact cons 0 s

    @[simp] theorem singleton [AbelianGroup α] (a : α) : (∑ UnorderedList.singleton a) = a := by
      conv => rhs rw [←zero_add a]

    theorem all_zero [AbelianGroup α] (s : UnorderedList α) (h : ∀ x ∈ s, x = 0) : (∑ s) = 0 :=
      @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
        (∀ a ∈ l, a = 0) → (∑ l) = 0) s (fun l hl => by
          induction l with
          | nil => rfl
          | cons x l ih =>
            rw [UnorderedList.cons', cons, hl x (by rw [UnorderedList.cons']; exact UnorderedList.mem_cons_self _ _), add_zero]
            exact ih (fun a ha => hl a (UnorderedList.mem_cons_of_mem ha)))
        h

    theorem append [AbelianGroup α] (s t : UnorderedList α) : (∑ s + t) = (∑ s) + (∑ t) := by
      have := fold_add.append 0 s t
      rw [add_zero] at this
      exact this

  end UnorderedList.sum
  namespace UnorderedList.map_sum

    @[simp] theorem singleton [AbelianGroup β] (f : α → β) (a : α) : (∑ f in UnorderedList.singleton a) = f a := by
      simp only [map_sum, map.singleton f a, sum.singleton]

  end UnorderedList.map_sum
end M4R