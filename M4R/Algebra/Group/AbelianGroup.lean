import M4R.Algebra.Group.SubGroup
import M4R.Set

namespace M4R
  open Group
  open AbelianGroup

  def UnorderedList.sum [AbelianGroup α] (s : UnorderedList α) : α := 
    s.fold (· + ·) (fun a b c => by simp only [add_assoc, add_comm b]) 0

  def UnorderedList.map_sum [AbelianGroup β] (s : UnorderedList α) (f : α → β) : β :=
    (s.map f).sum

  def Finset.sum [AbelianGroup α] (s : Finset α) : α := s.elems.sum
  def Finset.map_sum [AbelianGroup β] (s : Finset α) (f : α → β) : β := s.elems.map_sum f

  namespace UnorderedList.sum

    theorem cons [AbelianGroup α] (a : α) (s : UnorderedList α) : (∑ s.cons a) = (∑ s) + a := by
      simp only [sum, UnorderedList.fold.cons']

    @[simp] theorem cons_zero [AbelianGroup α] (s : UnorderedList α) : (∑ s.cons 0) = ∑ s := by
      rw [←add_zero (∑ s)]; exact cons 0 s

    @[simp] theorem singleton [AbelianGroup α] (a : α) : (∑ UnorderedList.singleton a) = a := by
      conv => rhs rw [←zero_add a]

  end UnorderedList.sum
  namespace UnorderedList.map_sum

    @[simp] theorem singleton [AbelianGroup β] (f : α → β) (a : α) : (∑ f in UnorderedList.singleton a) = f a := by
      simp only [map_sum, map.singleton f a, sum.singleton]

  end UnorderedList.map_sum
end M4R