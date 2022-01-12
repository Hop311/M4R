import M4R.Algebra.Ring.Defs

namespace M4R
  open NCSemiring
  open Semiring

  def UnorderedList.prod [Semiring α] (s : UnorderedList α) : α := 
    s.fold (· * ·) (fun a b c => by simp only [mul_assoc, mul_comm b]) 1
  def UnorderedList.map_prod [Semiring β] (s : UnorderedList α) (f : α → β) : β :=
    (s.map f).prod

  def Finset.prod [Semiring α] (s : Finset α) : α := s.elems.prod
  def Finset.map_prod [Semiring β] (s : Finset α) (f : α → β) : β := s.elems.map_prod f
end M4R
