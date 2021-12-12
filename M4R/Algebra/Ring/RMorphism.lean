import M4R.Algebra.Ring.Basic

namespace M4R

  structure RHomomorphism (α : Type _) (β : Type _) [Ring α] [Ring β] where
    hom           : α → β
    preserve_zero : hom 0 = 0
    preserve_one  : hom 1 = 1
    preserve_add  : ∀ a b, hom (a + b) = hom a + hom b
    preserve_neg  : ∀ a, hom (-a) = -hom a
    preserve_mul  : ∀ a b, hom a * hom b = hom (a * b)

  structure RIsomorphism (α : Type _) (β : Type _) [Ring α] [Ring β] extends RHomomorphism α β where
    bij : Function.bijective hom
  
  namespace RHomomorphism
  
    def to_GHomomorphism [Ring α] [Ring β] (rh : RHomomorphism α β) : GHomomorphism α β where
      hom           := rh.hom
      preserve_zero := rh.preserve_zero
      preserve_add  := rh.preserve_add
      preserve_neg  := rh.preserve_neg
  
  end RHomomorphism
  namespace RIsomorphism

    def to_GIsomorphism [Ring α] [Ring β] (ri : RIsomorphism α β) : GIsomorphism α β where
      toGHomomorphism := ri.toRHomomorphism.to_GHomomorphism
      bij             := ri.bij
  
  end RIsomorphism
end M4R