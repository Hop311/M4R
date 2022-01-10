import M4R.Algebra.Ring.SubRing

namespace M4R

  structure RHomomorphism (α : Type _) (β : Type _) [Ring α] [Ring β] where
    hom           : α → β
    preserve_zero : hom 0 = 0
    preserve_one  : hom 1 = 1
    preserve_add  : ∀ a b, hom (a + b) = hom a + hom b
    preserve_neg  : ∀ a, hom (-a) = -hom a
    preserve_mul  : ∀ a b, hom (a * b) = hom a * hom b

  structure RIsomorphism (α : Type _) (β : Type _) [Ring α] [Ring β] extends RHomomorphism α β where
    bij : Function.bijective hom
  
  instance RHomomorphismFun [Ring α] [Ring β] : CoeFun (RHomomorphism α β) (fun _ => α → β) where
    coe := RHomomorphism.hom

  namespace RHomomorphism
  
    def to_GHomomorphism [Ring α] [Ring β] (rh : RHomomorphism α β) : GHomomorphism α β where
      hom           := rh.hom
      preserve_zero := rh.preserve_zero
      preserve_add  := rh.preserve_add
      preserve_neg  := rh.preserve_neg
  
    def GHomomorphismSubRing [Ring α] [Ring β] (rh : RHomomorphism α β) (S : SubRing α): SubRing β where
      subset := {x | ∃ y ∈ S, rh y = x}
      has_zero := ⟨0, S.has_zero, rh.preserve_zero⟩
      has_one := ⟨1, S.has_one, rh.preserve_one⟩
      add_closed := fun a ⟨a', a'S, ha⟩ b ⟨b', b'S, hb⟩ =>
        ⟨a' + b', S.add_closed _ a'S _ b'S, by rw [←ha, ←hb]; exact rh.preserve_add a' b'⟩
      neg_closed := fun a ⟨a', a'S, ha⟩ =>
        ⟨-a', S.neg_closed _ a'S, by rw [←ha]; exact rh.preserve_neg a'⟩
      mul_closed := by exact fun a ⟨a', a'S, ha⟩ b ⟨b', b'S, hb⟩ =>
        ⟨a' * b', S.mul_closed _ a'S _ b'S, by rw [←ha, ←hb]; exact rh.preserve_mul a' b'⟩

  end RHomomorphism
  namespace RIsomorphism

    def to_GIsomorphism [Ring α] [Ring β] (ri : RIsomorphism α β) : GIsomorphism α β where
      toGHomomorphism := ri.toRHomomorphism.to_GHomomorphism
      bij             := ri.bij
  
  end RIsomorphism
end M4R