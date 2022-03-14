import M4R.Algebra.Ring.Ideal

namespace M4R
  
  structure MultiplicativeSet (α : Type _) [Ring α] where
    subset : Set α
    has_one : 1 ∈ subset
    mul_closed : ∀ {a b : α}, a ∈ subset → b ∈ subset → a * b ∈ subset
  instance MultiplicativeSet.MultiplicativeSetMem [Ring α]: Mem α (MultiplicativeSet α) where mem := fun x I => x ∈ I.subset

  theorem MultiplicativeSet.disjoint_ideal_proper [Ring α] {S : MultiplicativeSet α}
    {I : Ideal α} (hIS : Set.disjoint I.subset S.subset) : I.proper_ideal := fun h =>
      absurd (Ideal.is_unit_ideal.mp h) (Set.disjoint.elementwise.mp (hIS.comm) 1 S.has_one)

  def localisation_setoid [Ring α] (S : MultiplicativeSet α) : Setoid (α × S.subset) where
    r     := fun x y => ∃ s ∈ S, s * x.fst * y.snd.val = s * y.fst * x.snd.val
    iseqv := {
      refl  := fun _ => ⟨1, S.has_one, rfl⟩
      symm  := fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩
      trans := by--fun h₁ h₂ => by
        intro x y z ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
        have := congr (funext fun _ => h₁ ▸ rfl : (s₁ * x.fst * y.snd.val * ·) = (s₁ * y.fst * x.snd.val * ·)) h₂
        exact ⟨s₁ * y.fst * y.snd.val * s₂, by sorry, by sorry⟩
    }

  def localisation [Ring α] (S : MultiplicativeSet α) := Quotient (localisation_setoid S)

  instance localisation_ring [Ring α] {S : MultiplicativeSet α} : Ring (localisation S) := sorry

end M4R
