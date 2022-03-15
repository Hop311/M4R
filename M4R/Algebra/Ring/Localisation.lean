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

  abbrev frac [Ring α] (S : MultiplicativeSet α) := α × S.subset

  namespace frac
    variable [Ring α] {S : MultiplicativeSet α} (f : frac S)

    protected def mk (r : α) ⦃s : α⦄ (hs : s ∈ S) : frac S := (r, ⟨s, hs⟩)

    def num : α := f.fst
    def denom : α := f.snd.val
    theorem denom_in_S : denom f ∈ S := f.snd.property

    protected def r (x y : frac S) : Prop := ∃ s ∈ S, s * x.num * y.denom = s * y.num * x.denom

    protected instance setoid (S : MultiplicativeSet α) : Setoid (frac S) where
      r     := frac.r
      iseqv := {
        refl  := fun _ => ⟨1, S.has_one, rfl⟩
        symm  := fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩
        trans := by--fun h₁ h₂ => by
          intro x y z ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
          have := congr (funext fun _ => h₁ ▸ rfl : (s₁ * x.num * y.denom * ·) = (s₁ * y.num * x.denom * ·)) h₂
          exact ⟨s₁ * y.num * y.denom * s₂, by sorry, by sorry⟩
      }

  end frac

  def localisation [Ring α] (S : MultiplicativeSet α) := Quotient (frac.setoid S)

  namespace localisation
    variable [Ring α] {S : MultiplicativeSet α}

    def of_frac : frac S → localisation S := Quotient.mk
    
    def of_frac' (r : α) {s : α} (hs : s ∈ S) : localisation S :=
      of_frac (frac.mk r hs)
    
    theorem equiv (S : MultiplicativeSet α) {x y : frac S} : of_frac x = of_frac y ↔
      ∃ s ∈ S, s * x.num * y.denom = s * y.num * x.denom :=
        ⟨Quotient.exact, @Quotient.sound (frac S) (frac.setoid S) x y⟩

    open NCSemiring Semiring Group NCRing

    protected def add : localisation S → localisation S → localisation S :=
      Function.Quotient.map₂ _ _ _ (frac.setoid S).refl (frac.setoid S).refl
        (fun x y => frac.mk (x.num * y.denom + y.num * x.denom) (S.mul_closed x.denom_in_S y.denom_in_S))
        fun a₁ a₂ b₁ b₂ ⟨sa, hsaS, hsae⟩ ⟨sb, hsbS, hsbe⟩ =>
          ⟨sa * sb, S.mul_closed hsaS hsbS, (by
            simp only [mul_distrib_left, mul_distrib_right, ←mul_assoc]
            rw [mul_right_comm sa, mul_right_comm _ _ a₂.denom, mul_right_comm _ _ a₂.denom, hsae,
              mul_right_comm, mul_right_comm _ a₁.denom, mul_right_comm _ a₁.denom, mul_right_comm sa]
            conv => lhs rhs rw [mul_right_comm, mul_right_comm _ _ b₂.denom, mul_assoc sa, mul_assoc sa, hsbe,
              ←mul_assoc, ←mul_assoc, mul_right_comm, mul_right_comm _ b₁.denom, mul_right_comm _ b₁.denom] :
            sa * sb * (a₁.num * b₁.denom + b₁.num * a₁.denom) * (a₂.denom * b₂.denom)
              = sa * sb * (a₂.num * b₂.denom + b₂.num * a₂.denom) * (a₁.denom * b₁.denom))⟩

    protected def neg : localisation S → localisation S :=
      Function.Quotient.map _ _ (fun f => frac.mk (-f.num) f.denom_in_S)
        fun a₁ a₂ ⟨s, hsS, hse⟩ => ⟨s, hsS, (by simp only [mul_neg, neg_mul, hse] :
          s * -a₁.num * a₂.denom = s * -a₂.num * a₁.denom)⟩

    protected def mul : localisation S → localisation S → localisation S :=
      Function.Quotient.map₂ _ _ _ (frac.setoid S).refl (frac.setoid S).refl
        (fun x y => frac.mk (x.num * y.num) (S.mul_closed x.denom_in_S y.denom_in_S))
        fun a₁ a₂ b₁ b₂ ⟨sa, hsaS, hsae⟩ ⟨sb, hsbS, hsbe⟩ =>
          ⟨sa * sb, S.mul_closed hsaS hsbS, (by
            simp only [←mul_assoc]; rw [mul_right_comm _ _ a₂.denom, mul_right_comm sa,
              mul_right_comm _ sb, hsae, mul_assoc, mul_assoc, ←mul_assoc sb, hsbe,
              ←mul_assoc, ←mul_assoc, mul_right_comm _ _ sb, mul_right_comm sa, mul_right_comm _ a₁.denom] : 
              sa * sb * (frac.num a₁ * frac.num b₁) * (frac.denom a₂ * frac.denom b₂) =
                sa * sb * (frac.num a₂ * frac.num b₂) * (frac.denom a₁ * frac.denom b₁))⟩

    protected instance ring : Ring (localisation S) := Ring.construct {
      zero := of_frac' 0 S.has_one
      one  := of_frac' 1 S.has_one
      add  := localisation.add
      neg  := localisation.neg
      mul  := localisation.mul
      add_zero := sorry
      add_assoc := sorry
      add_neg := sorry
      add_comm := sorry
      mul_one := sorry
      mul_assoc := sorry
      mul_distrib_left := sorry
      mul_comm := sorry
    }

  end localisation

end M4R
