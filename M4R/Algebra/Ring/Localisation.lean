import M4R.Algebra.Ring.Ideal

namespace M4R
  open NCRing Semiring NCSemiring Group CommMonoid Monoid

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

    protected abbrev mk (r : α) ⦃s : α⦄ (hs : s ∈ S) : frac S := (r, ⟨s, hs⟩)

    abbrev num : α := f.fst
    abbrev denom : α := f.snd.val
    abbrev num_eq (r : α) {s : α} (hs : s ∈ S) : (frac.mk r hs).num = r := rfl
    abbrev denom_eq (r : α) {s : α} (hs : s ∈ S) : (frac.mk r hs).denom = s := rfl
    theorem denom_in_S : denom f ∈ S := f.snd.property

    theorem ext : ∀ {x y : frac S},  x = y ↔ x.num = y.num ∧ x.denom = y.denom
    | (x₁, x₂), (y₁, y₂) =>
      ⟨fun h => have ⟨h₁, h₂⟩ := Prod.mk.inj h; ⟨h₁, congrArg Subtype.val h₂⟩,
       fun ⟨h₁, h₂⟩ => Prod.mk.injEq x₁ x₂ y₁ y₂ ▸ ⟨h₁, Set.elementExt h₂⟩⟩

    protected def r (x y : frac S) : Prop := ∃ s ∈ S, s * x.num * y.denom = s * y.num * x.denom

    protected instance setoid (S : MultiplicativeSet α) : Setoid (frac S) where
      r     := frac.r
      iseqv := {
        refl  := fun _ => ⟨1, S.has_one, rfl⟩
        symm  := fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩
        trans := by
          intro x y z ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
          exact ⟨s₁ * s₂ * y.denom, S.mul_closed (S.mul_closed hs₁ hs₂) y.denom_in_S, by
            rw [mul_right_comm s₁, mul_right_comm _ s₂, mul_right_comm s₁, h₁]
            conv => rhs rw [mul_right_comm s₁, mul_right_comm _ y.denom, mul_assoc _ z.num,
              mul_assoc s₁, ←mul_assoc s₂, ←h₂, mul_right_comm s₂, ←mul_assoc, mul_right_comm s₁,
              mul_right_comm _ _ x.denom, ←mul_assoc]⟩
      }

  end frac

  def localisation [Ring α] (S : MultiplicativeSet α) := Quotient (frac.setoid S)

  namespace localisation
    variable [Ring α] {S : MultiplicativeSet α}

    def of_frac : frac S → localisation S := Quotient.mk

    abbrev of_frac' (r : α) {s : α} (hs : s ∈ S) : localisation S :=
      of_frac (frac.mk r hs)

    protected theorem frac_def (x : frac S) : Quot.mk Setoid.r x = of_frac x := rfl

    theorem equiv (S : MultiplicativeSet α) {x y : frac S} : of_frac x = of_frac y ↔
      ∃ s ∈ S, s * x.num * y.denom = s * y.num * x.denom :=
        ⟨Quotient.exact, @Quotient.sound (frac S) (frac.setoid S) x y⟩

    protected instance zero_inst : Zero (localisation S) where zero := of_frac' 0 S.has_one
    protected theorem zero_def : (0 : localisation S) = of_frac' 0 S.has_one := rfl
    protected instance one_inst : One (localisation S) where one := of_frac' 1 S.has_one
    protected theorem one_def : (1 : localisation S) = of_frac' 1 S.has_one := rfl

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
    protected instance add_inst : Add (localisation S) where add := localisation.add
    protected theorem add_def (x y : frac S) : of_frac x + of_frac y =
      of_frac' (x.num * y.denom + y.num * x.denom) (S.mul_closed x.denom_in_S y.denom_in_S) := rfl

    protected def neg : localisation S → localisation S :=
      Function.Quotient.map _ _ (fun f => frac.mk (-f.num) f.denom_in_S)
        fun a₁ a₂ ⟨s, hsS, hse⟩ => ⟨s, hsS, (by simp only [mul_neg, neg_mul, hse] :
          s * -a₁.num * a₂.denom = s * -a₂.num * a₁.denom)⟩
    protected instance neg_inst : Neg (localisation S) where neg := localisation.neg
    protected theorem neg_def (x : frac S) : - of_frac x = of_frac' (-x.num) x.denom_in_S := rfl

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
    protected instance mul_inst : Mul (localisation S) where mul := localisation.mul
    protected theorem mul_def (x y : frac S) : of_frac x * of_frac y =
      of_frac' (x.num * y.num) (S.mul_closed x.denom_in_S y.denom_in_S) := rfl

    protected instance ring : Ring (localisation S) := Ring.construct {
      add_zero := Quot.ind fun _ => Quot.sound ⟨1, S.has_one, by
        simp only [frac.denom_eq, mul_one, zero_mul, add_zero]⟩
      add_assoc := Function.Quotient.ind₃ _ _ _ fun x y z => Quot.sound ⟨1, S.has_one, by
        simp only [one_mul, mul_distrib_left, mul_distrib_right, ←mul_assoc, ←add_assoc]
        conv => rhs rw [mul_right_comm y.num, mul_right_comm z.num]⟩
      add_neg := Quot.ind fun _ => Quot.sound ⟨1, S.has_one, by
        simp only [one_mul, mul_one, zero_mul, ←mul_distrib_right, Group.add_neg]⟩
      add_comm := Quotient.ind₂ fun x y => Quot.sound ⟨1, S.has_one, by
        simp only [frac.num_eq, frac.denom_eq]; rw [add_comm, mul_comm y.denom]⟩
      mul_one := Quot.ind fun _ => Quot.sound ⟨1, S.has_one, by
        simp only [frac.denom_eq, mul_one]⟩
      mul_assoc := Function.Quotient.ind₃ _ _ _ fun _ _ _ => Quot.sound ⟨1, S.has_one, by
        simp only [←mul_assoc]⟩
      mul_distrib_left := Function.Quotient.ind₃ _ _ _ fun x y z => Quot.sound ⟨1, S.has_one, by
        simp only [frac.num_eq, frac.denom_eq, one_mul]; rw [mul_distrib_left]
        conv => rhs rw [mul_comm x.denom, mul_comm x.denom, mul_left_comm x.denom,
          ←mul_assoc _ _ x.denom, ←mul_assoc _ _ x.denom, ←mul_distrib_right]
        simp only [←mul_assoc]⟩
      mul_comm := Quotient.ind₂ fun x y => Quot.sound ⟨1, S.has_one, by
        simp only [frac.num_eq, frac.denom_eq]; rw [mul_comm y.num, mul_comm y.denom]⟩
    }

  end localisation

end M4R
