import M4R.Algebra.Ring.Ideal

namespace M4R
  open Monoid CommMonoid Group NCSemiring Semiring

  namespace QuotientRing

    def QRel [Ring α] (I : Ideal α) (a b : α) : Prop := -a + b ∈ I
    theorem QRel.refl [Ring α] (I : Ideal α) (a : α) : QRel I a a := by
      simp only [QRel]; rw [neg_add]; exact I.has_zero
    theorem QRel.symm [Ring α] (I : Ideal α) {a b : α} : QRel I a b → QRel I b a := by
      simp only [QRel]; intro h;
      rw [←neg_neg a, ←neg_add_distrib];
      exact I.neg_closed h
    theorem QRel.trans [Ring α] (I : Ideal α) {a b c : α} : QRel I a b → QRel I b c → QRel I a c := by
      simp only [QRel]; intro h₁ h₂;
      have := I.add_closed h₁ h₂
      rw [add_assoc, ←add_assoc b, add_neg, zero_add] at this;
      exact this

    instance QEquivalence [Ring α] (I : Ideal α) : Equivalence (QRel I) where
      refl  := QRel.refl I
      symm  := QRel.symm I
      trans := QRel.trans I

    instance QSetoid [Ring α] (I : Ideal α) : Setoid α where
      r := QRel I
      iseqv := QEquivalence I

    def QClass [Ring α] (I : Ideal α) : Type _ := Quotient (QSetoid I)

    def toQuotient [Ring α] (I : Ideal α) (a : α) : QClass I := @Quotient.mk α (QSetoid I) a

    theorem QClass.equiv [Ring α] (I : Ideal α) : ∀ a b : α, toQuotient I a = toQuotient I b ↔ -a + b ∈ I := fun a b =>
      ⟨@Quotient.exact α (QSetoid I) a b, @Quotient.sound α (QSetoid I) a b⟩

    def QuotAdd [Ring α] (I : Ideal α) : QClass I → QClass I → QClass I :=
      Function.Quotient.map₂ (QRel I) (QRel I) (QRel I)
        (QRel.refl I) (QRel.refl I) (· + ·) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp only [QRel] at *
          rw [neg_add_distrib, add_comm (-b₁), add_assoc, ←add_assoc (-b₁), add_comm (-b₁), add_assoc, ←add_assoc];
          exact I.add_closed ha hb)

    def QuotNeg [Ring α] (I : Ideal α) : QClass I → QClass I :=
      Function.Quotient.map (QRel I) (QRel I) (- ·)
        (fun x y hxy => by
          simp only [QRel] at *; rw [←neg_add_distrib, add_comm]; exact I.neg_closed hxy)

    def QuotMul [Ring α] (I : Ideal α) : QClass I → QClass I → QClass I := by
      apply Function.Quotient.map₂ (QRel I) (QRel I) (QRel I)
        (QRel.refl I) (QRel.refl I) (· * ·) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp only [QRel] at *
          have := I.add_closed (I.mul_closed b₁ ha) (I.mul_closed a₂ hb)
          rw [mul_distrib_left, mul_distrib_left, NCRing.mul_neg, mul_comm, mul_comm b₁, add_assoc, ←add_assoc (a₂ * b₁),
            NCRing.mul_neg, add_neg, zero_add] at this; exact this)
  end QuotientRing

  open QuotientRing

  instance QuotientRing {α : Type _} [Ring α] (I : Ideal α) : Ring (QClass I) := Ring.construct
    {
      zero := toQuotient I 0
      one := toQuotient I 1
      add := QuotAdd I
      neg := QuotNeg I
      mul := QuotMul I
      add_zero := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QRel]
        rw [add_zero, neg_add]; exact I.has_zero
      add_assoc := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QRel]
        rw [add_assoc, neg_add]; exact I.has_zero
      add_neg := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QRel]
        rw [add_neg, neg_add]; exact I.has_zero
      add_comm := by
        apply Function.Quotient.ind₂; intro a _; apply Quot.sound; simp only [QRel]
        rw [add_comm a, neg_add]; exact I.has_zero
      mul_one := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QRel]
        rw [mul_one, neg_add]; exact I.has_zero
      mul_assoc := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QRel]
        rw [mul_assoc, neg_add]; exact I.has_zero
      mul_distrib_left := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QRel]
        rw [mul_distrib_left, neg_add]; exact I.has_zero
      mul_comm := by
        apply Function.Quotient.ind₂; intros; apply Quot.sound; simp only [QRel]
        rw [mul_comm, neg_add]; exact I.has_zero
    }

  namespace QuotientRing

    theorem non_zero [Ring α] {I : Ideal α} {a : α} : toQuotient I a ≠ 0 ↔ a ∉ I :=
      ⟨by intro hI ha; apply hI; apply Quot.sound; simp only [Setoid.r, QRel]; rw [add_zero]; exact I.neg_closed ha,
      by
        intro ha hI; apply ha; have := @Quotient.exact α (QSetoid I) _ _ hI
        simp only [HasEquiv.Equiv, Setoid.r, QRel] at this; rw [add_zero] at this; rw [←neg_neg a]
        exact I.neg_closed this⟩

    theorem is_zero [Ring α] {I : Ideal α} {a : α} : toQuotient I a = 0 ↔ a ∈ I :=
      not_iff_not.mp non_zero

    theorem preserve_pow_nat [Ring α] (I : Ideal α) (a : α) (n : Nat) : (toQuotient I a) ^ n = toQuotient I (a ^ n) := by
      induction n with
      | zero      => rfl
      | succ n ih => rw [pow_nat_succ, pow_nat_succ, ih]; rfl

  end QuotientRing
end M4R
