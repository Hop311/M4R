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

    def QuotMul [Ring α] (I : Ideal α) : QClass I → QClass I → QClass I :=
      Function.Quotient.map₂ (QRel I) (QRel I) (QRel I)
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
      one  := toQuotient I 1
      add  := QuotAdd I
      neg  := QuotNeg I
      mul  := QuotMul I
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

    def natural_hom [Ring α] (I : Ideal α) : α →ᵣ QClass I where
      hom           := toQuotient I
      preserve_zero := rfl
      preserve_add  := fun _ _ => rfl
      preserve_neg  := fun _ => rfl
      preserve_one  := rfl
      preserve_mul  := fun _ _ => rfl
    
    theorem natural_hom.surjective [Ring α] (I : Ideal α) : Function.surjective (natural_hom I).hom :=
      @Quot.ind _ _ (fun x : QClass I => ∃ y, natural_hom I y = x) (fun y => ⟨y, rfl⟩)
    
    theorem natural_hom.kernel [Ring α] (I : Ideal α) {x : α} : natural_hom I x = 0 ↔ x ∈ I :=
      ⟨fun h => zero_add x ▸ neg_zero ▸ (QClass.equiv I 0 x).mp h.symm,
      fun hx => ((QClass.equiv I 0 x).mpr (neg_zero.symm ▸ (zero_add x).symm ▸ hx)).symm⟩

    open Ideal

    theorem quotient_extension_contraction [Ring α] {I J : Ideal α} (h : I ⊆ J) :
      contraction (QuotientRing.natural_hom I) (extension (QuotientRing.natural_hom I) J) = J :=
        Ideal.antisymm (fun x hx =>
          from_set.induction (fun y => ∀ x : α, QuotientRing.natural_hom I x = y → x ∈ J) hx
            (fun x hx => h ((natural_hom.kernel I).mp hx))
            (fun x ⟨z, hz, hzx⟩ y hyx => by
              rw [←zero_add y, ←add_neg z, add_assoc]
              exact J.add_closed hz (h ((QClass.equiv I z y).mp (hyx ▸ hzx : QuotientRing.natural_hom I z =
                QuotientRing.natural_hom I y))))
            (fun x y hx hy z hz => by
              let ⟨x', hx'⟩ := natural_hom.surjective I x
              let ⟨y', hy'⟩ := natural_hom.surjective I y
              rw [←hx', ←hy'] at hz
              have := J.add_closed (J.add_closed (hx x' hx') (hy y' hy')) (h ((QClass.equiv I (x' + y') z).mp hz.symm))
              rw [←add_assoc, add_neg, zero_add] at this
              exact this)
            (fun x y hy z hz => by
              let ⟨x', hx'⟩ := natural_hom.surjective I x
              let ⟨y', hy'⟩ := natural_hom.surjective I y
              rw [←hx', ←hy'] at hz
              have := J.add_closed (J.mul_closed x' (hy y' hy')) (h ((QClass.equiv I (x' * y') z).mp hz.symm))
              rw [←add_assoc, add_neg, zero_add] at this
              exact this) x rfl) (extension_contraction _ J)
  end QuotientRing
end M4R
