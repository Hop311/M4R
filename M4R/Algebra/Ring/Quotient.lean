import M4R.Algebra.Ring.RMorphism
import M4R.Set

namespace M4R
  open Group
  open AbelianGroup
  open NCRing
  open Ring

  structure Ideal (α : Type _) [Ring α] where
    subset : Set α
    has_zero : 0 ∈ subset
    add_closed : ∀ {a b : α}, a ∈ subset → b ∈ subset → a + b ∈ subset
    mul_closed : ∀ (a : α) {b : α}, b ∈ subset → a * b ∈ subset

  namespace Ideal
    instance IdealMem [Ring α] : Mem α (Ideal α) where mem := fun x I => x ∈ I.subset

    theorem mul_closed' [Ring α] (I : Ideal α) : ∀ {a : α},  a ∈ I → (b : α) → a * b ∈ I := by
      intro a as b; rw [mul_comm]; exact I.mul_closed b as

    theorem neg_closed [Ring α] (I : Ideal α) : ∀ {a : α}, a ∈ I → -a ∈ I := by
      intro a as; rw [←mul_one a, ←mul_neg, mul_comm]; exact I.mul_closed (-1) as

    protected def image [Ring α] (I : Ideal α) (a : α) (p : a ∈ I) : ↑I.subset := ⟨a, p⟩
    protected theorem image_eq [Ring α] (I : Ideal α) (a b : ↑I.subset) :
      a = b ↔ Set.inclusion a = Set.inclusion b :=
        ⟨congrArg Set.inclusion, Set.elementExt⟩

    instance ZeroIdeal [Ring α] : Ideal α where
      subset := Set.SingletonSet.mk 0
      has_zero := rfl
      add_closed := by intro x y xz yz; rw [xz, yz, add_zero]; rfl
      mul_closed := by intro _ _ h; rw [h, mul_zero]; trivial
      
    instance UnitIdeal (α : Type _) [Ring α] : Ideal α where
      subset := Set.Universal
      has_zero := trivial
      add_closed := by intros; trivial
      mul_closed := by intros; trivial

    instance IdealAbelianGroup [r : Ring α] (I : Ideal α) : AbelianGroup ↑I.subset where
      zero := ⟨0, I.has_zero⟩
      add := fun ⟨x, xs⟩ ⟨y, ys⟩ => ⟨x + y, I.add_closed xs ys⟩
      neg := fun ⟨x, xs⟩ => ⟨-x, I.neg_closed xs⟩
      add_zero  := by intro ⟨a, _⟩; simp only [Ideal.image_eq]; exact r.add_zero a
      add_assoc := by intro ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩; simp only [Ideal.image_eq]; exact r.add_assoc a b c
      add_neg   := by intro ⟨a, _⟩; simp only [Ideal.image_eq]; exact r.add_neg a
      add_comm  := by intro ⟨a, _⟩ ⟨b, _⟩; simp only [Ideal.image_eq]; exact r.add_comm a b
    
    protected def equivalent [Ring α] (I J: Ideal α) : Prop := I.subset = J.subset
    protected theorem ext [Ring α] {I J : Ideal α} : Ideal.equivalent I J ↔ I = J := by
      match I, J with
      | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ =>
        apply Iff.intro;
        { intro eq; rw [Ideal.mk.injEq]; exact eq }
        { simp [Ideal.equivalent]; exact id }
    protected theorem antisymm [Ring α] {I J : Ideal α} (h₁ : I ⊆ J) (h₂ : J ⊆ I) : I = J := by
      rw [←Ideal.ext]; simp only [Ideal.equivalent]; rw [←Set.ext]; simp only [Set.equivalent];
      exact fun x => ⟨fun h => h₁ h, fun h => h₂ h⟩

    protected def add [Ring α] (I J : Ideal α) : Ideal α where
      subset := {x | ∃ i ∈ I, ∃ j ∈ J, i + j = x }
      has_zero := ⟨0, I.has_zero, 0, J.has_zero, show 0 + 0 = 0 by rw [add_zero 0]⟩
      add_closed := fun ⟨ia, hia, ja, hja, hija⟩ ⟨ib, hib, jb, hjb, hijb⟩ =>
        ⟨
          ia + ib, I.add_closed hia hib,
          ja + jb, J.add_closed hja hjb,
          by rw [add_assoc, add_comm ib, add_assoc, add_comm jb, ←add_assoc, hija, hijb]
        ⟩
      mul_closed := fun a b ⟨i, hi, j, hj, hij⟩ =>
        ⟨
          a*i, I.mul_closed a hi,
          a*j, J.mul_closed a hj,
          by rw [←mul_distrib_left, hij]
        ⟩
    instance IdealAdd [Ring α] : Add (Ideal α) where add := Ideal.add

    protected theorem add.comm [Ring α] (I J : Ideal α) : I + J = J + I :=
      have : ∀ {K L : Ideal α}, K + L ⊆ L + K := by
        intro K L x ⟨i, hi, j, hj, hij⟩;
        exact ⟨j, hj, i, hi, by rw [add_comm]; exact hij⟩
      Ideal.antisymm this this

    protected theorem add.subset [Ring α] (I J : Ideal α) : I ⊆ I + J :=
      fun x hx => ⟨x, hx, 0, J.has_zero, add_zero x⟩
    protected theorem add.of_subset [Ring α] {I J : Ideal α} (h : I ⊆ J) : I + J = J := by
      apply Ideal.antisymm
      intro x ⟨i, iI, j, jJ, hij⟩; rw [←hij]; exact J.add_closed (h iI) jJ
      rw [Ideal.add.comm]; exact Ideal.add.subset J I

    def coprime [Ring α] (I J : Ideal α) : Prop := I + J = UnitIdeal α

    def principal [r : Ring α] (a : α) : Ideal α where
      subset := {x | a ÷ x}
      has_zero := divides_zero a;
      add_closed := divides_add
      mul_closed := fun x => divides_mul' x

    def is_principal [Ring α] (I : Ideal α) : Prop :=
      ∃ a, a ∈ I ∧ ∀ x, x ∈ I → a ÷ x

    def proper_ideal [Ring α] (I : Ideal α) : Prop :=
      I ≠ UnitIdeal α

    def is_prime [Ring α] (I : Ideal α) : Prop :=
      I.proper_ideal ∧ ∀ r s, r * s ∈ I → r ∈ I ∨ s ∈ I

    def is_maximal [Ring α] (I : Ideal α) : Prop :=
      I.proper_ideal ∧ ∀ {J : Ideal α}, I ⊆ J → J = I ∨ J = UnitIdeal α

    theorem maximal_neq [Ring α] {I : Ideal α} (h : I.is_maximal) : ∀ {J : Ideal α}, I ⊊ J → J = UnitIdeal α := by
      intro J ⟨hIJ, x, hxI, hxJ⟩;
      apply (h.right hIJ).resolve_left fun heq => by rw [heq] at hxJ; exact hxI hxJ

    theorem generator_in_principal [Ring α] (a : α) : a ∈ principal a := ⟨1, mul_one a⟩
    theorem principal_principal [Ring α] (a : α) : is_principal (principal a) :=
      ⟨a, ⟨divides_self a, by intro _ h; exact h⟩⟩

    theorem principal_of_is_principal [Ring α] (I : Ideal α) (h : is_principal I) : ∃ a, I = principal a := by
      let ⟨a, ⟨aI, ha⟩⟩ := h;
      exact ⟨a, by apply Ideal.ext.mp; apply Set.subset.antisymm ha;
                    intro x xp; let ⟨b, ab⟩ := xp; rw [←ab]; exact I.mul_closed' aI b⟩

    theorem in_unit_ideal [Ring α] : ∀ I : Ideal α, I ⊆ UnitIdeal α := by
      intro; simp only [Subset.subset]; intros; trivial
    theorem principal_in [Ring α] (I : Ideal α) : ∀ a ∈ I, principal a ⊆ I := by
      intro _ aI _ ⟨y, ayx⟩; rw [←ayx]; exact mul_closed' _ aI _;
    theorem unit_principal [Ring α] : ∀ u, isUnit u → (principal u) = UnitIdeal α := by
      intro u hu; exact Ideal.antisymm (in_unit_ideal _) (fun y _ => unit_divides u y hu);

    theorem is_unit_ideal [Ring α] {I : Ideal α} : I = UnitIdeal α ↔ 1 ∈ I := by
      apply Iff.intro (fun h => by rw [h]; trivial); intro h;
      exact Ideal.antisymm (in_unit_ideal I) (by rw [←unit_principal (1 : α) isUnit_1]; exact principal_in I 1 h);

    def ideal_chain [Ring α] (S : Set (Ideal α)) (hS : Nonempty S) (hc : Zorn.Chain Subset.subset S) : Ideal α where
      subset := ⋃₀ (Set.toSetSet S Ideal.subset)
      has_zero :=
        let ⟨⟨x, xS⟩, _⟩ := Classical.exists_true_of_nonempty hS
        ⟨x.subset, ⟨x, xS, rfl⟩, x.has_zero⟩
      add_closed := by
        intro a b ⟨i, ⟨I, IS, Ii⟩, ai⟩ ⟨j, ⟨J, JS, Jj⟩, bj⟩
        cases Classical.em (I = J) with
        | inl h =>
          rw [←Ii] at ai; rw [←h] at Jj; rw [←Jj] at bj
          exact ⟨I.subset, ⟨I, IS, rfl⟩, I.add_closed ai bj⟩
        | inr h =>
          cases hc I IS J JS h with
          | inl h =>
            rw [←Ii] at ai; rw [←Jj] at bj
            exact ⟨J.subset, ⟨J, JS, rfl⟩, J.add_closed (h ai) bj⟩
          | inr h =>
            rw [←Ii] at ai; rw [←Jj] at bj
            exact ⟨I.subset, ⟨I, IS, rfl⟩, I.add_closed ai (h bj)⟩
      mul_closed := by
        intro a b ⟨i, ⟨I, IS, Ii⟩, bi⟩
        rw [←Ii] at bi
        exact ⟨I.subset, ⟨I, IS, rfl⟩, I.mul_closed a bi⟩

    theorem ideal_chain_subset [Ring α] (S : Set (Ideal α)) {I : Ideal α} (IS : I ∈ S)
      (hc : Zorn.Chain Subset.subset S) : I ⊆ ideal_chain S ⟨I, IS⟩ hc :=
        fun x xI => ⟨I.subset, ⟨I, IS, rfl⟩, xI⟩

    theorem ideal_chain_proper [Ring α] (S : Set (Ideal α)) (hS : Nonempty S) (hc : Zorn.Chain Subset.subset S) :
      (∀ I ∈ S, I.proper_ideal) → (ideal_chain S hS hc).proper_ideal := by
        intro h hU;
        let ⟨_, ⟨I, IS, hI⟩, hIu⟩ := is_unit_ideal.mp hU;
        rw [←hI] at hIu;
        exact absurd (is_unit_ideal.mpr hIu) (h I IS)

    theorem ideal_chain_disjoint [Ring α] (S : Set (Ideal α)) (hS : Nonempty S) (hc : Zorn.Chain Subset.subset S) (S' : Set α) :
      (∀ I ∈ S, Set.disjoint I.subset S') → (Set.disjoint (ideal_chain S hS hc).subset S') := by
        intro h
        apply Set.disjoint.elementwise.mpr
        intro x ⟨y, ⟨J, JS, hJy⟩, xy⟩; rw [←hJy] at xy
        exact Set.disjoint.elementwise.mp (h J JS) x xy

  end Ideal

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

    def QuotAdd [Ring α] (I : Ideal α) : QClass I → QClass I → QClass I :=
      Function.Quotient.map₂ (QRel I) (QRel I) (QRel I)
        (QRel.refl I) (QRel.refl I) (fun x y => x + y) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp only [QRel] at *
          rw [neg_add_distrib, add_comm (-b₁), add_assoc, ←add_assoc (-b₁), add_comm (-b₁), add_assoc, ←add_assoc];
          exact I.add_closed ha hb)

    def QuotNeg [Ring α] (I : Ideal α) : QClass I → QClass I :=
      Function.Quotient.map (QRel I) (QRel I) (fun x => -x)
        (fun x y hxy => by
          simp only [QRel] at *; rw [←neg_add_distrib, add_comm]; exact I.neg_closed hxy)

    def QuotMul [Ring α] (I : Ideal α) : QClass I → QClass I → QClass I := by
      apply Function.Quotient.map₂ (QRel I) (QRel I) (QRel I)
        (QRel.refl I) (QRel.refl I) (fun x y => x * y) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp only [QRel] at *
          have := I.add_closed (I.mul_closed b₁ ha) (I.mul_closed a₂ hb)
          rw [mul_distrib_left, mul_distrib_left, mul_neg, mul_comm, mul_comm b₁, add_assoc, ←add_assoc (a₂ * b₁),
            mul_neg, add_neg, zero_add] at this; exact this)

    instance QuotientRing {α : Type _} [Ring α] (I : Ideal α) : Ring (QClass I) where
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
      one_mul := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QRel]
        rw [one_mul, neg_add]; exact I.has_zero
      mul_assoc := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QRel]
        rw [mul_assoc, neg_add]; exact I.has_zero
      mul_distrib_left := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QRel]
        rw [mul_distrib_left, neg_add]; exact I.has_zero
      mul_distrib_right := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QRel]
        rw [mul_distrib_right, neg_add]; exact I.has_zero
      mul_comm := by
        apply Function.Quotient.ind₂; intros; apply Quot.sound; simp only [QRel]
        rw [mul_comm, neg_add]; exact I.has_zero

    theorem non_zero [Ring α] {I : Ideal α} {a : α} : toQuotient I a ≠ 0 ↔ a ∉ I :=
      ⟨by intro hI ha; apply hI; apply Quot.sound; simp only [Setoid.r, QRel]; rw [add_zero]; exact I.neg_closed ha,
      by
        intro ha hI; apply ha; have := @Quotient.exact α (QSetoid I) _ _ hI
        simp only [HasEquiv.Equiv, Setoid.r, QRel] at this; rw [add_zero] at this; rw [←neg_neg a]
        exact I.neg_closed this⟩

  end QuotientRing

  namespace Ideal
    open QuotientRing

    instance ProperIdealNonTrivialRing [Ring α] {I : Ideal α} (hI : I.proper_ideal) : NonTrivialRing (QClass I) where
      one_neq_zero := by
        intro h10;
        have := @Quotient.exact α (QSetoid I) 0 1 h10.symm;
        simp only [HasEquiv.Equiv, Setoid.r, QRel] at this
        rw [neg_zero, zero_add] at this
        exact hI (Ideal.is_unit_ideal.mpr this)

    theorem NonTrivialRingProperIdeal [Ring α] {I : Ideal α} (h : is_NonTrivial (QClass I)) : I.proper_ideal := by
      intro hu;
      have : (1 : QClass I) = (0 : QClass I) := by
        apply Eq.symm; apply Quot.sound; simp only [Setoid.r, QRel]
        rw [neg_zero, zero_add]; exact Ideal.is_unit_ideal.mp hu
      exact h this

    theorem maximal_has_inverses [Ring α] {I : Ideal α} (hI : I.is_maximal) :
      ∀ {a : α}, toQuotient I a ≠ 0 → ∃ r : α, (toQuotient I a) * (toQuotient I r) = 1 := by
        intro a ha;
        have : I ⊊ I + (principal a) :=
          ⟨Ideal.add.subset I (principal a), a, non_zero.mp ha, 0, I.has_zero, a, ⟨1, mul_one a⟩, zero_add a⟩
        have ⟨i, hi, j, ⟨r, hj⟩, hij⟩ :=
          is_unit_ideal.mp (maximal_neq hI this)
        exact ⟨r, Quot.sound (by
            simp only [QRel]
            rw [hj, add_comm, ←sub_right.mp hij]
            exact hi)⟩
    theorem maximal_has_inverses' [Ring α] {I : Ideal α} (hI : I.is_maximal) :
      ∀ {a : QClass I}, a ≠ 0 → ∃ r : QClass I, a * r = 1 :=
        @Quotient.ind α (QSetoid I) (fun (a : QClass I) => a ≠ 0 → ∃ r : QClass I, a * r = 1) (fun _ ha =>
          have ⟨r, hr⟩ := maximal_has_inverses hI ha
          ⟨toQuotient I r, hr⟩)
    noncomputable def maximal_inv [Ring α] {I : Ideal α} (hI : I.is_maximal) : {a : QClass I} → a ≠ 0 → QClass I :=
      fun ha => Classical.choose (maximal_has_inverses' hI ha)

    noncomputable instance MaximalField [Ring α] {I : Ideal α} (hI : I.is_maximal) : Field (QClass I) where
      one_neq_zero := (ProperIdealNonTrivialRing hI.left).one_neq_zero
      mul_comm := by
        apply Function.Quotient.ind₂; intros; apply Quot.sound; simp only [QRel]
        rw [mul_comm, neg_add]; exact I.has_zero
      inv := maximal_inv hI
      mul_inv := fun ha => Classical.choose_spec (maximal_has_inverses' hI ha)
      inv_mul := fun ha => by
        rw [mul_comm];
        exact Classical.choose_spec (maximal_has_inverses' hI ha)

    theorem FieldMaximal [Ring α] {I : Ideal α} (h : is_Field (QClass I)) : I.is_maximal := by
      simp only [is_maximal, is_Field] at *
      exact ⟨NonTrivialRingProperIdeal h.left, by
        intro J hIJ;
        cases Classical.em (I = J) with
        | inl heq => exact Or.inl heq.symm 
        | inr hneq =>
          apply Or.inr; apply is_unit_ideal.mpr;
          let ⟨x, xJ, nxI⟩ := Classical.choice (Set.minus.nonempty 
            (Set.subset.neq_proper hIJ (by intro h'; exact hneq (Ideal.ext.mp h'))))
          let ⟨b, hb⟩ := h.right (non_zero.mpr nxI)
          exact @Quotient.ind α (QSetoid I) (fun (c : QClass I) => c = b → 1 ∈ J) (fun b' hb' => by
            rw [←hb'] at hb;
            have := @Quotient.exact α (QSetoid I) _ _ hb
            simp only [HasEquiv.Equiv, Setoid.r, QRel] at this
            have := J.add_closed (J.mul_closed b' xJ) (hIJ this)
            rw [mul_comm, ←add_assoc, add_neg, zero_add] at this
            exact this) b rfl⟩

    instance PrimeIntegralDomain [Ring α] {I : Ideal α} (hI : I.is_prime) : IntegralDomain (QClass I) where
      one_neq_zero := (ProperIdealNonTrivialRing hI.left).one_neq_zero
      mul_comm := by
        apply Function.Quotient.ind₂; intro a b
        apply Quot.sound; simp [QRel]
        rw [mul_comm, neg_add]
        exact I.has_zero
      integral := @Function.Quotient.ind₂ α α (QRel I) (QRel I)
          (fun (a b : QClass I) => a ≠ 0 → b ≠ 0 → a * b ≠ 0)
          (fun a b ha hb => non_zero.mpr fun hab =>
            Or.elim (hI.right a b hab) (non_zero.mp ha) (non_zero.mp hb))

    theorem IntegralDomainPrime [Ring α] {I : Ideal α} (h : is_IntegralDomain (QClass I)) : I.is_prime :=
      ⟨NonTrivialRingProperIdeal h.left, by
        simp [is_IntegralDomain] at h
        intro r s hrs
        apply Classical.byContradiction
        intro h'
        simp only [not_or_iff_and_not] at h'
        exact non_zero.mp (h.right (non_zero.mpr h'.left) (non_zero.mpr h'.right)) hrs⟩

    theorem maximal_is_prime [Ring α] {I : Ideal α} (h : I.is_maximal) : I.is_prime :=
      IntegralDomainPrime (MaximalField h).to_is_IntegralDomain

  end Ideal
end M4R