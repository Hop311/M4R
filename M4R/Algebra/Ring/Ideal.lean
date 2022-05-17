import M4R.Algebra.Ring.Prod

namespace M4R
  open Monoid CommMonoid NCSemiring Semiring NCRing Group

  structure Ideal (α : Type _) [Ring α] where
    subset     : Set α
    has_zero   : 0 ∈ subset
    add_closed : ∀ {a b : α}, a ∈ subset → b ∈ subset → a + b ∈ subset
    mul_closed : ∀ (a : α) {b : α}, b ∈ subset → a * b ∈ subset

  namespace Ideal
    instance IdealMem [Ring α] : Mem α (Ideal α) where mem := fun x I => x ∈ I.subset

    theorem mul_closed' [Ring α] (I : Ideal α) : ∀ {a : α},  a ∈ I → (b : α) → a * b ∈ I := by
      intro a as b; rw [mul_comm]; exact I.mul_closed b as

    theorem neg_closed [Ring α] (I : Ideal α) : ∀ {a : α}, a ∈ I → -a ∈ I := by
      intro a as; rw [←mul_one a, ←mul_neg, mul_comm]; exact I.mul_closed (-1) as

    theorem sub_closed [Ring α] (I : Ideal α) : ∀ {a b : α}, a ∈ I → b ∈ I → a - b ∈ I :=
      fun as bs => sub_def _ _ ▸ I.add_closed as (I.neg_closed bs)

    protected def image [Ring α] (I : Ideal α) (a : α) (p : a ∈ I) : ↑I.subset := ⟨a, p⟩
    protected theorem image_eq [Ring α] (I : Ideal α) (a b : ↑I.subset) :
      a = b ↔ Set.inclusion a = Set.inclusion b :=
        ⟨congrArg Set.inclusion, Set.elementExt⟩

    def ZeroIdeal (α : Type _) [Ring α] : Ideal α where
      subset     := Set.singleton 0
      has_zero   := rfl
      add_closed := fun xz yz => by rw [xz, yz, add_zero]; rfl
      mul_closed := fun _ _ h => by rw [h, mul_zero]; trivial

    def UnitIdeal (α : Type _) [Ring α] : Ideal α where
      subset     := Set.Universal
      has_zero   := trivial
      add_closed := by intros; trivial
      mul_closed := by intros; trivial

    instance ZeroIdeal.Zero [Ring α] : Zero (Ideal α) where zero := ZeroIdeal α
    instance UnitIdeal.One [Ring α] : One (Ideal α) where one := UnitIdeal α

    instance IdealAbelianGroup [r : Ring α] (I : Ideal α) : AbelianGroup ↑I.subset := AbelianGroup.construct
      {
        zero      := ⟨0, I.has_zero⟩
        add       := fun ⟨x, xs⟩ ⟨y, ys⟩ => ⟨x + y, I.add_closed xs ys⟩
        neg       := fun ⟨x, xs⟩ => ⟨-x, I.neg_closed xs⟩
        add_zero  := fun ⟨a, _⟩ => by simp only [Ideal.image_eq]; exact r.add_zero a
        add_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => by simp only [Ideal.image_eq]; exact r.add_assoc a b c
        add_neg   := fun ⟨a, _⟩ => by simp only [Ideal.image_eq]; exact r.add_neg a
        add_comm  := fun ⟨a, _⟩ ⟨b, _⟩ => by simp only [Ideal.image_eq]; exact r.add_comm a b
      }

    def RHomomorphism.kernel_ideal [Ring α] [Ring β] (f : α →ᵣ β) : Ideal α where
      subset     := f.kernel.subset
      has_zero   := f.preserve_zero
      add_closed := fun ha hb => (by rw [f.preserve_add, ha, hb, add_zero] : _ = (0 : β))
      mul_closed := fun _ _ hb => (by rw [f.preserve_mul, hb, mul_zero] : _ = (0 : β))

    protected def equivalent [Ring α] (I J: Ideal α) : Prop := I.subset = J.subset
    protected theorem ext [Ring α] : ∀ {I J : Ideal α}, Ideal.equivalent I J ↔ I = J
    | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ =>
      ⟨by intro eq; rw [Ideal.mk.injEq]; exact eq, by simp [Ideal.equivalent]; exact id⟩
    protected theorem ext' [Ring α] {I J : Ideal α} : I = J ↔ ∀ x, x ∈ I ↔ x ∈ J := by
      simp only [←Ideal.ext, Ideal.equivalent, ←Set.ext]; exact Iff.rfl
    protected theorem antisymm [Ring α] {I J : Ideal α} (h₁ : I ⊆ J) (h₂ : J ⊆ I) : I = J := by
      rw [←Ideal.ext]; simp only [Ideal.equivalent]; rw [←Set.ext]; simp only [Set.equivalent];
      exact fun x => ⟨fun h => h₁ h, fun h => h₂ h⟩
    protected theorem subsetneq [Ring α] {I J : Ideal α} : I ⊊ J ↔ I ⊆ J ∧ I ≠ J :=
      ⟨(And.imp_right (fun h₁ h₂ => let ⟨x, hxI, hxJ⟩ := h₁
        absurd ((Ideal.ext'.mp h₂ x).mpr hxJ) hxI) ·),
      fun ⟨h₁, h₂⟩ => ⟨h₁, Classical.byContradiction fun h => by
        simp only [not_exists, not_and] at h
        exact h₂ (Ideal.ext'.mpr fun x => ⟨(h₁ ·), fun hx => of_not_not (mt (h x) (iff_not_not.mpr hx))⟩)⟩⟩

    protected def add [Ring α] (I J : Ideal α) : Ideal α where
      subset     := {x | ∃ i ∈ I, ∃ j ∈ J, i + j = x }
      has_zero   := ⟨0, I.has_zero, 0, J.has_zero, by rw [add_zero 0]⟩
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

    namespace add

      protected theorem comm [Ring α] (I J : Ideal α) : I + J = J + I :=
        have : ∀ {K L : Ideal α}, K + L ⊆ L + K := by
          intro K L x ⟨i, hi, j, hj, hij⟩;
          exact ⟨j, hj, i, hi, by rw [add_comm]; exact hij⟩
        Ideal.antisymm this this

      protected theorem subset [Ring α] (I J : Ideal α) : I ⊆ I + J :=
        fun x hx => ⟨x, hx, 0, J.has_zero, add_zero x⟩

      protected theorem subset' [Ring α] (I J : Ideal α) : J ⊆ I + J :=
        add.comm I J ▸ add.subset J I

      protected theorem add_self [Ring α] (I : Ideal α) : I + I = I :=
        Ideal.antisymm (fun x ⟨i, hi, j, hj, hij⟩ => hij ▸ I.add_closed hi hj) (add.subset I I)

      protected theorem subset_add_subset [Ring α] {I₁ J₁ I₂ J₂ : Ideal α} (hI : I₁ ⊆ I₂) (hJ : J₁ ⊆ J₂) :
        I₁ + J₁ ⊆ I₂ + J₂ := fun x ⟨i, hi, j, hj, hij⟩ => ⟨i, hI hi, j, hJ hj, hij⟩

      protected theorem subset_add [Ring α] {I J K : Ideal α} (hI : I ⊆ K) (hJ : J ⊆ K) : I + J ⊆ K :=
        add.add_self K ▸ add.subset_add_subset hI hJ

      protected theorem of_subset [Ring α] {I J : Ideal α} (h : J ⊆ I) : I + J = I := by
        apply Ideal.antisymm
        intro x ⟨i, iI, j, jJ, hij⟩; rw [←hij]; exact I.add_closed iI (h jJ)
        exact Ideal.add.subset I J

      protected theorem of_subset' [Ring α] {I J : Ideal α} (h : I ⊆ J) : I + J = J :=
        add.comm I J ▸ add.of_subset h

      protected theorem mem [Ring α] (I J : Ideal α) : ∀ a, a ∈ I + J ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = a :=
        fun _ => Iff.rfl

      protected theorem assoc [Ring α] (I J K : Ideal α) : I + J + K = I + (J + K) := by
        apply Ideal.antisymm
        { intro x ⟨y, ⟨i, hi, j, hj, hijy⟩, k, hk, hykx⟩;
          exact ⟨i, hi, j + k, ⟨j, hj, k, hk, rfl⟩, add_assoc i j k ▸ hijy ▸ hykx⟩ }
        { intro x ⟨i, hi, y, ⟨j, hj, k, hk, hjky⟩, hiyx⟩;
          exact ⟨i + j, ⟨i, hi, j, hj, rfl⟩, k, hk, add_assoc i j k ▸ hjky ▸ hiyx⟩ }

    end add

    def coprime [Ring α] (I J : Ideal α) : Prop := I + J = 1

    open Ring

    def principal [r : Ring α] (a : α) : Ideal α where
      subset     := {x | a ÷ x}
      has_zero   := divides_zero a;
      add_closed := divides_add
      mul_closed := fun x => divides_mul' x

    def is_principal [Ring α] (I : Ideal α) : Prop :=
      ∃ a, a ∈ I ∧ ∀ x, x ∈ I → a ÷ x

    def proper_ideal [Ring α] (I : Ideal α) : Prop := I ≠ 1

    theorem generator_in_principal [Ring α] (a : α) : a ∈ principal a := ⟨1, mul_one a⟩
    theorem principal_principal [Ring α] (a : α) : is_principal (principal a) :=
      ⟨a, ⟨divides_self a, fun _ => id⟩⟩

    theorem principal_of_is_principal [Ring α] (I : Ideal α) (h : is_principal I) : ∃ a, I = principal a := by
      let ⟨a, ⟨aI, ha⟩⟩ := h;
      exact ⟨a, by apply Ideal.ext.mp; apply Set.subset.antisymm ha;
                    intro x xp; let ⟨b, ab⟩ := xp; rw [←ab]; exact I.mul_closed' aI b⟩

    theorem mem_unit_ideal [Ring α] (a : α) : a ∈ (1 : Ideal α) := trivial
    theorem mem_zero_ideal [Ring α] {a : α} : a ∈ (0 : Ideal α) ↔ a = 0 := Iff.rfl
    theorem one_notin_zero_ideal [R : NonTrivialRing α] : 1 ∉ (0 : Ideal α) :=
      (absurd · R.toNonTrivial.one_neq_zero)

    theorem in_unit_ideal [Ring α] (I : Ideal α) : I ⊆ 1 :=
      fun x _ => mem_unit_ideal x
    theorem unit_ideal_in [Ring α] {I : Ideal α} (hI : 1 ⊆ I) : I = 1 :=
      Ideal.antisymm (in_unit_ideal I) hI

    theorem zero_ideal_in [Ring α] (I : Ideal α) : 0 ⊆ I := fun x hx =>
      mem_zero_ideal.mp hx ▸ I.has_zero
    theorem in_zero_ideal [Ring α] {I : Ideal α} (hI : I ⊆ 0) : I = 0 :=
      Ideal.antisymm hI (zero_ideal_in I)

    theorem principal_in [Ring α] {I : Ideal α} {a : α} (ha : a ∈ I) : principal a ⊆ I := by
      intro _ ⟨y, ayx⟩; rw [←ayx]; exact mul_closed' _ ha _;
    theorem unit_principal [Ring α] {u : α} (hu : isUnit u) : principal u = 1 :=
      Ideal.antisymm (in_unit_ideal _) (fun y _ => unit_divides u y hu)
    theorem unit_not_principal [Ring α] {u : α} (hu : ¬isUnit u) : (principal u).proper_ideal :=
      fun h => absurd (by rw [h]; trivial : 1 ∈ principal u) hu
    theorem zero_principal (α : Type _) [Ring α] : principal (0 : α) = 0 :=
      in_zero_ideal fun x ⟨y, hy⟩ => (zero_mul y ▸ hy.symm : x = 0)

    theorem is_unit_ideal' [Ring α] {I : Ideal α} : I = 1 ↔ ∃ x, isUnit x ∧ x ∈ I :=
      ⟨(· ▸ ⟨1, isUnit_1, trivial⟩), fun ⟨x, hx, hxI⟩ =>
        Ideal.antisymm (in_unit_ideal I) (unit_principal hx ▸ principal_in hxI)⟩
    theorem is_unit_ideal [Ring α] {I : Ideal α} : I = 1 ↔ 1 ∈ I :=
      is_unit_ideal'.trans ⟨fun ⟨x, ⟨y, hxy⟩, hxI⟩ => hxy ▸ I.mul_closed' hxI y, fun h => ⟨1, isUnit_1, h⟩⟩
    theorem is_zero_ideal [Ring α] {I : Ideal α} : I = 0 ↔ ∀ a ∈ I, a = 0 := by
      simp only [←Ideal.ext, Ideal.equivalent, ←Set.ext, Set.equivalent];
      exact propext_iff.mpr (forall_congr fun _ => propext ⟨Iff.mp, fun h => ⟨h, (· ▸ I.has_zero)⟩⟩)

    theorem div_mem [Ring α] {I : Ideal α} {a : α} : a ∈ I ↔ ∃ b ∈ I, b ÷ a :=
      ⟨fun h => ⟨a, h, divides_self a⟩, fun ⟨b, hb, c, hbc⟩ => hbc ▸ I.mul_closed' hb c⟩

    theorem proper_iff_notin [Ring α] {I : Ideal α} : I.proper_ideal ↔ ∃ x, x ∉ I :=
      ⟨fun h => Classical.byContradiction fun h' => h (is_unit_ideal.mpr (of_not_not (not_exists.mp h' 1))),
       fun ⟨x, hx⟩ h => (h ▸ hx : x ∉ (1 : Ideal α)) trivial⟩
    theorem proper_iff_1_notin [Ring α] {I : Ideal α} : I.proper_ideal ↔ 1 ∉ I :=
      not_iff_not.mpr is_unit_ideal
    theorem proper_ideal_subset [Ring α] {I J : Ideal α} (hIJ : I ⊆ J) (hJ : J.proper_ideal) : I.proper_ideal :=
      fun hI => absurd (unit_ideal_in (hI ▸ hIJ)) hJ
    theorem proper_ideal_subsetneq [Ring α] {I J : Ideal α} (hIJ : I ⊊ J) : I.proper_ideal :=
      have ⟨h₁, h₂⟩ := Ideal.subsetneq.mp hIJ
      fun hI => absurd (hI.trans (unit_ideal_in (hI ▸ h₁)).symm) h₂
    theorem zero_ideal_proper_of_nontrivial {α} [Ring α] (h : Ring.is_NonTrivial α) : (ZeroIdeal α).proper_ideal :=
      proper_iff_notin.mpr ⟨1, h⟩
    theorem zero_ideal_proper (α) [NonTrivialRing α] : (ZeroIdeal α).proper_ideal :=
      zero_ideal_proper_of_nontrivial NonTrivial.one_neq_zero
    theorem eq_zero_ideal_of_trivial [Ring α] (h : ¬Ring.is_NonTrivial α) (I : Ideal α) : I = 0 :=
      is_zero_ideal.mpr fun x _ => by rw [←one_mul x, of_not_not h, zero_mul]

    protected def intersection [Ring α] (I J : Ideal α) : Ideal α where
      subset     := I.subset ∩ J.subset
      has_zero   := ⟨I.has_zero, J.has_zero⟩
      add_closed := fun as bs => ⟨I.add_closed as.left bs.left, J.add_closed as.right bs.right⟩
      mul_closed := fun a _ bs => ⟨I.mul_closed a bs.left, J.mul_closed a bs.right⟩
    noncomputable instance IdealIntersection [Ring α] : Intersection (Ideal α) where intersection := Ideal.intersection

    namespace intersection

      protected theorem mem [Ring α] {I J : Ideal α} : ∀ a, a ∈ I ∩ J ↔ a ∈ I ∧ a ∈ J := fun _ => Iff.rfl

      protected theorem subset_left [Ring α] (I J : Ideal α) : I ∩ J ⊆ I := fun _ => And.left
      protected theorem subset_right [Ring α] (I J : Ideal α) : I ∩ J ⊆ J := fun _ => And.right
      protected theorem and_subset_and [Ring α] {I₁ I₂ J₁ J₂ : Ideal α} (hI : I₁ ⊆ I₂) (hJ : J₁ ⊆ J₂) : I₁ ∩ J₁ ⊆ I₂ ∩ J₂ :=
        fun _ => And.imp (hI ·) (hJ ·)

      protected theorem of_subset [Ring α] {I J : Ideal α} (h : I ⊆ J) : I ∩ J = I :=
        Ideal.antisymm (intersection.subset_left I J) fun a ha => ⟨ha, h ha⟩

      protected theorem comm [Ring α] (I J : Ideal α) : I ∩ J = J ∩ I :=
        Ideal.ext'.mpr fun a => ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩

      protected theorem inter_zero [Ring α] (I : Ideal α) : I ∩ 0 = 0 :=
        intersection.comm I 0 ▸ intersection.of_subset (zero_ideal_in I)

      protected theorem inter_one [Ring α] (I : Ideal α) : I ∩ 1 = I :=
        intersection.of_subset (in_unit_ideal I)

    end intersection

    protected def sIntersection [Ring α] (S : Set (Ideal α)) : Ideal α where
      subset     := ⋂₀ S.toSetSet Ideal.subset
      has_zero   := fun s ⟨I, IS, hIs⟩ => by rw [←hIs]; exact I.has_zero
      add_closed := by
        intro a b ha hb s ⟨I, IS, hIs⟩; rw [←hIs]; exact I.add_closed
          (by rw [hIs]; exact ha s ⟨I, IS, hIs⟩)
          (by rw [hIs]; exact hb s ⟨I, IS, hIs⟩)
      mul_closed := by
        intro a b hb s ⟨I, IS, hIs⟩; rw [←hIs]; exact I.mul_closed a (by rw [hIs]; exact hb s ⟨I, IS, hIs⟩)
    noncomputable instance IdealSIntersection [Ring α] : Set.SIntersection (Ideal α) where sIntersection := Ideal.sIntersection

    namespace sIntersection

      theorem of_two [Ring α] (I J : Ideal α) : I ∩ J = ⋂₀ {K | K = I ∨ K = J} :=
        Ideal.ext'.mpr fun x =>
          ⟨fun ⟨hxI, hxJ⟩ s ⟨K, hKIJ, hKs⟩ => by
            cases hKIJ with
            | inl h => exact hKs ▸ h.symm ▸ hxI
            | inr h => exact hKs ▸ h.symm ▸ hxJ,
          fun h => ⟨h I.subset ⟨I, Or.inl rfl, rfl⟩, h J.subset ⟨J, Or.inr rfl, rfl⟩⟩⟩

      protected theorem mem [Ring α] {S : Set (Ideal α)} {a : α} : a ∈ ⋂₀ S ↔ ∀ I ∈ S, a ∈ I :=
        ⟨fun h I hIS => h I.subset ⟨I, hIS, rfl⟩, fun h s ⟨I, hIS, hIs⟩ => hIs ▸ h I hIS⟩

      protected theorem contains [Ring α] {S : Set (Ideal α)} {I : Ideal α} (h : I ∈ S) : ⋂₀ S ⊆ I :=
        fun x hx => have : I.subset ∈ S.toSetSet Ideal.subset := ⟨I, h, rfl⟩
          Set.SoSIntersection.subset_of_mem this hx

      protected theorem single [Ring α] (I : Ideal α) : ⋂₀ Set.singleton I = I :=
        Ideal.ext'.mpr fun x => ⟨fun hx => hx _ ⟨I, rfl, rfl⟩, fun hx s ⟨J, hJI, hJs⟩ => hJs ▸ hJI ▸ hx⟩

    end sIntersection

    noncomputable def from_set [Ring α] (S : Set α) : Ideal α := ⋂₀ {I : Ideal α | S ⊆ I.subset}

    namespace from_set
      variable [Ring α] (S : Set α)

      theorem contains_set : S ⊆ (from_set S).subset :=
        Set.SoSIntersection.subset fun s ⟨I, hIS, hIs⟩ => hIs ▸ hIS

      variable {S}

      theorem contains_mem {a : α} (ha : a ∈ S) : a ∈ from_set S :=
        contains_set S ha

      theorem contains_mem_mul (a : α) {b : α} (hb : b ∈ S) : a * b ∈ from_set S :=
        (from_set S).mul_closed a (contains_mem hb)

      theorem contains_principal {a : α} (ha : a ∈ S) : principal a ⊆ from_set S :=
        fun x ⟨b, hx⟩ => hx ▸ (from_set S).mul_closed' (contains_mem ha) b

      theorem ideal_contained {I : Ideal α} (hI : S ⊆ I.subset) : from_set S ⊆ I :=
        Set.SoSIntersection.subset_of_mem ⟨I, hI, rfl⟩

      theorem self (I : Ideal α) : from_set I.subset = I :=
        Ideal.antisymm (ideal_contained (Subset.refl _)) (contains_set _)

      theorem is_principal (a : α) : from_set (Set.singleton a) = principal a :=
        Ideal.antisymm (ideal_contained fun x hx => hx.symm ▸ generator_in_principal a)
          (contains_principal rfl)

      theorem contains_unit (h : ∃ a ∈ S, isUnit a) : from_set S = 1 :=
        let ⟨a, haS, ha⟩ := h
        unit_ideal_in (unit_principal ha ▸ contains_principal haS)

      theorem zero_set (α : Type _) [Ring α] : from_set (Set.singleton (0 : α)) = 0 :=
        Ideal.antisymm (ideal_contained (Subset.refl _)) (zero_ideal_in _)

      theorem mem {a : α} : a ∈ from_set S ↔ ∀ I : Ideal α, S ⊆ I.subset → a ∈ I := by
        simp only [from_set, sIntersection.mem]; exact Iff.rfl

      theorem subset {T : Set α} (h : S ⊆ T) : from_set S ⊆ from_set T :=
        fun x hx => mem.mpr fun I hTI => mem.mp hx I (Subset.trans h hTI)

      theorem empty : from_set (∅ : Set α) = 0 :=
        Ideal.ext'.mpr fun x => ⟨(mem.mp · 0 (fun _ _ => by contradiction)), (· ▸ (from_set ∅).has_zero)⟩

      theorem induction (p : α → Prop) {a : α} (ha : a ∈ from_set S) (h₀ : p 0) (h₁ : ∀ x ∈ S, p x)
        (h₂ : ∀ x y, p x → p y → p (x + y)) (h₃ : ∀ x y, p y → p (x * y)) : p a :=
          mem.mp ha ⟨p, h₀, h₂ _ _, h₃⟩ h₁

      theorem to_finset (l : UnorderedList α) : from_set l.toSet = from_set l.to_finset.toSet :=
        congrArg from_set (UnorderedList.to_finset_toSet l)

      theorem mem_finite_gen {S} {a : α} : a ∈ from_set S ↔ ∃ f : Finset α, f.toSet ⊆ S ∧ a ∈ from_set f.toSet :=
        ⟨(induction (fun x => ∃ f : Finset α, f.toSet ⊆ S ∧ x ∈ from_set f.toSet) ·
          ⟨∅, Set.empty_subset _, Ideal.has_zero (from_set ∅)⟩
          (fun x hx => ⟨Finset.singleton x, fun y hy => Finset.in_singleton hy ▸ hx,
            contains_mem (Finset.self_singleton x)⟩)
          (fun x y ⟨fx, hfxS, hxfx⟩ ⟨fy, hfyS, hyfy⟩ => ⟨fx ∪ fy,
            Finset.union_toSet fx fy ▸ Set.union.subset hfxS hfyS,
            mem.mpr fun I hI => I.add_closed
              (mem.mp hxfx I (Subset.trans (Finset.union_toSet fx fy ▸ Set.union.subset_union_left _ _) hI))
              (mem.mp hyfy I (Subset.trans (Finset.union_toSet fx fy ▸ Set.union.subset_union_right _ _) hI))⟩)
          (fun x y ⟨f, hfS, hyf⟩ => ⟨f, hfS, Ideal.mul_closed (from_set _) x hyf⟩)),
        fun ⟨f, hfS, haf⟩ => subset hfS haf⟩

      open Classical

      theorem mem_as_sum_finset {f : Finset α} {a : α} : a ∈ from_set f.toSet ↔ ∃ c : α → α, a = ∑ x in f, c x * x :=
        ⟨fun h => induction (fun a => ∃ c : α → α, a = ∑ x in f, c x * x) h
          ⟨fun _ => 0, (Finset.map_sum.eq_zero (fun x _ => zero_mul x)).symm⟩
          (fun x hx => ⟨fun y => if y = x then 1 else 0, by
            rw [Finset.erase_cons f hx, Finset.map_sum.cons]
            simp only [ite_true]; rw [Finset.map_sum.eq_zero (fun y hy => by
              simp only [(Finset.mem_erase.mp hy).left, ite_false]; exact zero_mul y), zero_add, one_mul]⟩)
          (fun x y ⟨cx, hcx⟩ ⟨cy, hcy⟩ => ⟨fun z => cx z + cy z, hcx ▸ hcy ▸ Finset.map_sum.distrib _ _ _ ▸
            congrArg f.map_sum (funext fun _ => (mul_distrib_right _ _ _).symm)⟩)
          (fun r s ⟨c, hc⟩ => ⟨fun z => r * c z, hc ▸ Finset.map_sum.mul_sum _ _ _ ▸
            congrArg f.map_sum (funext fun _ => (mul_assoc _ _ _).symm)⟩),
        fun ⟨c, h⟩ => h ▸ Finset.map_sum.prop_sum (· ∈ from_set f.toSet) (fun x => c x * x) f
          (from_set f.toSet).has_zero
          (fun x hx => (from_set f.toSet).mul_closed (c x) (from_set.contains_mem hx))
          fun _ _ => (from_set f.toSet).add_closed⟩

      theorem mem_as_sum {a : α} : a ∈ from_set S ↔ ∃ (f : Finset α) (c : α → α), f.toSet ⊆ S ∧ a = ∑ x in f, c x * x :=
        propext mem_finite_gen ▸ ⟨fun ⟨f, hfS, haf⟩ => let ⟨c, hc⟩ := mem_as_sum_finset.mp haf; ⟨f, c, hfS, hc⟩,
        fun ⟨f, c, hf, ha⟩ => ⟨f, hf, ha ▸ Finset.induction (fun fs =>
          (∑ x in fs, c x * x) ∈ from_set fs.toSet) (from_set ∅).has_zero
          (fun x s hx ih => by
            simp only; exact Finset.map_sum.sum_insert _ hx ▸ (from_set (s.insert x).toSet).add_closed
              ((from_set (s.insert x).toSet).mul_closed _ (from_set.contains_mem (Finset.mem_insert_self x s)))
              (from_set.subset (fun _ => Finset.mem_insert_of_mem : s ⊆ s.insert x) ih)) f⟩⟩

      theorem repeat (S : Set α) : from_set (from_set S).subset = from_set S :=
        Ideal.antisymm (ideal_contained (Subset.refl (from_set S).subset)) (contains_set _)

    end from_set

    def finitely_generated [Ring α] (I : Ideal α) : Prop := ∃ f : Finset α, I = from_set f.toSet

    namespace finitely_generated

      theorem zero [Ring α] : (0 : Ideal α).finitely_generated := ⟨∅, from_set.empty.symm⟩

      variable [Ring α] {I : Ideal α} (h : I.finitely_generated)
      open Classical

      noncomputable def generating_set : Finset α := choose h

      theorem generating_set_def : I = from_set (generating_set h).toSet := choose_spec h

      theorem generating_set_subset : (generating_set h).toSet ⊆ I.subset :=
        fun x hx => generating_set_def h ▸ from_set.contains_set _ hx

      theorem has_minimal_generating_set : ∃ f : Finset α, I = from_set f.toSet ∧
        ∀ g : Finset α, I = from_set g.toSet → f.length ≤ g.length :=
          let ⟨f, hf⟩ := h
          minimal.min_exists ({fs | I = from_set fs.toSet} : Set (Finset α)) ⟨f, hf⟩ Finset.length

      noncomputable def minimal_generator_count : Nat := (choose (has_minimal_generating_set h)).length

    end finitely_generated

    section
      open from_set

      theorem iff_finite_subbasis [Ring α] {I : Ideal α} : I.finitely_generated ↔
        ∀ S : Set α, I = from_set S → ∃ f : Finset α, f.toSet ⊆ S ∧ I = from_set f.toSet :=
          ⟨fun h S hS => by
            let ⟨f, hfS, hf⟩ := @Finset.cons_induction α
              (fun fs => fs.toSet ⊆ I.subset → ∃ f, f.toSet ⊆ S ∧ fs.toSet ⊆ (from_set (Finset.toSet f)).subset)
              (fun _ => ⟨∅, fun _ _ => by contradiction, fun _ h => False.elim
                (Finset.mem_empty.mp (Finset.ext_toSet.mpr h))⟩) (fun a s ha h₁ h₂ =>
                  let ⟨f₁, hf₁S, hsf₁⟩ := h₁ (fun x hx => h₂ (Finset.cons_subset s ha hx))
                  let ⟨f₂, hf₂S, haf₂⟩ := from_set.mem_finite_gen.mp (hS ▸ h₂ (s.mem_cons_self ha) : a ∈ from_set S)
                  ⟨f₁ ∪ f₂, Finset.union_toSet f₁ f₂ ▸ Set.union.subset hf₁S hf₂S, fun x hx =>
                    Or.elim (Finset.mem_cons.mp hx) (Finset.union_toSet f₁ f₂ ▸ · ▸
                      from_set.subset (Set.union.subset_union_right f₁.toSet f₂.toSet) haf₂)
                      fun h => Finset.union_toSet f₁ f₂ ▸ from_set.subset
                      (Set.union.subset_union_left f₁.toSet f₂.toSet) (hsf₁ h)⟩)
                h.generating_set h.generating_set_subset
            exact ⟨f, hfS, Ideal.antisymm (fun x hx => by
              have := from_set.subset hf
              rw [from_set.repeat, ←h.generating_set_def] at this
              exact this hx) (hS ▸ from_set.subset hfS)⟩,
          fun h => let ⟨f, h₁, h₂⟩ := h I.subset (from_set.self I).symm; ⟨f, h₂⟩⟩

      theorem iff_finite_subbasis' [Ring α] {I : Ideal α} : I.finitely_generated ↔
        ∀ S : Set α, infinite S → I = from_set S → ∃ f : Finset α, f.toSet ⊆ S ∧ I = from_set f.toSet :=
          iff_finite_subbasis.trans ⟨fun h S _ => h S, fun h S hIS => by
            byCases hS : finite S
            { exact ⟨hS.to_finset, fun _ => hS.mem_to_finset.mp, hS.to_finset_toSet.symm ▸ hIS⟩ }
            { exact h S hS hIS }⟩

    end

    abbrev product_gen [Ring α] (I J : Ideal α) : Set α := {x | ∃ i ∈ I, ∃ j ∈ J, x = i * j}

    protected noncomputable def product [Ring α] (I J : Ideal α) : Ideal α :=
      from_set (product_gen I J)
    noncomputable instance IdealMul [Ring α] : Mul (Ideal α) where mul := Ideal.product

    namespace product

      protected theorem comm [Ring α] (I J : Ideal α) : I * J = J * I :=
        congrArg from_set (Set.ext.mp fun a =>
          ⟨fun ⟨i, hi, j, hj, hij⟩ => ⟨j, hj, i, hi, Semiring.mul_comm i j ▸ hij⟩,
          fun ⟨j, hj, i, hi, hji⟩ => ⟨i, hi, j, hj, Semiring.mul_comm j i ▸ hji⟩⟩)

      theorem mem [Ring α] {I J : Ideal α} {a : α} :
        a ∈ I * J ↔ ∀ K : Ideal α, product_gen I J ⊆ K.subset → a ∈ K := by
          rw [←from_set.mem]; exact Iff.rfl

      theorem subset_inter [Ring α] {I J : Ideal α} : I * J ⊆ I ∩ J := fun x hx =>
        mem.mp hx (I ∩ J) fun x ⟨i, hi, j, hj, hxij⟩ => hxij ▸ ⟨I.mul_closed' hi j, J.mul_closed i hj⟩

      theorem subset_left [Ring α] {I J : Ideal α} : I * J ⊆ I :=
        Subset.trans subset_inter (Set.intersection.subset_inter_left _ _)

      theorem subset_right [Ring α] {I J : Ideal α} : I * J ⊆ J :=
        Subset.trans subset_inter (Set.intersection.subset_inter_right _ _)

      theorem mul_subset_mul [Ring α] {I₁ I₂ J₁ J₂ : Ideal α} (hI : I₁ ⊆ I₂) (hJ : J₁ ⊆ J₂) : I₁ * J₁ ⊆ I₂ * J₂ :=
        from_set.subset fun x ⟨i, hi, j, hj, hij⟩ => ⟨i, hI hi, j, hJ hj, hij⟩

      theorem principal_mul [Ring α] (a : α) (I : Ideal α) : (principal a * I).subset = {x | ∃ y ∈ I, x = a * y} :=
        Set.ext.mp fun x => ⟨fun hx => from_set.induction (fun x => ∃ y ∈ I, x = a * y) hx
          ⟨0, I.has_zero, (mul_zero a).symm⟩
          (fun x ⟨i, ⟨b, hb⟩, j, hj, hij⟩ => ⟨b * j, I.mul_closed b hj, by rw [hij, ←hb, mul_assoc]⟩)
          (fun x y ⟨x', hx', hex'⟩ ⟨y', hy', hey'⟩ => ⟨x' + y', I.add_closed hx' hy', by rw [hex', hey', mul_distrib_left]⟩)
          (fun x y ⟨y', hy', hey'⟩ => ⟨x * y', I.mul_closed x hy', by rw [hey', mul_left_comm]⟩),
          fun ⟨y, hy, hyx⟩ => from_set.contains_mem ⟨a, generator_in_principal a, y, hy, hyx⟩⟩

      private abbrev triple_product_gen [Ring α] (I J K : Ideal α) : Set α := {x | ∃ i ∈ I, ∃ j ∈ J, ∃ k ∈ K, x = i * j * k}
      private abbrev mult_fibre [Ring α] (f : Finset α) (k y : α) : Set α := {x | x ∈ f ∧ x * k = y}

      theorem triple [Ring α] (I J K : Ideal α) : I * J * K = from_set (triple_product_gen I J K) :=
        Ideal.ext'.mpr fun x => ⟨fun hx =>
          let ⟨fx, cx, hfx, hcx⟩ := from_set.mem_as_sum.mp hx
          hcx ▸ @Finset.cons_induction α (fun f => f.toSet ⊆ product_gen (I * J) K →
            ∀ c : α → α, (∑ a in f, c a * a) ∈ from_set (triple_product_gen I J K))
            (fun hf c => Finset.map_sum.empty _ ▸ (from_set (triple_product_gen I J K)).has_zero)
            (fun a f ha ih hf c => Finset.map_sum.cons _ _ ▸ (from_set (triple_product_gen I J K)).add_closed
              (ih (Subset.trans (Finset.cons_subset f ha) hf) c)
              (let ⟨ij, hij, k, hk, h⟩ := hf (Finset.mem_cons_self f ha)
              let ⟨fij, cij, hfij, hcij⟩ := from_set.mem_as_sum.mp hij
              -- need finset made up of elems of `fij` multiplied by `k`
              -- coefficient of `x` is sum of coefficients `cij (i * j)` (where `i * j ∈ fij`) such that `i * j * k = x`
              (from_set (triple_product_gen I J K)).mul_closed _ (from_set.mem_as_sum.mpr ⟨(fij.map (· * k)).to_finset,
                fun x => (∑ cij in (finite.subset fij.to_finite (fun _ => And.left : mult_fibre fij k x ⊆ fij.toSet)).to_finset),
                fun z hz =>
                  let ⟨b, hb₁, hb₂⟩ := Finset.map_mem.mp (UnorderedList.to_finset_toSet _ ▸ hz : z ∈ (fij.map (· * k)).toSet)
                  let ⟨i, hi, j, hj, hij⟩ := hfij hb₁
                  ⟨i, hi, j, hj, k, hk, by rw [←hb₂, hij]⟩,
                by
                  rw [h, hcij]
                  exact @Finset.cons_induction α (fun f => (∑ x in f, cij x * x) * k = ∑ x in (f.map (· * k)).to_finset,
                    (∑ cij in (finite.subset f.to_finite (fun _ => And.left : mult_fibre f k x ⊆ f.toSet)).to_finset) * x)
                    (by simp only [Finset.map_empty, UnorderedList.to_finset_zero, Finset.map_sum.empty, zero_mul])
                    (fun x s hx ih => by
                      simp only [Finset.map_sum.cons, mul_distrib_right, ih, Finset.map_cons, mul_assoc]
                      byCases h : x * k ∈ s.map (· * k)
                      { rw [UnorderedList.to_finset_cons_of_pos h, Finset.map_sum.sum_term _ _ (UnorderedList.mem_to_finset.mpr h),
                          Finset.map_sum.sum_term _ _ (UnorderedList.mem_to_finset.mpr h), add_assoc, ←mul_distrib_right];
                        have hxs : x ∉ (finite.subset s.to_finite (fun _ => And.left : mult_fibre s k (x * k) ⊆ s.toSet)).to_finset :=
                          fun h => hx ((finite.mem_to_finset _).mp h).left
                        have : (finite.subset (s.cons x hx).to_finite (fun _ => And.left : mult_fibre (s.cons x hx) k (x * k) ⊆ (s.cons x hx).toSet)).to_finset =
                          (finite.subset s.to_finite (fun _ => And.left : mult_fibre s k (x * k) ⊆ s.toSet)).to_finset.cons x hxs := by
                            apply Finset.ext; intro; rw [finite.mem_to_finset, Finset.mem_cons]
                            exact ⟨fun ⟨h₁, h₂⟩ => Or.imp_right (fun h => (finite.mem_to_finset _).mpr ⟨h, h₂⟩) (Finset.mem_cons.mp h₁),
                              (Or.elim · (fun h => ⟨h.symm ▸ s.mem_cons_self hx, congrArg (· * k) h⟩)
                                (fun h => have ⟨h₁, h₂⟩ := (finite.mem_to_finset _).mp h; ⟨Finset.mem_cons_self' hx h₁, h₂⟩))⟩
                        rw [this, Finset.map_sum.cons]
                        exact congrArg (· + _) (Finset.map_sum.congr rfl fun b hb => congrArg (· * b) (Finset.map_sum.congr
                          (finite.to_finset_ext.mpr fun c => ⟨(And.imp_left (Finset.mem_cons_self' hx ·) ·),
                            fun ⟨h₁, h₂⟩ => ⟨(Finset.mem_cons.mp h₁).resolve_left (fun h =>
                              (Finset.mem_erase.mp hb).left (h ▸ h₂.symm)), h₂⟩⟩) (fun _ _ => rfl))) }
                      { rw [UnorderedList.to_finset_cons_of_neg h, Finset.map_sum.cons]
                        have : (finite.subset (s.cons x hx).to_finite (fun _ => And.left :
                          mult_fibre (s.cons x hx) k (x * k) ⊆ (s.cons x hx).toSet)).to_finset = Finset.singleton x := by
                            apply Finset.ext; intro b; rw [Finset.mem_singleton, finite.mem_to_finset]
                            exact ⟨fun ⟨h₁, h₂⟩ => (Finset.mem_cons.mp h₁).resolve_right fun hb => h (Finset.map_mem.mpr ⟨b, hb, h₂⟩),
                              fun hb => ⟨hb.symm ▸ s.mem_cons_self hx, congrArg (· * k) hb⟩⟩
                        rw [this, Finset.map_sum.singleton]
                        exact congrArg (· + cij x * (x * k)) (Finset.map_sum.congr rfl fun y hy => congrArg (· * y)
                          (Finset.map_sum.congr (finite.to_finset_ext.mpr fun z => ⟨(And.imp_left (Finset.mem_cons_self' hx ·) ·),
                            fun ⟨h₁, h₂⟩ => ⟨(Finset.mem_cons.mp h₁).resolve_left (fun h' => h (Finset.map_mem.mpr ((h' ▸ h₂ : x * k = y) ▸
                              Finset.map_mem.mp (UnorderedList.mem_to_finset.mp hy)))), h₂⟩⟩) (fun _ _ => rfl))) }) fij⟩))) fx hfx cx,
          fun hx =>
            let ⟨fx, cx, hfx, hcx⟩ := from_set.mem_as_sum.mp hx
            hcx ▸ @Finset.cons_induction α (fun f => f.toSet ⊆ triple_product_gen I J K →
              ∀ c : α → α, (∑ x in f, c x * x) ∈ I * J * K)
              (fun _ _ => Finset.map_sum.empty _ ▸ (I * J * K).has_zero)
              (fun a f ha ih hf c => Finset.map_sum.cons _ _ ▸ (I * J * K).add_closed
                (ih (Subset.trans (Finset.cons_subset f ha) hf) c)
                ((I * J * K).mul_closed _
                  (let ⟨i, hi, j, hj, k, hk, he⟩ := hf (f.mem_cons_self ha)
                  from_set.mem_as_sum.mpr ⟨Finset.singleton a, fun _ => 1, fun b hb =>
                    ⟨i * j, from_set.contains_set _ ⟨i, hi, j, hj, rfl⟩, k, hk, Finset.mem_singleton.mp hb ▸ he⟩,
                    by rw [Finset.map_sum.singleton, one_mul]⟩))) fx hfx cx⟩

      protected theorem assoc [Ring α] (I J K : Ideal α) : I * J * K = I * (J * K) := by
        rw [triple, product.comm, triple]
        exact congrArg from_set (Set.ext.mp fun x =>
          ⟨fun ⟨i, hi, j, hj, k, hk, hijk⟩ => ⟨j, hj, k, hk, i, hi, Semiring.mul_comm _ _ ▸ mul_assoc _ _ _ ▸ hijk⟩,
            fun ⟨j, hj, k, hk, i, hi, hjki⟩ => ⟨i, hi, j, hj, k, hk, mul_assoc _ _ _ ▸ Semiring.mul_comm _ _ ▸ hjki⟩⟩)

      open Classical

      private noncomputable abbrev choose_i [Ring α] {I J K : Ideal α} {f : Finset α} (hf : f.toSet ⊆ product_gen I (J + K))
        {x : α} (hx : x ∈ f) : α := choose (hf hx)
      private noncomputable abbrev choose_j [Ring α] {I J K : Ideal α} {f : Finset α} (hf : f.toSet ⊆ product_gen I (J + K))
        {x : α} (hx : x ∈ f) : α := choose (choose_spec (choose_spec (hf hx)).right).left
      private noncomputable abbrev choose_k [Ring α] {I J K : Ideal α} {f : Finset α} (hf : f.toSet ⊆ product_gen I (J + K))
        {x : α} (hx : x ∈ f) : α := choose (choose_spec (choose_spec (choose_spec (hf hx)).right).left).right
      private theorem choose_hi [Ring α] {I J K : Ideal α} {f : Finset α} (hf : f.toSet ⊆ product_gen I (J + K))
        {x : α} (hx : x ∈ f) : choose_i hf hx ∈ I := (choose_spec (hf hx)).left
      private theorem choose_hj [Ring α] {I J K : Ideal α} {f : Finset α} (hf : f.toSet ⊆ product_gen I (J + K))
        {x : α} (hx : x ∈ f) : choose_j hf hx ∈ J := (choose_spec (choose_spec (choose_spec (hf hx)).right).left).left
      private theorem choose_hk [Ring α] {I J K : Ideal α} {f : Finset α} (hf : f.toSet ⊆ product_gen I (J + K))
        {x : α} (hx : x ∈ f) : choose_k hf hx ∈ K := (choose_spec (choose_spec (choose_spec (choose_spec (hf hx)).right).left).right).left
      private theorem choose_heq [Ring α] {I J K : Ideal α} {f : Finset α} (hf : f.toSet ⊆ product_gen I (J + K))
        {x : α} (hx : x ∈ f) : x = choose_i hf hx * (choose_j hf hx + choose_k hf hx) := by
          rw [(choose_spec (choose_spec (choose_spec (choose_spec (hf hx)).right).left).right).right,
            ←(choose_spec (choose_spec (hf hx)).right).right]

      private noncomputable abbrev distrib_gens_left [Ring α] {I J K : Ideal α} {f : Finset α}
        (hf : f.toSet ⊆ product_gen I (J + K)) : Finset α :=
          (f.elems.pmap (fun x hx => choose_i hf hx * choose_j hf hx) (fun _ => id)).to_finset
      private noncomputable abbrev distrib_gens_right [Ring α] {I J K : Ideal α} {f : Finset α}
        (hf : f.toSet ⊆ product_gen I (J + K)) : Finset α :=
          (f.elems.pmap (fun x hx => choose_i hf hx * choose_k hf hx) (fun _ => id)).to_finset

      private theorem distrib_gens_left_subset [Ring α] {I J K : Ideal α} {f : Finset α}
        (hf : f.toSet ⊆ product_gen I (J + K)) : (distrib_gens_left hf).toSet ⊆ product_gen I J := fun b hb =>
          let ⟨y, hy, he⟩ := UnorderedList.mem_pmap.mp (UnorderedList.mem_to_finset.mp hb)
          ⟨choose_i hf hy, choose_hi hf hy, choose_j hf hy, choose_hj hf hy, he.symm⟩
      private theorem distrib_gens_right_subset [Ring α] {I J K : Ideal α} {f : Finset α}
        (hf : f.toSet ⊆ product_gen I (J + K)) : (distrib_gens_right hf).toSet ⊆ product_gen I K := fun b hb =>
          let ⟨y, hy, he⟩ := UnorderedList.mem_pmap.mp (UnorderedList.mem_to_finset.mp hb)
          ⟨choose_i hf hy, choose_hi hf hy, choose_k hf hy, choose_hk hf hy, he.symm⟩

      private abbrev distrib_gens_left_coeff_set [Ring α] {I J K : Ideal α} {f : Finset α}
        (hf : f.toSet ⊆ product_gen I (J + K)) (x : α) : Set α :=
          {y | if hy : y ∈ f then choose_i hf hy * choose_j hf hy = x else False}
      /-- All elements `y` of `distrib_gens_left_coeff_set hf x` satisfy `y ∈ f`. -/
      private theorem distrib_gens_left_coeff_subset [Ring α] {I J K : Ideal α} {f : Finset α}
        {hf : f.toSet ⊆ product_gen I (J + K)} {x : α} (hx : x ∈ distrib_gens_left hf) :
          distrib_gens_left_coeff_set hf x ⊆ f.toSet :=
            fun b (hb : if hy : b ∈ f then _ else False) => by
              byCases hb' : b ∈ f; { exact hb' } { simp only [hb', dite_false] at hb }
      /-- All elements `y` of `distrib_gens_left_coeff_set hf x` satisfy `choose_i y * choose_k y = x`. -/
      private theorem distrib_gens_left_coeff_eq [Ring α] {I J K : Ideal α} {f : Finset α}
        {hf : f.toSet ⊆ product_gen I (J + K)} {x : α} (hx : x ∈ distrib_gens_left hf) {y : α}
          (hy : y ∈ distrib_gens_left_coeff_set hf x) : choose_i hf (distrib_gens_left_coeff_subset hx hy) *
            choose_j hf (distrib_gens_left_coeff_subset hx hy) = x := by
              have hy' : y ∈ f := distrib_gens_left_coeff_subset hx hy
              have : if hy : y ∈ f then choose_i hf hy * choose_j hf hy = x else False := hy
              simp only [hy', dite_true] at this
              exact this
      private theorem to_distrib_gens_left_coeff [Ring α] {I J K : Ideal α} {f : Finset α}
        {hf : f.toSet ⊆ product_gen I (J + K)} {x : α} (hx : x ∈ distrib_gens_left hf) {y : α}
          (hy : y ∈ f) (he : choose_i hf hy * choose_j hf hy = x) : y ∈ distrib_gens_left_coeff_set hf x :=
            (by simp only [hy, dite_true, he] : if hy : y ∈ f then choose_i hf hy * choose_j hf hy = x else False)
      private noncomputable abbrev distrib_gens_left_coeff [Ring α] {I J K : Ideal α} {f : Finset α}
        (hf : f.toSet ⊆ product_gen I (J + K)) (c : α → α) : α → α := fun x =>
          if hx : x ∈ distrib_gens_left hf then
            ∑ c in (finite.subset f.to_finite (distrib_gens_left_coeff_subset hx)).to_finset
          else 0

      private abbrev distrib_gens_right_coeff_set [Ring α] {I J K : Ideal α} {f : Finset α}
        (hf : f.toSet ⊆ product_gen I (J + K)) (x : α) : Set α :=
          {y | if hy : y ∈ f then choose_i hf hy * choose_k hf hy = x else False}
      /-- All elements `y` of `distrib_gens_right_coeff_set hf x` satisfy `y ∈ f`. -/
      private theorem distrib_gens_right_coeff_subset [Ring α] {I J K : Ideal α} {f : Finset α}
        {hf : f.toSet ⊆ product_gen I (J + K)} {x : α} (hx : x ∈ distrib_gens_right hf) :
          distrib_gens_right_coeff_set hf x ⊆ f.toSet :=
            fun b (hb : if hy : b ∈ f then _ else False) => by
              byCases hb' : b ∈ f; { exact hb' } { simp only [hb', dite_false] at hb }
      /-- All elements `y` of `distrib_gens_right_coeff_set hf x` satisfy `choose_i y * choose_k y = x`. -/
      private theorem distrib_gens_right_coeff_eq [Ring α] {I J K : Ideal α} {f : Finset α}
        {hf : f.toSet ⊆ product_gen I (J + K)} {x : α} (hx : x ∈ distrib_gens_right hf) {y : α}
          (hy : y ∈ distrib_gens_right_coeff_set hf x) : choose_i hf (distrib_gens_right_coeff_subset hx hy) *
            choose_k hf (distrib_gens_right_coeff_subset hx hy) = x := by
              have hy' : y ∈ f := distrib_gens_right_coeff_subset hx hy
              have : if hy : y ∈ f then choose_i hf hy * choose_k hf hy = x else False := hy
              simp only [hy', dite_true] at this
              exact this
      private theorem to_distrib_gens_right_coeff [Ring α] {I J K : Ideal α} {f : Finset α}
        {hf : f.toSet ⊆ product_gen I (J + K)} {x : α} (hx : x ∈ distrib_gens_right hf) {y : α}
          (hy : y ∈ f) (he : choose_i hf hy * choose_k hf hy = x) : y ∈ distrib_gens_right_coeff_set hf x :=
            (by simp only [hy, dite_true, he] : if hy : y ∈ f then choose_i hf hy * choose_k hf hy = x else False)
      private noncomputable abbrev distrib_gens_right_coeff [Ring α] {I J K : Ideal α} {f : Finset α}
        (hf : f.toSet ⊆ product_gen I (J + K)) (c : α → α) : α → α := fun x =>
          if hx : x ∈ distrib_gens_right hf then
            ∑ c in (finite.subset f.to_finite (distrib_gens_right_coeff_subset hx)).to_finset
          else 0

      private theorem product_gen_subset [Ring α] (I : Ideal α) {J K : Ideal α} (h : J ⊆ K) :
        product_gen I J ⊆ product_gen I K := fun x ⟨i, hi, j, hj, he⟩ => ⟨i, hi, j, h hj, he⟩
      private noncomputable abbrev distrib_coeff [Ring α] (fij fik : Finset α) (cij cik : α → α) (x : α) : α :=
        if x ∈ fij then if x ∈ fik then cij x + cik x else cij x else cik x
      private noncomputable abbrev distrib_coeff_empty_left [Ring α] (fik : Finset α) (cij cik : α → α) (x : α) :
        distrib_coeff ∅ fik cij cik x = cik x := by simp only [distrib_coeff, Finset.mem_empty, ite_false]
      private noncomputable abbrev distrib_coeff_only_left [Ring α] {fij fik : Finset α} (cij cik : α → α)
        {x : α} (hij : x ∈ fij) (hik : x ∉ fik) : distrib_coeff fij fik cij cik x = cij x := by
          simp only [distrib_coeff, hij, ite_true, hik, ite_false]

      protected theorem distrib [Ring α] (I J K : Ideal α) : I * (J + K) = I * J + I * K :=
        Ideal.ext'.mpr fun a =>
          ⟨fun ha =>
            let ⟨fa, ca, hfa, hca⟩ := from_set.mem_as_sum.mp ha
            let fij := distrib_gens_left hfa
            let cij := distrib_gens_left_coeff hfa ca
            let fik := distrib_gens_right hfa
            let cik := distrib_gens_right_coeff hfa ca
            ⟨(∑ x in fij, cij x * x), from_set.mem_as_sum.mpr ⟨fij, cij, distrib_gens_left_subset hfa, rfl⟩,
             (∑ x in fik, cik x * x), from_set.mem_as_sum.mpr ⟨fik, cik, distrib_gens_right_subset hfa, rfl⟩,
              hca ▸ @Finset.cons_induction α (fun f => (hf : f.toSet ⊆ product_gen I (J + K)) →
                (∑ x in distrib_gens_left hf, distrib_gens_left_coeff hf ca x * x) +
                (∑ x in distrib_gens_right hf, distrib_gens_right_coeff hf ca x * x) = ∑ x in f, ca x * x)
                (fun hf => by rw [(by rfl : distrib_gens_left hf = ∅), Finset.map_sum.empty, zero_add]; rfl)
                (fun b f hb ih hfb => by
                  have hf : f.toSet ⊆ product_gen I (J + K) := fun x hx => hfb (Finset.mem_cons_self' hb hx)
                  rw [Finset.map_sum.cons, ←ih hf]
                  let i := choose_i hfb (f.mem_cons_self hb)
                  let j := choose_j hfb (f.mem_cons_self hb)
                  let k := choose_k hfb (f.mem_cons_self hb)
                  have h₁ : (∑ x in distrib_gens_left hfb, distrib_gens_left_coeff hfb ca x * x) =
                    (∑ x in distrib_gens_left hf, distrib_gens_left_coeff hf ca x * x) + ca b * (i * j) := by
                      byCases h : i * j ∈ distrib_gens_left hf
                      { have heq : distrib_gens_left hfb = distrib_gens_left hf := by
                          apply Finset.ext; intro
                          simp only [UnorderedList.mem_to_finset, UnorderedList.mem_pmap]
                          exact ⟨fun ⟨a, ha, hea⟩ => Or.elim (Finset.mem_cons.mp ha)
                            (fun ha =>
                              let ⟨c, hc, hec⟩ := UnorderedList.mem_pmap.mp (UnorderedList.mem_to_finset.mp h)
                              ⟨c, hc, by rw [hec, ←hea]; subst ha; rfl⟩)
                            fun ha => ⟨a, ha, hea⟩,
                            fun ⟨a, ha, hea⟩ => ⟨a, Finset.mem_cons_self' hb ha, hea⟩⟩
                        rw [heq, Finset.map_sum.sum_term _ _ h, Finset.map_sum.sum_term _ _ h, add_assoc, ←mul_distrib_right]
                        have h' : i * j ∈ distrib_gens_left hfb := heq ▸ h
                        have : distrib_gens_left_coeff hfb ca (i * j) = distrib_gens_left_coeff hf ca (i * j) + ca b := by
                          have : (finite.subset (f.cons b hb).to_finite (distrib_gens_left_coeff_subset h')).to_finset =
                            (finite.subset f.to_finite (distrib_gens_left_coeff_subset h)).to_finset.cons b fun hb' =>
                              hb (distrib_gens_left_coeff_subset h ((finite.mem_to_finset _).mp hb')) := by
                                apply Finset.ext; intro
                                rw [finite.mem_to_finset, Finset.mem_cons, finite.mem_to_finset]
                                exact ⟨fun hx => Or.imp_right
                                  (to_distrib_gens_left_coeff h · (distrib_gens_left_coeff_eq h' hx))
                                  (Finset.mem_cons.mp (distrib_gens_left_coeff_subset h' hx)),
                                (Or.elim · (fun hx => hx.symm ▸ to_distrib_gens_left_coeff h' (f.mem_cons_self hb) rfl)
                                  fun hx => to_distrib_gens_left_coeff h'
                                    (Finset.mem_cons_self' hb (distrib_gens_left_coeff_subset h hx))
                                    (distrib_gens_left_coeff_eq h hx))⟩
                          simp only [distrib_gens_left_coeff, h, h', dite_true, this, Finset.map_sum.cons]
                        rw [this]
                        exact congrArg (· + _) (Finset.map_sum.congr rfl (fun c hc => congrArg (· * c) (by
                          have ⟨he, hc⟩ := Finset.mem_erase.mp hc
                          have hcb : c ∈ distrib_gens_left hfb := heq ▸ hc
                          simp only [distrib_gens_left_coeff, hc, hcb, dite_true]
                          exact Finset.map_sum.congr (finite.to_finset_ext.mpr fun d =>
                            ⟨fun hd => to_distrib_gens_left_coeff hc ((Finset.mem_cons.mp
                              (distrib_gens_left_coeff_subset hcb hd)).resolve_left (fun h => by
                                subst h; exact he (distrib_gens_left_coeff_eq hcb hd).symm))
                              (distrib_gens_left_coeff_eq hcb hd),
                            fun hd => to_distrib_gens_left_coeff hcb (Finset.mem_cons_self' hb
                              (distrib_gens_left_coeff_subset hc hd))
                              (distrib_gens_left_coeff_eq hc hd)⟩) fun _ _ => rfl))) }
                      { have heq : distrib_gens_left hfb = (distrib_gens_left hf).cons (i * j) h := by
                          apply Finset.ext; intro
                          simp only [Finset.mem_cons, UnorderedList.mem_to_finset, UnorderedList.mem_pmap]
                          exact ⟨fun ⟨a, ha, hea⟩ => Or.imp
                              (fun ha => by subst ha; exact hea.symm)
                              (fun ha => ⟨a, ha, hea⟩) (Finset.mem_cons.mp ha),
                            (Or.elim · (fun ha => ⟨b, f.mem_cons_self hb, ha.symm⟩)
                              fun ⟨a, ha, hea⟩ => ⟨a, Finset.mem_cons_self' hb ha, hea⟩)⟩
                        rw [heq, Finset.map_sum.cons]
                        have hij : i * j ∈ distrib_gens_left hfb := UnorderedList.mem_to_finset.mpr
                          (UnorderedList.mem_pmap.mpr ⟨b, f.mem_cons_self hb, rfl⟩)
                        have : distrib_gens_left_coeff hfb ca (i * j) = ca b := by
                          simp only [distrib_gens_left_coeff, hij, dite_true]
                          have : (finite.subset (f.cons b hb).to_finite (distrib_gens_left_coeff_subset hij)).to_finset = Finset.singleton b := by
                            apply Finset.ext; intro c; rw [Finset.mem_singleton, finite.mem_to_finset]
                            exact ⟨fun hc => (Finset.mem_cons.mp (distrib_gens_left_coeff_subset hij hc)).resolve_right fun h' =>
                                h (UnorderedList.mem_to_finset.mpr (UnorderedList.mem_pmap.mpr ⟨c, h', distrib_gens_left_coeff_eq hij hc⟩)),
                              fun hc => by subst hc; exact to_distrib_gens_left_coeff hij (f.mem_cons_self hb) rfl⟩
                          rw [this, Finset.map_sum.singleton]
                        rw [this]
                        exact congrArg (· + _) (Finset.map_sum.congr rfl (fun c hc => congrArg (· * c)
                          (by
                            have hcb : c ∈ distrib_gens_left hfb := heq ▸ Finset.mem_cons_self' h hc
                            simp only [distrib_gens_left_coeff, hc, hcb, dite_true]
                            exact Finset.map_sum.congr (finite.to_finset_ext.mpr fun d =>
                              ⟨fun hd => have := distrib_gens_left_coeff_eq hcb hd
                                Or.elim (Finset.mem_cons.mp (distrib_gens_left_coeff_subset hcb hd))
                                  (fun hd' => by subst hd'; exact absurd (this ▸ hc) h)
                                  fun hd' => to_distrib_gens_left_coeff hc hd' this,
                              fun hd => to_distrib_gens_left_coeff hcb (Finset.mem_cons_self' hb
                                (distrib_gens_left_coeff_subset hc hd)) (distrib_gens_left_coeff_eq hc hd)⟩)
                              (fun _ _ => rfl)))) }
                  have h₂ : (∑ x in distrib_gens_right hfb, distrib_gens_right_coeff hfb ca x * x) =
                    (∑ x in distrib_gens_right hf, distrib_gens_right_coeff hf ca x * x) + ca b * (i * k) := by
                      byCases h : i * k ∈ distrib_gens_right hf
                      { have heq : distrib_gens_right hfb = distrib_gens_right hf := by
                          apply Finset.ext; intro
                          simp only [UnorderedList.mem_to_finset, UnorderedList.mem_pmap]
                          exact ⟨fun ⟨a, ha, hea⟩ => Or.elim (Finset.mem_cons.mp ha)
                            (fun ha =>
                              let ⟨c, hc, hec⟩ := UnorderedList.mem_pmap.mp (UnorderedList.mem_to_finset.mp h)
                              ⟨c, hc, by rw [hec, ←hea]; subst ha; rfl⟩)
                            fun ha => ⟨a, ha, hea⟩,
                            fun ⟨a, ha, hea⟩ => ⟨a, Finset.mem_cons_self' hb ha, hea⟩⟩
                        rw [heq, Finset.map_sum.sum_term _ _ h, Finset.map_sum.sum_term _ _ h, add_assoc, ←mul_distrib_right]
                        have h' : i * k ∈ distrib_gens_right hfb := heq ▸ h
                        have : distrib_gens_right_coeff hfb ca (i * k) = distrib_gens_right_coeff hf ca (i * k) + ca b := by
                          have : (finite.subset (f.cons b hb).to_finite (distrib_gens_right_coeff_subset h')).to_finset =
                            (finite.subset f.to_finite (distrib_gens_right_coeff_subset h)).to_finset.cons b fun hb' =>
                              hb (distrib_gens_right_coeff_subset h ((finite.mem_to_finset _).mp hb')) := by
                                apply Finset.ext; intro
                                rw [finite.mem_to_finset, Finset.mem_cons, finite.mem_to_finset]
                                exact ⟨fun hx => Or.imp_right
                                  (to_distrib_gens_right_coeff h · (distrib_gens_right_coeff_eq h' hx))
                                  (Finset.mem_cons.mp (distrib_gens_right_coeff_subset h' hx)),
                                (Or.elim · (fun hx => hx.symm ▸ to_distrib_gens_right_coeff h' (f.mem_cons_self hb) rfl)
                                  fun hx => to_distrib_gens_right_coeff h'
                                    (Finset.mem_cons_self' hb (distrib_gens_right_coeff_subset h hx))
                                    (distrib_gens_right_coeff_eq h hx))⟩
                          simp only [distrib_gens_right_coeff, h, h', dite_true, this, Finset.map_sum.cons]
                        rw [this]
                        exact congrArg (· + _) (Finset.map_sum.congr rfl (fun c hc => congrArg (· * c) (by
                          have ⟨he, hc⟩ := Finset.mem_erase.mp hc
                          have hcb : c ∈ distrib_gens_right hfb := heq ▸ hc
                          simp only [distrib_gens_right_coeff, hc, hcb, dite_true]
                          exact Finset.map_sum.congr (finite.to_finset_ext.mpr fun d =>
                            ⟨fun hd => to_distrib_gens_right_coeff hc ((Finset.mem_cons.mp
                              (distrib_gens_right_coeff_subset hcb hd)).resolve_left (fun h => by
                                subst h; exact he (distrib_gens_right_coeff_eq hcb hd).symm))
                              (distrib_gens_right_coeff_eq hcb hd),
                            fun hd => to_distrib_gens_right_coeff hcb (Finset.mem_cons_self' hb
                              (distrib_gens_right_coeff_subset hc hd))
                              (distrib_gens_right_coeff_eq hc hd)⟩) fun _ _ => rfl))) }
                      { have heq : distrib_gens_right hfb = (distrib_gens_right hf).cons (i * k) h := by
                          apply Finset.ext; intro
                          simp only [Finset.mem_cons, UnorderedList.mem_to_finset, UnorderedList.mem_pmap]
                          exact ⟨fun ⟨a, ha, hea⟩ => Or.imp
                              (fun ha => by subst ha; exact hea.symm)
                              (fun ha => ⟨a, ha, hea⟩) (Finset.mem_cons.mp ha),
                            (Or.elim · (fun ha => ⟨b, f.mem_cons_self hb, ha.symm⟩)
                              fun ⟨a, ha, hea⟩ => ⟨a, Finset.mem_cons_self' hb ha, hea⟩)⟩
                        rw [heq, Finset.map_sum.cons]
                        have hik : i * k ∈ distrib_gens_right hfb := UnorderedList.mem_to_finset.mpr
                          (UnorderedList.mem_pmap.mpr ⟨b, f.mem_cons_self hb, rfl⟩)
                        have : distrib_gens_right_coeff hfb ca (i * k) = ca b := by
                          simp only [distrib_gens_right_coeff, hik, dite_true]
                          have : (finite.subset (f.cons b hb).to_finite (distrib_gens_right_coeff_subset hik)).to_finset = Finset.singleton b := by
                            apply Finset.ext; intro c; rw [Finset.mem_singleton, finite.mem_to_finset]
                            exact ⟨fun hc => (Finset.mem_cons.mp (distrib_gens_right_coeff_subset hik hc)).resolve_right fun h' =>
                                h (UnorderedList.mem_to_finset.mpr (UnorderedList.mem_pmap.mpr ⟨c, h', distrib_gens_right_coeff_eq hik hc⟩)),
                              fun hc => by subst hc; exact to_distrib_gens_right_coeff hik (f.mem_cons_self hb) rfl⟩
                          rw [this, Finset.map_sum.singleton]
                        rw [this]
                        exact congrArg (· + _) (Finset.map_sum.congr rfl (fun c hc => congrArg (· * c)
                          (by
                            have hcb : c ∈ distrib_gens_right hfb := heq ▸ Finset.mem_cons_self' h hc
                            simp only [distrib_gens_right_coeff, hc, hcb, dite_true]
                            exact Finset.map_sum.congr (finite.to_finset_ext.mpr fun d =>
                              ⟨fun hd => have := distrib_gens_right_coeff_eq hcb hd
                                Or.elim (Finset.mem_cons.mp (distrib_gens_right_coeff_subset hcb hd))
                                  (fun hd' => by subst hd'; exact absurd (this ▸ hc) h)
                                  fun hd' => to_distrib_gens_right_coeff hc hd' this,
                              fun hd => to_distrib_gens_right_coeff hcb (Finset.mem_cons_self' hb
                                (distrib_gens_right_coeff_subset hc hd)) (distrib_gens_right_coeff_eq hc hd)⟩)
                              (fun _ _ => rfl)))) }
                  rw [h₁, h₂, add_assoc, add_left_comm (ca b * (i * j)), ←add_assoc,
                    ←mul_distrib_left, ←mul_distrib_left, choose_heq hfb (f.mem_cons_self hb)]) fa hfa⟩,
          fun ha =>
            let ⟨ij, hij, ik, hik, hijik⟩ := ha
            let ⟨fij, cij, hfij, hcij⟩ := from_set.mem_as_sum.mp hij
            let ⟨fik, cik, hfik, hcik⟩ := from_set.mem_as_sum.mp hik
            from_set.mem_as_sum.mpr ⟨fij ∪ fik, distrib_coeff fij fik cij cik,
              fun x hx => Or.elim (Finset.mem_union.mp hx)
                (fun hx => product_gen_subset I (Ideal.add.subset J K) (hfij hx))
                (fun hx => product_gen_subset I (Ideal.add.subset' J K) (hfik hx)),
              by
                rw [←hijik, hcij, hcik]
                exact @Finset.cons_induction _ (fun fij => fij.toSet ⊆ product_gen I J →
                  (∑ x in fij, cij x * x) + (∑ x in fik, cik x * x) =
                  ∑ x in fij ∪ fik, distrib_coeff fij fik cij cik x * x)
                  (fun _ => by
                    rw [Finset.map_sum.empty, zero_add, Finset.union_empty_left]
                    exact Finset.map_sum.congr rfl fun x hx => (congrArg (· * x)
                      (distrib_coeff_empty_left fik cij cik x)).symm)
                  (fun a s ha ih hs => by
                    rw [Finset.map_sum.cons, add_right_comm, ih (Subset.trans (s.cons_subset ha) hs)]
                    byCases ha' : a ∈ fik
                    { have ha'' : a ∈ s ∪ fik := Finset.mem_union.mpr (Or.inr ha')
                      have : (s.cons a ha) ∪ fik = s ∪ fik := by
                        apply Finset.ext; intro; simp only [Finset.mem_union, Finset.mem_cons]
                        exact ⟨(Or.elim · (Or.elim · (fun h => Or.inr (h ▸ ha')) Or.inl) Or.inr),
                          (Or.elim · (fun h => Or.inl (Or.inr h)) Or.inr)⟩
                      rw [this, Finset.map_sum.sum_term _ _ ha'', Finset.map_sum.sum_term _ _ ha'',
                        add_assoc, ←mul_distrib_right]
                      have : distrib_coeff s fik cij cik a + cij a = distrib_coeff (s.cons a ha) fik cij cik a := by
                        simp only [distrib_coeff, ha, ite_false, s.mem_cons_self ha, ite_true, ha', add_comm]
                      exact this ▸ congrArg (· + _) (Finset.map_sum.congr rfl fun x hx => congrArg (· * x) (by
                        have : x ∈ s ↔ x ∈ s.cons a ha := by simp only [Finset.mem_cons,
                          (Finset.mem_erase.mp hx).left, false_or]; exact Iff.rfl
                        simp only [distrib_coeff, this])) }
                    { have ha'' : a ∉ s ∪ fik := fun h => absurd (Finset.mem_union.mp h) (not_or_iff_and_not.mpr ⟨ha, ha'⟩);
                      have : (s.cons a ha) ∪ fik = (s ∪ fik).cons a ha'' := by
                        apply Finset.ext; intro; simp only [Finset.mem_union, Finset.mem_cons] exact Or.assoc.symm;
                      rw [this, Finset.map_sum.cons, distrib_coeff_only_left cij cik (s.mem_cons_self ha) ha']
                      exact congrArg (· + _) (Finset.map_sum.congr rfl fun x hx => congrArg (· * x) (by
                        have : x ≠ a := fun h => ha'' (h ▸ hx)
                        have : x ∈ s ↔ x ∈ s.cons a ha := by
                          simp only [Finset.mem_cons, this, false_or]; exact Iff.rfl
                        simp only [distrib_coeff, this])) }) fij hfij⟩⟩

    end product

    noncomputable instance IdealSemiring [Ring α] : Semiring (Ideal α) := Semiring.construct {
      add_zero         := fun I => add.of_subset (zero_ideal_in I)
      add_assoc        := add.assoc
      add_comm         := add.comm
      mul_one          := fun I => Ideal.antisymm
        (fun x hx => intersection.inter_one I ▸ product.subset_inter hx)
         fun x hx => product.mem.mpr fun K hK => hK ⟨x, hx, 1, trivial, (mul_one x).symm⟩
      mul_assoc        := product.assoc
      mul_distrib_left := product.distrib
      mul_zero         := fun I => in_zero_ideal (by
        have := @product.subset_inter _ _ I 0
        rw [intersection.inter_zero I] at this
        exact this)
      mul_comm         := product.comm
    }

    namespace product
      theorem pow_succ_subset [Ring α] (I : Ideal α) (n : Nat) : I ^ n.succ ⊆ I ^ n :=
        pow_nat_succ I n ▸ product.subset_left

      theorem pow_subset [Ring α] (I : Ideal α) (n : Nat) (hn : n ≠ 0) : I ^ n ⊆ I := by
        have : ∀ n : Nat, I ^ n.succ ⊆ I := fun n => by
          induction n with
          | zero      => exact Subset.refl I
          | succ n ih => exact Subset.trans (pow_succ_subset I n.succ) ih
        cases n; contradiction; exact this _

      theorem pow_contains [Ring α] (n : Nat) {I : Ideal α} {x : α} (hx : x ∈ I) : x ^ n ∈ I ^ n := by
        induction n with
        | zero      => trivial
        | succ n ih => rw [pow_nat_succ, pow_nat_succ]; exact from_set.contains_mem ⟨x ^ n, ih, x, hx, rfl⟩
    end product

    def ideal_quotient [Ring α] (I : Ideal α) (a : α) : Ideal α where
      subset     := {x | a * x ∈ I}
      has_zero   := ((mul_zero a).symm ▸ I.has_zero : a * 0 ∈ I)
      add_closed := by intro x y hx hy; exact (mul_distrib_left a x y ▸ I.add_closed hx hy : a * (x + y) ∈ I)
      mul_closed := by intro x y hy; exact (mul_left_comm x a y ▸ I.mul_closed x hy : a * (x * y) ∈ I)

    theorem ideal_quotient.subset [Ring α] (I : Ideal α) (a : α) : I ⊆ ideal_quotient I a :=
      fun _ => I.mul_closed a

    noncomputable def extension [Ring α] [Ring β] (f : α → β) (I : Ideal α) : Ideal β :=
      from_set (Function.image' f I.subset)

    theorem extension.subset [Ring α] [Ring β] (f : α → β) {I J : Ideal α} (h : I ⊆ J) :
      extension f I ⊆ extension f J := from_set.subset (Function.image'_subset f h)

    theorem extension_unit_of_surjective [Ring α] [Ring β] {f : α → β} (hfs : Function.surjective f) :
      extension f 1 = 1 :=
        let ⟨x, hx⟩ := hfs 1
        is_unit_ideal.mpr (from_set.contains_mem ⟨x, trivial, hx⟩)

    theorem extension_add [Ring α] [Ring β] (f : α →₊ β) (I J : Ideal α) : extension f (I + J) = extension f I + extension f.hom J :=
      Ideal.ext'.mpr fun x => ⟨fun hx => from_set.mem.mp hx (extension f.hom I + extension f.hom J) fun x ⟨y, ⟨i, hi, j, hj, hij⟩, hyx⟩ =>
        ⟨f i, from_set.contains_mem ⟨i, hi, rfl⟩, f j, from_set.contains_mem ⟨j, hj, rfl⟩, hyx ▸ hij ▸ (f.preserve_add i j).symm⟩,
      fun ⟨i, hi, j, hj, hij⟩ => hij ▸ (extension f.hom (I + J)).add_closed
        (extension.subset f.hom (Ideal.add.subset I J) hi) (extension.subset f.hom (Ideal.add.subset' I J) hj)⟩

    theorem extension_mul [Ring α] [Ring β] (f : α →ᵣ β) (I J : Ideal α) : extension f (I * J) = extension f I * extension f.hom J :=
      Ideal.ext'.mpr fun x => ⟨fun hx => from_set.mem.mp hx (extension f.hom I * extension f J) fun x ⟨y, hy, hyx⟩ =>
        hyx ▸ from_set.induction (fun y : α => f y ∈ extension f.hom I * extension f.hom J) hy
          (by simp only [f.preserve_zero]; exact (extension f.hom I * extension f.hom J).has_zero)
          (fun x ⟨i, hi, j, hj, hij⟩ => from_set.contains_mem ⟨f i, from_set.contains_mem ⟨i, hi, rfl⟩,
            f j, from_set.contains_mem ⟨j, hj, rfl⟩, hij ▸ f.preserve_mul i j⟩)
          (fun x y hx hy => by simp only [f.preserve_add]; exact (extension f.hom I * extension f.hom J).add_closed hx hy)
          (fun x y hy => by simp only [f.preserve_mul]; exact (extension f.hom I * extension f.hom J).mul_closed _ hy),
        fun hx => from_set.mem.mp hx (extension f (I * J)) (fun x ⟨i, hi, j, hj, hij⟩ =>
          let ⟨fI, cI, hfI, hcI⟩ := from_set.mem_as_sum.mp hi
          let ⟨fJ, cJ, hfJ, hcJ⟩ := from_set.mem_as_sum.mp hj
          let f' : Finset β → Finset β → Finset β := fun fI fJ =>
            ((fI.elems.product fJ.elems).map (fun ⟨i, j⟩ => i * j)).to_finset
          let c' : Finset β → Finset β → β → β := fun fI fJ x =>
            ∑ y in (fI.elems.product fJ.elems).to_finset.filter (fun y => y.fst * y.snd = x), cI y.fst * cJ y.snd
          from_set.mem_as_sum.mpr ⟨f' fI fJ, c' fI fJ, by
            intro x hx
            let ⟨⟨y₁, y₂⟩, hy, hyx⟩ := UnorderedList.map.mem_map.mp (UnorderedList.mem_to_finset.mp hx)
            have ⟨hyI, hyJ⟩ := UnorderedList.product.mem.mp hy
            let ⟨i, hi, hiy⟩ := hfI hyI
            let ⟨j, hj, hjy⟩ := hfJ hyJ
            exact ⟨i * j, from_set.contains_mem ⟨i, hi, j, hj, rfl⟩, by rw [←hyx, f.preserve_mul, hiy, hjy]⟩,
          by
            have : ∀ x, c' fI fJ x * x = ∑ y in (fI.elems.product fJ.elems).to_finset.filter (fun y => y.fst * y.snd = x),
              cI y.fst * y.fst * (cJ y.snd * y.snd) := fun x => by
                simp only [Finset.map_sum.sum_mul]; exact Finset.map_sum.congr rfl (fun y hy => by
                  rw [←(Finset.mem_filter.mp hy).right, mul_assoc, mul_left_comm (cJ y.snd), ←mul_assoc])
            rw [hij, hcI, hcJ, Finset.map_sum.mul_distrib, Finset.map_sum.congr rfl (fun x _ => this x), Finset.sum_distrib]
            have : (∑ x in (f' fI fJ), ((fI.elems.product fJ.elems).to_finset.filter (fun y => y.fst * y.snd = x)).elems).nodup :=
              UnorderedList.sum_nodup (UnorderedList.nodup_map_on
                (fun x hx y hy h =>
                  let ⟨⟨xi, xj⟩, hxij, hxe⟩ := UnorderedList.map.mem_map.mp (UnorderedList.mem_to_finset.mp hx)
                  have : (xi, xj) ∈ ((fI.elems.product fJ.elems).to_finset.filter (fun y' => y'.fst * y'.snd = y)).elems :=
                    h ▸ Finset.mem_filter.mpr ⟨UnorderedList.mem_to_finset.mpr  hxij, hxe⟩
                  (Finset.mem_filter.mp this).right ▸ hxe.symm) (Finset.val_nodup _))
                (fun s hs => let ⟨t, ht, hts⟩ := UnorderedList.map.mem_map.mp hs; hts ▸ Finset.val_nodup _)
                (fun s hs t ht hst x hxs hxt => hst (by
                  let ⟨s', hs', hse⟩ := UnorderedList.map.mem_map.mp hs
                  let ⟨t', ht', hte⟩ := UnorderedList.map.mem_map.mp ht
                  rw [←hse, ←hte]; rw [←hse] at hxs; rw [←hte] at hxt
                  let ⟨_, hse⟩ := Finset.mem_filter.mp hxs; let ⟨_, hte⟩ := Finset.mem_filter.mp hxt
                  rw [hse.symm.trans hte]))
            have : fI.elems.product fJ.elems = ∑ x in (f' fI fJ), ((fI.elems.product fJ.elems).to_finset.filter (fun y => y.fst * y.snd = x)).elems :=
              (UnorderedList.nodup_ext (UnorderedList.product.nodup fI.nodup fJ.nodup) this).mpr (fun ⟨x₁, x₂⟩ =>
                ⟨fun hx => UnorderedList.sum_mem.mpr ⟨((fI.elems.product fJ.elems).to_finset.filter (fun y => y.fst * y.snd = x₁ * x₂)).elems,
                  UnorderedList.map.mem_map.mpr ⟨x₁ * x₂, UnorderedList.mem_to_finset.mpr (UnorderedList.map.mem_map.mpr ⟨(x₁, x₂), hx, rfl⟩), rfl⟩,
                  Finset.mem_filter.mpr ⟨UnorderedList.mem_to_finset.mpr hx, rfl⟩⟩,
                fun hx => by
                  let ⟨l, hl, hxl⟩ := UnorderedList.sum_mem.mp hx
                  let ⟨y, hy, hyl⟩ := UnorderedList.map.mem_map.mp hl
                  rw [←hyl] at hxl; exact UnorderedList.mem_to_finset.mp (Finset.mem_filter.mp hxl).left⟩)
            exact UnorderedList.map_sum.congr this (fun _ _ => rfl)⟩)⟩

    theorem extension_pow [Ring α] [Ring β] (f : α →ᵣ β) (I : Ideal α) {n : Nat} (hn : n ≠ 0) : extension f (I ^ n) = extension f.hom I ^ n := by
      have : ∀ n : Nat, extension f (I ^ n.succ) = extension f.hom I ^ n.succ := fun n => by
        induction n with
        | zero      => rw [pow_nat_1, pow_nat_1]
        | succ n ih => rw [pow_nat_succ, extension_mul, ih, pow_nat_succ _ n.succ]
      cases n; contradiction; exact this _

    theorem extension_zero [Ring α] [Ring β] {f : α → β} {I : Ideal α} : extension f I = 0 ↔ I.subset ⊆ Function.fibre f 0 :=
      ⟨fun h x hx => by
        have : f x ∈ extension f I := from_set.contains_mem ⟨x, hx, rfl⟩
        rw [h] at this; exact this,
      fun h => Ideal.antisymm (from_set.zero_set _ ▸ from_set.subset (Subset.trans (Function.image'_subset f h)
        fun x ⟨y, hy, hyx⟩ => hyx ▸ hy)) (zero_ideal_in _)⟩

    abbrev preserve_mul_left [Ring α] [Ring β] (f : α →₋ β) : Prop := ∀ a b, ∃ c, f (a * b) = c * f b
  end Ideal

    open Ideal

    theorem RMulMap.preserve_mul_left [Ring α] [Ring β] (f : α →ᵣ β) : preserve_mul_left f.toGHomomorphism :=
      fun a b => ⟨f a, f.preserve_mul a b⟩
    theorem RHomomorphism.preserve_mul_left [Ring α] [Ring β] (f : α →ᵣ₁ β) : preserve_mul_left f.toGHomomorphism :=
      f.toRMulMap.preserve_mul_left

  namespace Ideal
    variable [Ring α] [Ring β] {f : α →₋ β} (hf : preserve_mul_left f)

    def contraction (I : Ideal β) : Ideal α where
      subset     := Function.inv_image f.hom I.subset
      has_zero   := (f.preserve_zero ▸ I.has_zero : _ ∈ I)
      add_closed := fun ha hb => (f.preserve_add _ _ ▸ I.add_closed ha hb : _ ∈ I)
      mul_closed := fun a b hb => let ⟨c, hc⟩ := hf a b; (hc ▸ I.mul_closed c hb : f (a * b) ∈ I)

    def contractionᵣ (f : α →ᵣ β) : Ideal β → Ideal α := contraction f.preserve_mul_left
    def contractionᵣ₁ (f : α →ᵣ₁ β) : Ideal β → Ideal α := contractionᵣ f.toRMulMap

    theorem contraction_unit : contraction hf 1 = 1 := is_unit_ideal.mpr trivial

    theorem contraction_image_unit {J : Ideal β} (hJ : f.image.subset ⊆ J.subset) : contraction hf J = 1 :=
      is_unit_ideal.mpr (hJ ⟨1, rfl⟩)

    theorem contraction.subset {I J : Ideal β} (h : I ⊆ J) :
      contraction hf I ⊆ contraction hf J := fun _ => (h ·)

    theorem contraction.proper_of_preserve_one (hf₁ : f 1 = 1) {I : Ideal β}
      (hI : I.proper_ideal) : (contraction hf I).proper_ideal :=
        proper_iff_1_notin.mpr fun h => proper_iff_1_notin.mp hI (hf₁ ▸ h)

    theorem extension_contraction (I : Ideal α) : I ⊆ contraction hf (extension f I) :=
      fun x hx => from_set.contains_mem ⟨x, hx, rfl⟩

    theorem contraction_extension (I : Ideal β) :
      extension f (contraction hf I) ⊆ I := from_set.ideal_contained fun x ⟨y, hy, hyx⟩ => hyx ▸ hy

    theorem extension_contraction_extension (I : Ideal α) :
      extension f I = extension f.hom (contraction hf (extension f I)) :=
        Ideal.antisymm (extension.subset f.hom (extension_contraction hf I))
          (contraction_extension hf (extension f.hom I))

    theorem contraction_extension_contraction (I : Ideal β) :
      contraction hf (extension f (contraction hf I)) = contraction hf I := 
        Ideal.antisymm (contraction.subset hf (contraction_extension hf I))
          (extension_contraction hf (contraction hf I))

    theorem contraction_extension_of_surjective (hfs : Function.surjective f.hom)
      (J : Ideal β) : J ⊆ extension f (contraction hf J) :=
        fun x hx => let ⟨y, hy⟩ := hfs x; from_set.contains_mem ⟨y, (hy ▸ hx : f y ∈ J), hy⟩

    theorem contraction_extension_eq_of_surjective (hfs : Function.surjective f.hom)
      (J : Ideal β) : extension f (contraction hf J) = J :=
        Ideal.antisymm (contraction_extension _ J) (contraction_extension_of_surjective hf hfs J)

    theorem contraction.of_subset_of_surjective (hfs : Function.surjective f.hom) {I J : Ideal β}
      (h : contraction hf I ⊆ contraction hf J) : I ⊆ J :=
        contraction_extension_eq_of_surjective hf hfs I ▸
          contraction_extension_eq_of_surjective hf hfs J ▸ extension.subset f.hom h

    theorem contraction_injective_of_contraction_extension (hf' : ∀ I, extension f (contraction hf I) = I) :
      Function.injective (contraction hf) := fun x y h => hf' x ▸ hf' y ▸ congrArg _ h

    theorem extension_injective_of_extension_contraction (hf' : ∀ I, contraction hf (extension f I) = I) :
      Function.injective (extension f.hom) := fun x y h => hf' x ▸ hf' y ▸ congrArg _ h

    theorem contraction_injective_of_surjective (hfs : Function.surjective f.hom) :
      Function.injective (contraction hf) :=
        contraction_injective_of_contraction_extension hf (contraction_extension_eq_of_surjective hf hfs)

    theorem extension_eq_image_of_left_surjective (f : α →₋ β) (hf : ∀ x y', ∃ x', f (x' * y') = x * f y') (I : Ideal α) :
      (extension f I).subset = Function.image' f.hom I.subset :=
        Set.ext.mp fun x => ⟨fun hx =>
          from_set.induction (fun x => x ∈ Function.image' f.hom I.subset) hx
            ⟨0, I.has_zero, f.preserve_zero⟩
            (fun _ => id)
            (fun x y ⟨x', hxI, hxe⟩ ⟨y', hyI, hye⟩ => ⟨x' + y', I.add_closed hxI hyI, by rw [f.preserve_add, hxe, hye]⟩)
            (fun x y ⟨y', hyI, hye⟩ =>
              let ⟨x', hx'⟩ := hf x y'
              ⟨x' * y', I.mul_closed x' hyI, by rw [←hye, hx']⟩), from_set.contains_mem⟩

    theorem extension_eq_image_of_surjective_mul_closed (f : α →ᵣ β) (hf : Function.surjective f.hom) (I : Ideal α) :
      (extension f I).subset = Function.image' f.hom I.subset :=
        extension_eq_image_of_left_surjective f.toGHomomorphism (fun x y' =>
          let ⟨x', hx'⟩ := hf x; ⟨x', hx' ▸ f.preserve_mul x' y'⟩) I

    theorem extension_contraction_eq_of_injective_eq_image {f : α →₋ β} (hf₁ : preserve_mul_left f)
      (hf₂ : Function.injective f.hom) (hf₃ : ∀ I, (extension f I).subset = Function.image' f.hom I.subset) (I : Ideal α) :
        contraction hf₁ (extension f I) = I :=
          Ideal.antisymm (fun x hx =>
            let ⟨y, hyI, hye⟩ := (Set.ext.mpr (hf₃ I) _).mp hx
            hf₂ hye ▸ hyI) (extension_contraction _ I)

    theorem extension_injective_of_injective_eq_image {f : α →₋ β} (hf₁ : preserve_mul_left f)
      (hf₂ : Function.injective f.hom) (hf₃ : ∀ I, (extension f I).subset = Function.image' f.hom I.subset) :
        Function.injective (extension f.hom) :=
          extension_injective_of_extension_contraction hf₁ (extension_contraction_eq_of_injective_eq_image hf₁ hf₂ hf₃)

    theorem extension_eq_image_of_isomorphism (f : α ≅ᵣ β) : ∀ I, (extension f I).subset = Function.image' f.hom I.subset :=
      extension_eq_image_of_left_surjective f.toGHomomorphism
        (fun x y =>
          let ⟨z, hz⟩ := f.toMIsomorphism.to_surjective x
          ⟨z, by rw [←hz, f.preserve_mul]⟩)

    theorem extension_contraction_eq_of_isomorphism (f : α ≅ᵣ β) : ∀ I, contractionᵣ f.toRMulMap (extension f I) = I :=
      extension_contraction_eq_of_injective_eq_image f.preserve_mul_left
        f.toMIsomorphism.to_injective (extension_eq_image_of_isomorphism f)

    theorem exists_kernel_element {f : α →ᵣ β} (hf : Function.surjective f.hom) {I J : Ideal α}
      (hIJ : I ⊊ J) (he : extension f.hom I = extension f.hom J) : ∃ x, x ∉ I ∧ x ∈ J ∧ x ∈ f.kernel :=
        let ⟨x, hxI, hxJ⟩ := hIJ.right
        have : f x ∈ extension f.hom I := he ▸ from_set.contains_mem ⟨x, hxJ, rfl⟩
        let ⟨fs, c, hfs, hc⟩ := from_set.mem_as_sum.mp this
        @Finset.cons_induction _ (fun fs : Finset β => fs.toSet ⊆ Function.image' f.hom I.subset →
          ∀ x, x ∉ I → x ∈ J → f x = (∑ x in fs, c x * x) → ∃ x, x ∉ I ∧ x ∈ J ∧ x ∈ f.kernel)
          (fun a x hxI hxJ hc => ⟨x, hxI, hxJ, (Finset.map_sum.empty _ ▸ hc : f x = 0)⟩)
          (fun a s ha ih hs x hxI hxJ hc =>
            let ⟨y, hyI, hye⟩ := hs (Finset.mem_cons_self s ha)
            let ⟨cy, hcy⟩ := hf (c a)
            have hcyy := I.mul_closed cy hyI
            ih (fun x hx => hs (Finset.mem_cons_self' ha hx)) (x - cy * y)
              (fun h => absurd (sub_add x _ ▸ I.add_closed h hcyy) hxI)
              (J.sub_closed hxJ (hIJ.left hcyy))
              (by rw [f.toGHomomorphism.preserve_sub, f.preserve_mul, hcy, hye,
                Group.sub_eq, hc, ←Finset.map_sum.cons])) fs hfs x hxI hxJ hc

    theorem extension_principal (f : α →ᵣ β) (a : α) : extension f (principal a) = principal (f a) :=
      Ideal.ext'.mpr fun x => ⟨(from_set.induction (· ∈ principal (f a)) ·
        (principal (f a)).has_zero
        (fun x ⟨y, ⟨z, hzy⟩, hyx⟩ => hyx ▸ hzy ▸ f.preserve_mul a z ▸ ⟨f z, rfl⟩)
        (fun x y ⟨x', hx'⟩ ⟨y', hy'⟩ => hx' ▸ hy' ▸ mul_distrib_left (f a) x' y' ▸ ⟨x' + y', rfl⟩)
        fun x y ⟨y', hy'⟩ => hy' ▸ mul_left_comm x (f a) y' ▸ ⟨x * y', rfl⟩),
      fun ⟨y, hy⟩ => hy ▸ (extension f (principal a)).mul_closed' (from_set.contains_mem ⟨a, generator_in_principal a, rfl⟩) y⟩

    theorem extension_from_set (s : Set α) : extension f (from_set s) = from_set (Function.image' f.hom s) :=
      Ideal.antisymm (from_set.ideal_contained (fun x ⟨y, hy, hyx⟩ =>
        hyx ▸ from_set.induction (f · ∈ from_set (Function.image' f.hom s)) hy
          (by simp only [f.preserve_zero]; exact (from_set (Function.image' f.hom s)).has_zero)
          (fun x hx t ⟨I, hI, hIt⟩ => hIt ▸ hI ⟨x, hx, rfl⟩)
          (fun x y => by simp only [f.preserve_add]; exact (from_set (Function.image' f.hom s)).add_closed)
          (fun x y hy => by let ⟨z, hz⟩ := hf x y; simp only [hz]; exact hz ▸
            (from_set (Function.image' f.hom s)).mul_closed z hy)))
        (from_set.subset (Function.image'_subset f.hom (from_set.contains_set s)))

    theorem extension_from_finset (fs : Finset α) : extension f (from_set fs.toSet) = from_set (fs.map f.hom).to_finset.toSet :=
      (extension_from_set hf fs.toSet).trans (congrArg _ (Set.ext.mp fun _ => Finset.map_mem.symm.trans UnorderedList.mem_to_finset.symm))
  end Ideal
end M4R
