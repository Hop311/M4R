import M4R.Algebra.Ring.Prod

namespace M4R
  open Monoid CommMonoid NCSemiring Semiring NCRing

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

    protected def image [Ring α] (I : Ideal α) (a : α) (p : a ∈ I) : ↑I.subset := ⟨a, p⟩
    protected theorem image_eq [Ring α] (I : Ideal α) (a b : ↑I.subset) :
      a = b ↔ Set.inclusion a = Set.inclusion b :=
        ⟨congrArg Set.inclusion, Set.elementExt⟩

    def ZeroIdeal (α : Type _) [Ring α] : Ideal α where
      subset := Set.SingletonSet.mk 0
      has_zero := rfl
      add_closed := fun xz yz => by rw [xz, yz, add_zero]; rfl
      mul_closed := fun _ _ h => by rw [h, mul_zero]; trivial

    def UnitIdeal (α : Type _) [Ring α] : Ideal α where
      subset := Set.Universal
      has_zero := trivial
      add_closed := by intros; trivial
      mul_closed := by intros; trivial

    instance ZeroIdeal.Zero [Ring α] : Zero (Ideal α) where zero := ZeroIdeal α
    instance UnitIdeal.One [Ring α] : One (Ideal α) where one := UnitIdeal α

    instance IdealAbelianGroup [r : Ring α] (I : Ideal α) : AbelianGroup ↑I.subset := AbelianGroup.construct
      {
        zero := ⟨0, I.has_zero⟩
        add := fun ⟨x, xs⟩ ⟨y, ys⟩ => ⟨x + y, I.add_closed xs ys⟩
        neg := fun ⟨x, xs⟩ => ⟨-x, I.neg_closed xs⟩
        add_zero  := fun ⟨a, _⟩ => by simp only [Ideal.image_eq]; exact r.add_zero a
        add_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => by simp only [Ideal.image_eq]; exact r.add_assoc a b c
        add_neg   := fun ⟨a, _⟩ => by simp only [Ideal.image_eq]; exact r.add_neg a
        add_comm  := fun ⟨a, _⟩ ⟨b, _⟩ => by simp only [Ideal.image_eq]; exact r.add_comm a b
      }

    protected def equivalent [Ring α] (I J: Ideal α) : Prop := I.subset = J.subset
    protected theorem ext [Ring α] : ∀ {I J : Ideal α}, Ideal.equivalent I J ↔ I = J
    | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ =>
      ⟨by intro eq; rw [Ideal.mk.injEq]; exact eq, by simp [Ideal.equivalent]; exact id⟩
    protected theorem ext' [Ring α] {I J : Ideal α} : I = J ↔ ∀ x, x ∈ I ↔ x ∈ J := by
      simp only [←Ideal.ext, Ideal.equivalent, ←Set.ext]; exact Iff.rfl
    protected theorem antisymm [Ring α] {I J : Ideal α} (h₁ : I ⊆ J) (h₂ : J ⊆ I) : I = J := by
      rw [←Ideal.ext]; simp only [Ideal.equivalent]; rw [←Set.ext]; simp only [Set.equivalent];
      exact fun x => ⟨fun h => h₁ h, fun h => h₂ h⟩

    protected def add [Ring α] (I J : Ideal α) : Ideal α where
      subset := {x | ∃ i ∈ I, ∃ j ∈ J, i + j = x }
      has_zero := ⟨0, I.has_zero, 0, J.has_zero, by rw [add_zero 0]⟩
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

      protected theorem of_subset [Ring α] {I J : Ideal α} (h : I ⊆ J) : I + J = J := by
        apply Ideal.antisymm
        intro x ⟨i, iI, j, jJ, hij⟩; rw [←hij]; exact J.add_closed (h iI) jJ
        rw [add.comm]; exact Ideal.add.subset J I

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
      subset := {x | a ÷ x}
      has_zero := divides_zero a;
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

    theorem in_unit_ideal [Ring α] (I : Ideal α) : I ⊆ 1 :=
      fun x _ => mem_unit_ideal x
    theorem unit_ideal_in [Ring α] {I : Ideal α} (hI : 1 ⊆ I) : I = 1 :=
      Ideal.antisymm (in_unit_ideal I) hI

    theorem zero_ideal_in [Ring α] (I : Ideal α) : 0 ⊆ I := fun x hx =>
      mem_zero_ideal.mp hx ▸ I.has_zero
    theorem in_zero_ideal [Ring α] {I : Ideal α} (hI : I ⊆ 0) : I = 0 :=
      Ideal.antisymm hI (zero_ideal_in I)

    theorem principal_in [Ring α] (I : Ideal α) : ∀ a ∈ I, principal a ⊆ I := by
      intro _ aI _ ⟨y, ayx⟩; rw [←ayx]; exact mul_closed' _ aI _;
    theorem unit_principal [Ring α] : ∀ {u}, isUnit u → principal u = (1 : Ideal α) := by
      intro u hu; exact Ideal.antisymm (in_unit_ideal _) (fun y _ => unit_divides u y hu);

    theorem is_unit_ideal' [Ring α] {I : Ideal α} : I = 1 ↔ ∃ x, isUnit x ∧ x ∈ I :=
      ⟨(· ▸ ⟨1, isUnit_1, trivial⟩), fun ⟨x, hx, hxI⟩ =>
        Ideal.antisymm (in_unit_ideal I) (unit_principal hx ▸ principal_in I x hxI)⟩
    theorem is_unit_ideal [Ring α] {I : Ideal α} : I = 1 ↔ 1 ∈ I :=
      is_unit_ideal'.trans ⟨fun ⟨x, ⟨y, hxy⟩, hxI⟩ => hxy ▸ I.mul_closed' hxI y, fun h => ⟨1, isUnit_1, h⟩⟩
    theorem is_zero_ideal [Ring α] {I : Ideal α} : I = 0 ↔ ∀ a ∈ I, a = 0 := by
      simp only [←Ideal.ext, Ideal.equivalent, ←Set.ext, Set.equivalent];
      exact propext_iff.mpr (forall_congr fun _ => propext ⟨Iff.mp, fun h => ⟨h, (· ▸ I.has_zero)⟩⟩)

    theorem div_mem [Ring α] {I : Ideal α} {a : α} : a ∈ I ↔ ∃ b ∈ I, b ÷ a :=
      ⟨fun h => ⟨a, h, divides_self a⟩, fun ⟨b, hb, c, hbc⟩ => hbc ▸ I.mul_closed' hb c⟩

    protected def intersection [Ring α] (I J : Ideal α) : Ideal α where
      subset := I.subset ∩ J.subset
      has_zero := ⟨I.has_zero, J.has_zero⟩
      add_closed := fun as bs => ⟨I.add_closed as.left bs.left, J.add_closed as.right bs.right⟩
      mul_closed := fun a _ bs => ⟨I.mul_closed a bs.left, J.mul_closed a bs.right⟩
    noncomputable instance IdealIntersection [Ring α] : Intersection (Ideal α) where intersection := Ideal.intersection

    namespace intersection

      protected theorem mem [Ring α] {I J : Ideal α} : ∀ a, a ∈ I ∩ J ↔ a ∈ I ∧ a ∈ J := fun _ => Iff.rfl

      protected theorem subset_left [Ring α] (I J : Ideal α) : I ∩ J ⊆ I := fun _ => And.left
      protected theorem subset_right [Ring α] (I J : Ideal α) : I ∩ J ⊆ J := fun _ => And.right
      
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
      subset := ⋂₀ S.toSetSet Ideal.subset
      has_zero := fun s ⟨I, IS, hIs⟩ => by rw [←hIs]; exact I.has_zero
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

    end sIntersection

    noncomputable def from_set [Ring α] (S : Set α) : Ideal α := ⋂₀ {I : Ideal α | S ⊆ I.subset}

    namespace from_set
      variable [Ring α] (S : Set α)

      theorem contains_set : S ⊆ (from_set S).subset :=
        Set.SoSIntersection.subset fun s ⟨I, hIS, hIs⟩ => hIs ▸ hIS
      
      variable {S}

      theorem contains_mem {a : α} (ha : a ∈ S) : a ∈ from_set S :=
        contains_set S ha

      theorem contains_principal {a : α} (ha : a ∈ S) : principal a ⊆ from_set S :=
        fun x ⟨b, hx⟩ => hx ▸ (from_set S).mul_closed' (contains_mem ha) b

      theorem ideal_contained {I : Ideal α} (hI : S ⊆ I.subset) : from_set S ⊆ I :=
        Set.SoSIntersection.subset_of_mem ⟨I, hI, rfl⟩

      theorem is_principal {a : α} : from_set (Set.SingletonSet.mk a) = principal a :=
        Ideal.antisymm (ideal_contained fun x hx => hx.symm ▸ generator_in_principal a)
          (contains_principal rfl)

      theorem contains_unit (h : ∃ a ∈ S, isUnit a) : from_set S = 1 :=
        let ⟨a, haS, ha⟩ := h
        unit_ideal_in (unit_principal ha ▸ contains_principal haS)

      theorem mem {a : α} : a ∈ from_set S ↔ ∀ I : Ideal α, S ⊆ I.subset → a ∈ I := by
        simp only [from_set, sIntersection.mem]; exact Iff.rfl

    end from_set

    protected noncomputable def product [Ring α] (I J : Ideal α) : Ideal α :=
      from_set {x | ∃ i ∈ I, ∃ j ∈ J, x = i * j}
    noncomputable instance IdealMul [Ring α] : Mul (Ideal α) where mul := Ideal.product

    namespace product

      protected theorem comm [Ring α] (I J : Ideal α) : I * J = J * I :=
        congrArg from_set (Set.ext.mp fun a =>
          ⟨fun ⟨i, hi, j, hj, hij⟩ => ⟨j, hj, i, hi, Semiring.mul_comm i j ▸ hij⟩,
          fun ⟨j, hj, i, hi, hji⟩ => ⟨i, hi, j, hj, Semiring.mul_comm j i ▸ hji⟩⟩)

      theorem mem [Ring α] {I J : Ideal α} {a : α} : a ∈ I * J ↔ ∀ K : Ideal α,
        ↑({x | ∃ i ∈ I, ∃ j ∈ J, x = i * j} : Set α) ⊆ K.subset → a ∈ K := by
          rw [←from_set.mem]; exact Iff.rfl

      theorem subset_inter [Ring α] {I J : Ideal α} : I * J ⊆ I ∩ J := fun x hx =>
        mem.mp hx (I ∩ J) fun x ⟨i, hi, j, hj, hxij⟩ => hxij ▸ ⟨I.mul_closed' hi j, J.mul_closed i hj⟩

      protected theorem assoc [Ring α] (I J K : Ideal α) : I * J * K = I * (J * K) := by
        apply Ideal.ext'.mpr; intro x
        rw [mem, mem]; apply propext_iff.mpr; apply forall_congr;
        intro L; apply propext
        sorry

    end product

    noncomputable instance IdealSemiring [Ring α] : Semiring (Ideal α) := Semiring.construct {
      add_zero         := fun I => add.comm 0 I ▸ add.of_subset (zero_ideal_in I)
      add_assoc        := add.assoc
      add_comm         := add.comm
      mul_one          := fun I => Ideal.antisymm
        (fun x hx => intersection.inter_one I ▸ product.subset_inter hx)
         fun x hx => product.mem.mpr fun K hK => hK ⟨x, hx, 1, trivial, (mul_one x).symm⟩
      mul_assoc        := product.assoc
      mul_distrib_left := sorry
      mul_zero         := fun I => in_zero_ideal (by
        have := @product.subset_inter _ _ I 0
        rw [intersection.inter_zero I] at this
        exact this)
      mul_comm         := product.comm
    }

    structure chain (α : Type _) [Ring α] where
      f        : Nat → Ideal α
      hsubsets : ∀ n, f n ⊆ f n.succ

    namespace chain
      variable [Ring α] (c : chain α)

      instance chain_coefun : CoeFun (chain α) (fun _ => Nat → Ideal α) where coe := f

      def is_stable : Prop := ∃ N : Nat, ∀ n, N ≤ n → c n = c N

    end chain
  end Ideal
end M4R
