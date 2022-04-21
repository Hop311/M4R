import M4R.Algebra.Ring.Matsumura

namespace M4R

  namespace Ideal
    structure chain (α : Type _) [Ring α] where
      f : Nat → Ideal α

    namespace chain
      variable [Ring α] (c : chain α)

      instance chain_coefun : CoeFun (chain α) (fun _ => Nat → Ideal α) where coe := f

      def ascending : Prop :=  ∀ n, c n ⊆ c n.succ

      def descending : Prop :=  ∀ n, c n.succ ⊆ c n

      def is_stable : Prop := ∃ N, ∀ n, N ≤ n → c n = c N

      def is_prime : Prop := ∀ n, (c n).is_prime

      def strict_infinite : Prop := ∀ n, c n ≠ c n.succ

      def strict_stable : Prop := ∃ N, (∀ n, n < N → c n ≠ c n.succ) ∧ (∀ n, N ≤ n → c n = c N)

      noncomputable def stable_length (hc : c.strict_stable) : Nat := Classical.choose hc

      theorem stable_length_spec (hc : c.strict_stable) : (∀ n, n < c.stable_length hc → c n ≠ c n.succ) ∧
        ∀ n, c.stable_length hc ≤ n → c n = c (c.stable_length hc) := Classical.choose_spec hc

      def strict : Prop := strict_stable c ∨ strict_infinite c

    end chain
  end Ideal

  open Ideal

  namespace Ring
    namespace krull_dim
      open Ideal

      structure krull_chain (α : Type _) [Ring α] extends chain α where
        hprime  : tochain.is_prime
        hascend : tochain.ascending

      structure strict_stable_chain (α : Type _) [Ring α] extends krull_chain α where
        hstrict_stab : tochain.strict_stable
      noncomputable def strict_stable_chain.length [Ring α] (c : strict_stable_chain α) : Nat :=
        c.stable_length c.hstrict_stab
      theorem strict_stable_chain.length_spec [Ring α] (c : strict_stable_chain α) :
        (∀ n, n < c.length → c.tochain n ≠ c.tochain n.succ) ∧ ∀ n, c.length ≤ n → c.tochain n = c.tochain c.length :=
          c.stable_length_spec c.hstrict_stab
      theorem strict_stable_chain.nonempty (α) [NonTrivialRing α] : Nonempty (strict_stable_chain α) :=
        let ⟨I, hI⟩ := Ideal.exists_prime_ideal α
        ⟨{
          f            := fun _ => I
          hprime       := fun _ => hI
          hascend      := fun _ => Subset.refl _
          hstrict_stab := ⟨0, fun _ => (absurd · (Nat.not_lt_zero _)), fun _ _ => rfl⟩
        }⟩

      def krull_dim_infinite (α : Type _) [Ring α] : Prop := (∃ c : krull_chain α, c.strict_infinite) ∨
        ∀ n, ∃ c : strict_stable_chain α, n ≤ c.length

      def has_krull_dim (α : Type _) [Ring α] : Prop := (∀ c : krull_chain α, ¬c.strict_infinite) ∧
        ∃ c : strict_stable_chain α, ∀ d : strict_stable_chain α, d.length ≤ c.length

      theorem has_krull_dim_iff_not_infinite [NonTrivialRing α] : has_krull_dim α ↔ ¬krull_dim_infinite α := by
        simp only [has_krull_dim, krull_dim_infinite, not_or_iff_and_not, not_forall, not_exists, Nat.not_le]
        apply Iff.and
        { rw [←not_exists, not_iff_not]; exact ⟨fun ⟨c, hc⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨c, hc⟩⟩ }
        { exact ⟨fun ⟨c, hc⟩ => ⟨c.length.succ, fun d => Nat.lt_succ_of_le (hc d)⟩,
          fun ⟨c, hc⟩ => by
            let ⟨I, hI⟩ := Ideal.exists_prime_ideal α
            let ⟨x, _, hx⟩ := maximal.max_exists (@Set.Universal (strict_stable_chain α))
              ⟨Classical.choice (strict_stable_chain.nonempty α), trivial⟩
              strict_stable_chain.length ⟨c, fun x _ => Nat.le_of_lt (hc x)⟩
            exact ⟨x, (hx · trivial)⟩⟩ }

      noncomputable def dim [Ring α] (h : has_krull_dim α) : Nat := (Classical.choose h.right).length

    end krull_dim
  end Ring

  namespace Ideal
    variable [Ring α] (I : Ideal α)
    open Ring.krull_dim

    structure height_chain extends chain α where
      hbase : f 0 = I
      hprime : tochain.is_prime
      hdescend : tochain.descending
    theorem height_chain.subset_base [Ring α] {I : Ideal α} (c : height_chain I) (n : Nat) : c.tochain n ⊆ I := by
      induction n with
      | zero      => rw [c.hbase]; exact Subset.refl I
      | succ n ih => exact Subset.trans (c.hdescend n) ih
    theorem height_chain.base_prime [Ring α] {I : Ideal α} (c : height_chain I) : I.is_prime :=
      c.hbase ▸ c.hprime 0

    structure stable_height_chain extends height_chain I where
      hstrict_stab : tochain.strict_stable
    noncomputable def stable_height_chain.length [Ring α] {I : Ideal α} (c : stable_height_chain I) : Nat :=
      c.stable_length c.hstrict_stab
    theorem stable_height_chain.length_spec [Ring α] {I : Ideal α} (c : stable_height_chain I) :
      (∀ n, n < c.length → c.tochain n ≠ c.tochain n.succ) ∧ ∀ n, c.length ≤ n → c.tochain n = c.tochain c.length :=
        c.stable_length_spec c.hstrict_stab
    def stable_height_chain.const (hI : I.is_prime) : stable_height_chain I where
      f            := fun _ => I
      hbase        := rfl
      hprime       := fun _ => hI
      hdescend      := fun _ => Subset.refl _
      hstrict_stab := ⟨0, fun _ => (absurd · (Nat.not_lt_zero _)), fun _ _ => rfl⟩
    theorem stable_height_chain.const_length (hI : I.is_prime) : (const I hI).length = 0 :=
      Classical.byContradiction fun h => (const I hI).length_spec.left 0 (Nat.zero_lt_iff_neq_zero.mpr h) rfl
    theorem stable_height_chain.nonempty (hI : I.is_prime) : Nonempty (stable_height_chain I) :=
      ⟨stable_height_chain.const I hI⟩

    def height_le (n : Nat) : Prop := (∀ c : height_chain I, ¬c.strict_infinite) ∧
      (∀ c : stable_height_chain I, c.length ≤ n) ∧ I.is_prime

    def height_ge (n : Nat) : Prop := (∃ c : height_chain I, c.strict_infinite) ∨
      ∃ c : stable_height_chain I, c.length ≥ n

    def height_eq (n : Nat) : Prop := I.height_le n ∧ ∃ c : stable_height_chain I, c.length = n

    theorem is_prime_of_height_le {n : Nat} (h : I.height_le n) : I.is_prime :=
      h.right.right

    theorem is_prime_of_height_ge {n : Nat} (h : I.height_ge n) : I.is_prime :=
      Or.elim h (fun ⟨c, _⟩ => c.base_prime) (fun ⟨c, _⟩ => c.base_prime)

    theorem is_prime_of_height_eq {n : Nat} (h : I.height_eq n) : I.is_prime :=
      I.is_prime_of_height_le h.left

    theorem height_antisymm (n : Nat) : I.height_eq n ↔ I.height_le n ∧ I.height_ge n :=
      ⟨(And.imp_right (fun h => let ⟨c, hc⟩ := h; Or.inr ⟨c, Nat.le_of_eq hc.symm⟩) ·),
      fun ⟨h₁, h₂⟩ => ⟨h₁,
        let ⟨c, hc⟩ := h₂.resolve_left (not_exists.mpr h₁.left)
        ⟨c, Nat.le_antisymm (h₁.right.left c) hc⟩⟩⟩

    theorem height_le_of_eq {n : Nat} : I.height_eq n → I.height_le n := And.left

    theorem height_ge_of_eq {n : Nat} (h : I.height_eq n) : I.height_ge n :=
      let ⟨c, hc⟩ := h.right
      Or.inr ⟨c, Nat.le_of_eq hc.symm⟩

    theorem height_ge_zero (hI : I.is_prime) : I.height_ge 0 :=
      Or.inr ⟨Classical.choice (stable_height_chain.nonempty I hI), Nat.zero_le _⟩

    theorem height_eq_zero : I.height_eq 0 ↔ I.minimal_prime_ideal_of 0 :=
      ⟨fun h => ⟨I.is_prime_of_height_eq h, I.zero_ideal_in, by
        intro J
        exact fun hJ h0 hJI => Classical.byContradiction fun hJI' =>
          let c : stable_height_chain I := {
            f            := fun n => match n with | 0 => I | n+1 => J
            hbase        := rfl
            hprime       := fun n => match n with | 0 => I.is_prime_of_height_eq h | n+1 => hJ
            hdescend     := fun n => match n with | 0   => hJI | n+1 => Subset.refl J
            hstrict_stab := ⟨1, fun n hn => by
                have : n = 0 := by cases n; rfl; contradiction
                subst this; exact Ne.symm hJI',
              fun n hn => by cases n; contradiction; rfl⟩
          }
          have h₁ := Nat.le_zero.mp (h.left.right.left c)
          have h₂ := c.length_spec.right 1 (h₁ ▸ Nat.zero_le 1)
          absurd (h₁ ▸ h₂ : c.tochain 1 = c.tochain 0) hJI'⟩,
      fun ⟨h₁, h₂, h₃⟩ => ⟨⟨fun c hc => absurd (h₃ (c.hprime 1) (Ideal.zero_ideal_in _)
        (fun x hx => c.hbase ▸ c.hdescend 0 hx)) fun h => (hc 0) (h.symm ▸ c.hbase),
        fun c => Classical.byContradiction fun h => (c.length_spec.left 0 (Nat.not_le.mp h)).symm
          (c.hbase.symm ▸ h₃ (c.hprime 1) (Ideal.zero_ideal_in _) (fun x hx => c.hbase ▸ c.hdescend 0 hx)), h₁⟩,
        stable_height_chain.const I h₁, stable_height_chain.const_length I h₁⟩⟩

    open localisation

    noncomputable def localise_height_chain [Ring α] {S : MultiplicativeSet α} {P : Ideal α} (hPS : Set.disjoint P.subset S.subset)
      (c : height_chain P) : height_chain (localise_ideal S P) where
        f        := fun n => localise_ideal S (c.tochain n)
        hbase    := by simp only; rw [c.hbase]
        hprime   := fun n => localise_ideal.prime (c.hprime n) (Set.disjoint.subset_left (c.subset_base n) hPS)
        hdescend := fun n => extension.subset _ (c.hdescend n)

    theorem localise_height_chain.imp_strict_infinite [Ring α] {S : MultiplicativeSet α} {P : Ideal α}
      (hPS : Set.disjoint P.subset S.subset) {c : height_chain P} (hc : c.strict_infinite) :
        (localise_height_chain hPS c).strict_infinite := fun n h => hc n (localise_ideal.prime_loc_deloc (c.hprime n)
          (Set.disjoint.subset_left (c.subset_base n) hPS) ▸ localise_ideal.prime_loc_deloc (c.hprime n.succ)
            (Set.disjoint.subset_left (c.subset_base n.succ) hPS) ▸ congrArg (delocalise_ideal S ·) h)

    noncomputable def localise_stable_height_chain [Ring α] {S : MultiplicativeSet α} {P : Ideal α} (hPS : Set.disjoint P.subset S.subset)
      (c : stable_height_chain P) : stable_height_chain (localise_ideal S P) where
        toheight_chain := localise_height_chain hPS c.toheight_chain
        hstrict_stab   := let ⟨N, hN₁, hN₂⟩ := c.hstrict_stab
          ⟨N, fun n hn hc => hN₁ n hn (localise_ideal.prime_loc_deloc (c.hprime n)
            (Set.disjoint.subset_left (c.subset_base n) hPS) ▸ localise_ideal.prime_loc_deloc (c.hprime n.succ)
            (Set.disjoint.subset_left (c.subset_base n.succ) hPS) ▸ congrArg (delocalise_ideal S ·) hc),
          fun n hn => congrArg (localise_ideal S ·) (hN₂ n hn)⟩

    theorem localise_stable_height_chain.preserve_length [Ring α] {S : MultiplicativeSet α} {P : Ideal α} (hPS : Set.disjoint P.subset S.subset)
      (c : stable_height_chain P) : c.length = (localise_stable_height_chain hPS c).length :=
        Nat.le_antisymm
          (Nat.not_lt.mp (mt (c.length_spec.left (localise_stable_height_chain hPS c).length) (iff_not_not.mpr
            (localise_ideal.prime_loc_deloc (c.hprime (localise_stable_height_chain hPS c).length) (Set.disjoint.subset_left
            (c.subset_base (localise_stable_height_chain hPS c).length) hPS) ▸ localise_ideal.prime_loc_deloc (c.hprime
            (localise_stable_height_chain hPS c).length.succ) (Set.disjoint.subset_left (c.subset_base
            (localise_stable_height_chain hPS c).length.succ) hPS) ▸ (congrArg (delocalise_ideal S ·)
            ((localise_stable_height_chain hPS c).length_spec.right (localise_stable_height_chain hPS c).length.succ (Nat.le_succ _))).symm))))
          (Nat.not_lt.mp (mt ((localise_stable_height_chain hPS c).length_spec.left c.length) (iff_not_not.mpr (congrArg
          (localise_ideal S ·) (c.length_spec.right c.length.succ (Nat.le_succ _)).symm))))

    theorem local_height_le [Ring α] {S : MultiplicativeSet α} {P : Ideal α} (hP : P.is_prime) (hPS : Set.disjoint P.subset S.subset)
      (n : Nat) (h : (localise_ideal S P).height_le n) : P.height_le n :=
        ⟨fun c hc => h.left (localise_height_chain hPS c) (localise_height_chain.imp_strict_infinite hPS hc),
        fun c => localise_stable_height_chain.preserve_length hPS c ▸ h.right.left (localise_stable_height_chain hPS c), hP⟩

  end Ideal

  structure NoetherianRing.ascending_chain (α : Type) [Ring α] extends chain α where
    hascend : tochain.ascending

  def Ring.is_noetherian (α : Type _) [Ring α] : Prop := ∀ c : NoetherianRing.ascending_chain α, c.is_stable

  class NoetherianRing (α : Type _) extends Ring α where
    noetherian : Ring.is_noetherian α

  namespace NoetherianRing
    open Classical

    noncomputable def no_maximal_seq [Ring α] {S : Set (Ideal α)} (hS : Nonempty S)
      (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) : Nat → Ideal α
    | 0   => (choice hS).val
    | n+1 => if hn : (no_maximal_seq hS h n) ∈ S then
        choose (h (no_maximal_seq hS h n) hn)
      else no_maximal_seq hS h n

    theorem no_maximal_seq_in_S [Ring α] {S : Set (Ideal α)} (hS : Nonempty S)
      (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) (n : Nat) : no_maximal_seq hS h n ∈ S := by
    induction n with
    | zero      => exact (choice hS).property
    | succ n ih =>
      simp only [no_maximal_seq, ih, dite_true]
      exact (choose_spec (h (no_maximal_seq hS h n) ih)).left

    theorem no_maximal_seq_def [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) (n : Nat) :
      no_maximal_seq hS h n.succ = choose (h (no_maximal_seq hS h n) (no_maximal_seq_in_S hS h n)) := by
        simp only [no_maximal_seq, no_maximal_seq_in_S hS h n]; rfl

    theorem no_maximal_seq_subsetneq [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) :
      (n : Nat) → no_maximal_seq hS h n ⊊ no_maximal_seq hS h n.succ
    | 0 => no_maximal_seq_def hS h 0 ▸ (choose_spec (h (no_maximal_seq hS h 0)
      (no_maximal_seq_in_S hS h 0))).right
    | n+1 => no_maximal_seq_def hS h n.succ ▸ (choose_spec (h (no_maximal_seq hS h n.succ)
      (no_maximal_seq_in_S hS h n.succ))).right

    theorem no_maximal_seq_subset [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) (n : Nat) :
      no_maximal_seq hS h n ⊆ no_maximal_seq hS h n.succ :=
        (no_maximal_seq_subsetneq hS h n).left

    theorem no_maximal_seq_neq [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) (n : Nat) :
      no_maximal_seq hS h n ≠ no_maximal_seq hS h n.succ :=
        (Ideal.subsetneq.mp (no_maximal_seq_subsetneq hS h n)).right

    theorem exists_maximal [NoetherianRing α] {S : Set (Ideal α)} (hS : Nonempty S) : ∃ I ∈ S, ∀ J ∈ S, I ⊆ J → J = I :=
      byContradiction fun h => by
      simp only [not_exists, not_and, not_forall] at h
      have h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J := fun I hI =>
        let ⟨J, hJ₁, hJ₂, hJ₃⟩ := h I hI
        ⟨J, hJ₁, Ideal.subsetneq.mpr ⟨hJ₂, Ne.symm hJ₃⟩⟩
      let c : ascending_chain α := {
        f        := no_maximal_seq hS h
        hascend := no_maximal_seq_subset hS h
      }
      let ⟨N, hN⟩ := NoetherianRing.noetherian c
      exact absurd (hN N.succ N.le_succ) (no_maximal_seq_neq hS h N).symm

    theorem ideal_finitely_generated [NoetherianRing α] (I : Ideal α) : I.finitely_generated :=
      let S : Set (Ideal α) := {J | J ⊆ I ∧ J.finitely_generated}
      let ⟨M, ⟨hM₁, hM₂⟩, hM₃⟩ := exists_maximal (⟨0, Ideal.zero_ideal_in I, finitely_generated.zero⟩ : Nonempty S)
      have : M = I := Ideal.antisymm hM₁ (fun x hx => by
        let ⟨f, hf⟩ := hM₂
        byCases hxf : x ∈ f.toSet
        { exact hf ▸ from_set.contains_mem hxf }
        { have := hM₃ (from_set (f.cons x hxf).toSet) ⟨from_set.ideal_contained fun y hy =>
            Or.elim (Finset.mem_cons.mp hy) (· ▸ hx) (fun hy => hM₁ (hf ▸ from_set.contains_mem hy)), _, rfl⟩
            (hf ▸ from_set.subset (Finset.cons_subset _ _));
          rw [←this]; apply from_set.contains_mem; exact Finset.mem_cons_self _ _ })
      this ▸ hM₂

    open localisation

    theorem minimal_prime_localisation [NoetherianRing α] {P I : Ideal α} (h : P.minimal_prime_ideal_of I)
      {S : MultiplicativeSet α} (hPS : Set.disjoint P.subset S.subset) :
        (localise_ideal S P).minimal_prime_ideal_of (localise_ideal S I) := by
          apply Classical.byContradiction; intro h'
          simp only [minimal_prime_ideal_of, not_and, not_forall] at h'
          let ⟨Q, hQ, hIQ, hQP₁, hQP₂⟩ := h' (localise_ideal.prime h.left hPS) (extension.subset _ h.right.left)
          let Q' : Ideal α := delocalise_ideal S Q
          apply iff_not_not.mpr h.right; simp only [not_and, not_forall]; intro
          exact ⟨Q', delocalise_ideal.prime S hQ, Subset.trans (I.extension_contraction (natural_hom S))
            (Ideal.contraction.subset (natural_hom S) hIQ), localise_ideal.prime_loc_deloc h.left hPS ▸
            Ideal.contraction.subset _ hQP₁, fun h' => hQP₂ (congrArg (localise_ideal S ·) h' ▸
            (delocalise_ideal.deloc_loc S Q).symm)⟩

    def delocalise_ascending_chain [Ring α] {S : MultiplicativeSet α} (c : ascending_chain (localisation S)) :
      ascending_chain α where
        f       := fun n => delocalise_ideal S (c.tochain n)
        hascend := fun n => contraction.subset _ (c.hascend n)

    theorem delocalise_ascending_chain.of_stable [Ring α] {S : MultiplicativeSet α} {c : ascending_chain (localisation S)} :
      (delocalise_ascending_chain c).is_stable → c.is_stable :=
        fun ⟨N, hN⟩ => ⟨N, fun n hn => delocalise_ideal.deloc_loc S (c.tochain n) ▸
          delocalise_ideal.deloc_loc S (c.tochain N) ▸ congrArg _ (hN n hn)⟩

    theorem localiastion_noetherian [NoetherianRing α] (S : MultiplicativeSet α) : Ring.is_noetherian (localisation S) :=
      fun c => delocalise_ascending_chain.of_stable (NoetherianRing.noetherian (delocalise_ascending_chain c))
    
    instance localisation_NoetherianRing [NoetherianRing α] (S : MultiplicativeSet α) : NoetherianRing (localisation S) where
      noetherian := localiastion_noetherian S

    theorem surjective_noetherian [NoetherianRing α] [Ring β] {f : α →ᵣ β} (hf : Function.surjective f.hom) :
      Ring.is_noetherian β := fun c =>
        let c' : ascending_chain α := {
          f       := fun n => contraction f (c.tochain n)
          hascend := fun n => contraction.subset _ (c.hascend n)
        }
        let ⟨N, hN⟩ := NoetherianRing.noetherian c'
        ⟨N, fun n hn => contraction_extension_eq_of_surjective hf (c.tochain n) ▸
          contraction_extension_eq_of_surjective hf (c.tochain N) ▸ congrArg _ (hN n hn)⟩

    open QuotientRing

    theorem quotient_noetherian [NoetherianRing α] (I : Ideal α) : Ring.is_noetherian (QClass I) :=
      surjective_noetherian (natural_hom.surjective I)

    instance quotient_NoetherianRing [NoetherianRing α] (I : Ideal α) : NoetherianRing (QClass I) where
      noetherian := quotient_noetherian I
  end NoetherianRing
end M4R
