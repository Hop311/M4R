import M4R.Algebra.Ring.Matsumura

namespace M4R

  namespace Ideal
    structure chain (α : Type _) [Ring α] where
      f : Nat → Ideal α

    namespace chain
      variable [Ring α] (c : chain α)

      instance chain_coefun : CoeFun (chain α) (fun _ => Nat → Ideal α) where coe := f

      protected theorem ext : ∀ {c₁ c₂ : chain α}, c₁ = c₂ ↔ ∀ n, c₁ n = c₂ n
      | ⟨_⟩, ⟨_⟩ => by rw [chain.mk.injEq, funext_iff]; exact Iff.rfl

      def ascending : Prop :=  ∀ n, c n ⊆ c n.succ

      def descending : Prop :=  ∀ n, c n.succ ⊆ c n

      def is_prime : Prop := ∀ n, (c n).is_prime

      def base (I : Ideal α) : Prop := c 0 = I

      theorem base_self : c.base (c 0) := rfl

      def is_stable : Prop := ∃ N, ∀ n, N ≤ n → c n = c N

      def strict_infinite : Prop := ∀ n, c n ≠ c n.succ

      def strict_stable : Prop := ∃ N, (∀ n, n < N → c n ≠ c n.succ) ∧ (∀ n, N ≤ n → c n = c N)

      noncomputable def stable_length (hc : c.strict_stable) : Nat := Classical.choose hc

      theorem stable_length_spec (hc : c.strict_stable) : (∀ n, n < c.stable_length hc → c n ≠ c n.succ) ∧
        ∀ n, c.stable_length hc ≤ n → c n = c (c.stable_length hc) := Classical.choose_spec hc

      def shift (n : Nat) : chain α where f := fun k => c (n + k)

      variable {c}

      theorem stable_length_eq (N : Nat) (hN₁ : ∀ n, n < N → c n ≠ c n.succ) (hN₂ : ∀ n, N ≤ n → c n = c N) :
        c.stable_length ⟨N, hN₁, hN₂⟩ = N :=
          let hc : c.strict_stable := ⟨N, hN₁, hN₂⟩
          Nat.le_antisymm (Nat.not_lt.mp (mt ((c.stable_length_spec hc).left N) (iff_not_not.mpr ((hN₂ N.succ (Nat.le_succ N)).symm))))
            (Nat.not_lt.mp (mt (hN₁ (c.stable_length hc)) (iff_not_not.mpr (((c.stable_length_spec hc).right _ (Nat.le_succ _)).symm))))

      theorem shift_ascending (n : Nat) (hc : c.ascending) : (c.shift n).ascending :=
        fun m => (Nat.add_succ n m ▸ hc (n + m) : c (n + m) ⊆ c (n + m.succ))
      theorem shift_descending (n : Nat) (hc : c.descending) : (c.shift n).descending :=
        fun m => (Nat.add_succ n m ▸ hc (n + m) : c (n + m.succ) ⊆ c (n + m))
      theorem shift_prime (n : Nat) (hc : c.is_prime) : (c.shift n).is_prime :=
        fun m => hc (n + m)
      theorem shift_base (c : chain α) (n : Nat) : (c.shift n).base (c n) := rfl
      theorem shift_is_stable (n : Nat) (hc : c.is_stable) : (c.shift n).is_stable := by
        let ⟨N, hN⟩ := hc
        byCases h : n < N
        { exact ⟨N - n, fun m hm => (hN (n + m) (Nat.add_comm m n ▸ Nat.sub_le_iff_right.mp hm)).trans
          (congrArg c.f (Nat.add_sub_of_le (Nat.le_of_lt h))).symm⟩ }
        { exact ⟨0, fun m hm => have h := Nat.not_lt.mp h;
            (hN (n + m) (Nat.le_trans h (Nat.le_add_right n m))).trans (hN n h).symm⟩ }
      theorem shift_strict_infinite (n : Nat) (hc : c.strict_infinite) : (c.shift n).strict_infinite :=
        fun m => hc (n + m)
      theorem shift_strict_stable (n : Nat) (hc : c.strict_stable) : (c.shift n).strict_stable := by
        let ⟨N, hN₁, hN₂⟩ := hc
        byCases h : n < N
        { exact ⟨N - n, fun m hm => hN₁ (n + m) (Nat.add_comm m n ▸ (Nat.lt_sub_iff_right (Nat.le_of_lt h)).mp hm),
            fun m hm => (hN₂ (n + m) (Nat.add_comm n m ▸ Nat.sub_le_iff_right.mp hm)).trans (congrArg c.f
              (Nat.add_sub_of_le (Nat.le_of_lt h))).symm⟩ }
        { exact ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m), fun m hm =>
            have h := Nat.not_lt.mp h;
            (hN₂ (n + m) (Nat.le_trans h (Nat.le_add_right n m))).trans (hN₂ n h).symm⟩ }

      theorem subset_ascending (hc : c.ascending) {m n : Nat} (h : m ≤ n) : c m ⊆ c n :=
        have : ∀ n, c m ⊆ c (m + n) := fun n => by
          induction n with
          | zero      => exact Subset.refl _
          | succ n ih => exact Nat.add_succ m n ▸ Subset.trans ih (hc (m + n))
        let ⟨k, hk⟩ := Nat.le.dest h
        hk ▸ this k
      theorem subset_descending (hc : c.descending) {m n : Nat} (h : m ≤ n) : c n ⊆ c m :=
        have : ∀ n, c (m + n) ⊆ c m := fun n => by
          induction n with
          | zero      => exact Subset.refl _
          | succ n ih => exact Nat.add_succ m n ▸ Subset.trans (hc (m + n)) ih
        let ⟨k, hk⟩ := Nat.le.dest h
        hk ▸ this k

      theorem subset_base {I : Ideal α} (hc₁ : c.base I) (hc₂ : c.descending) (n : Nat) : c n ⊆ I :=
        hc₁ ▸ subset_descending hc₂ (Nat.zero_le n)
      theorem base_subset {I : Ideal α} (hc₁ : c.base I) (hc₂ : c.ascending) (n : Nat) : I ⊆ c n :=
        hc₁ ▸ subset_ascending hc₂ (Nat.zero_le n)
      theorem base_prime {I : Ideal α} (hc₁ : c.base I) (hc₂ : c.is_prime) : I.is_prime :=
        hc₁ ▸ hc₂ 0

      theorem subsetneq_succ_of_strict_infinite_descending (hc₁ : c.strict_infinite) (hc₂ : c.descending) (n : Nat) :
        c n.succ ⊊ c n := Ideal.subsetneq.mpr ⟨hc₂ n, (hc₁ n).symm⟩
      theorem subsetneq_lt_of_strict_infinite_descending (hc₁ : c.strict_infinite) (hc₂ : c.descending) {m n : Nat} (h : m < n) :
        c n ⊊ c m := ProperSubset.trans_right (subset_descending hc₂ h)
          (subsetneq_succ_of_strict_infinite_descending hc₁ hc₂ m)

      theorem is_stable_of_strict_stable : c.strict_stable → c.is_stable :=
        fun ⟨N, hN⟩ => ⟨N, hN.right⟩

      theorem length_zero_of_strict_stable_0_eq_1 (hc : c.strict_stable) (h01 : c 0 = c 1) : c.stable_length hc = 0 :=
        Nat.le_zero.mp (Nat.not_lt.mp (mt ((c.stable_length_spec hc).left 0) (iff_not_not.mpr h01)))

      def length_infinite (S : Set (chain α)) : Prop :=
        (∃ c ∈ S, c.strict_infinite) ∨
          ∀ n, ∃ (c : chain α) (hc : c.strict_stable), c ∈ S ∧ n ≤ c.stable_length hc

      def length_finite (S : Set (chain α)) : Prop :=
        (∀ c ∈ S, ¬c.strict_infinite) ∧ ∃ (c : chain α) (hc : c.strict_stable), c ∈ S ∧
          ∀ (d : chain α) (hd : d.strict_stable), d ∈ S → d.stable_length hd  ≤ c.stable_length hc

      theorem length_finite_iff_not_infinite {S : Set (chain α)} (hS : ∃ c ∈ S, c.strict_stable) :
        length_finite S ↔ ¬length_infinite S := by
          simp only [chain.length_finite, chain.length_infinite, not_or_iff_and_not, not_exists, not_forall, not_and, Nat.not_le]
          exact Iff.and (forall_congr' fun _ => Iff.rfl)
            ⟨fun ⟨c, hstab, _, hmax⟩ => ⟨(c.stable_length hstab).succ, fun d hd₁ hd₂ => Nat.lt_succ_of_le (hmax d hd₁ hd₂)⟩,
              fun ⟨N, hN⟩ =>
                let ⟨⟨c, hc⟩, hcS, hmax⟩ := maximal.max_exists {c : Subtype chain.strict_stable | c.val ∈ S}
                  (let ⟨c, hcS, hstab⟩ := hS; ⟨⟨c, hstab⟩, hcS⟩) (fun ⟨c, hc⟩ => c.stable_length hc)
                  ⟨N, fun ⟨c, hc⟩ hcS => Nat.le_of_lt (hN c hc hcS)⟩
                ⟨c, hc, hcS, fun d hd => hmax ⟨d, hd⟩⟩⟩

      open NCSemiring

      theorem NonTrivial_of_length_infinite {S : Set (chain α)} (h : length_infinite S) : Ring.is_NonTrivial α :=
      fun h10 =>
        have : ∀ x : α, x = 0 := fun x => by rw [←mul_one x, h10, mul_zero]
        have : ∀ I J : Ideal α, I = J := fun I J =>
          Ideal.ext.mp (Set.ext.mp fun _ => by simp only [this, I.has_zero, J.has_zero])
        h.elim (fun ⟨c, hcS, hc⟩ => absurd (this _ _) (hc 0)) fun hc =>
          let ⟨c, hc, hcS, hc'⟩ := hc 1; absurd (this _ _) ((c.stable_length_spec hc).left 0 hc')

      theorem field_not_strict_infinite_of_descending (h : Ring.is_Field α) {c : chain α}
        (hdesc : c.descending) : ¬c.strict_infinite := fun hc => by
          have : ∀ n, c n = 1 := fun n => (Ring.ideal_0_or_1 h (c n)).resolve_left
            fun h => hc n (in_zero_ideal (h ▸ hdesc n : c n.succ ⊆ 0) ▸ h)
          apply hc 0; rw [this 0, this 1]

      theorem field_strict_stable_length_le_1_of_descending (h : Ring.is_Field α) {c : chain α}
        (hdesc : c.descending) (hc : c.strict_stable) : c.stable_length hc ≤ 1 :=
          Nat.not_lt.mp (mt ((c.stable_length_spec hc).left 1) (iff_not_not.mpr ((Ring.ideal_0_or_1 h (c 0)).elim
            (fun h₀₀ => have : ∀ n, c n = 0 := fun n => in_zero_ideal (h₀₀ ▸ c.subset_base c.base_self hdesc n)
              (this 1).trans (this 2).symm)
            fun h₀₁ => (Ring.ideal_0_or_1 h (c 1)).elim
              (fun h₁₀ => h₁₀.trans (in_zero_ideal (h₁₀ ▸ hdesc 1)).symm)
              fun h₁₁ => have := length_zero_of_strict_stable_0_eq_1 hc (h₀₁.trans h₁₁.symm)
                h₁₁.trans (h₀₁.symm.trans (this ▸ ((c.stable_length_spec hc).right 2 (this ▸ Nat.zero_le 2)).symm)))))

      theorem field_length_finite_of_descending (h : Ring.is_Field α) {S : Set (chain α)} (hS₁ : ∃ c ∈ S, c.strict_stable)
        (hS₂ : S ⊆ {c | c.descending}) : length_finite S :=
          (length_finite_iff_not_infinite hS₁).mpr fun hinf => hinf.elim
            (fun ⟨c, hcS, hc⟩ => absurd hc (field_not_strict_infinite_of_descending h (hS₂ hcS)))
            fun h' => by
              let ⟨c, hc, hcS, hc2⟩ := h' 2
              have := Nat.le_trans hc2 (field_strict_stable_length_le_1_of_descending h (hS₂ hcS) hc)
              contradiction

      open Classical

      noncomputable def length_of_finite {S : Set (chain α)} (h : length_finite S) : Nat :=
        (choose h.right).stable_length (choose (choose_spec h.right))

      def const_chain (I : Ideal α) : chain α := ⟨fun _ => I⟩

      theorem const_chain.ascending (I : Ideal α) : (const_chain I).ascending :=
        fun _ => Subset.refl I
      theorem const_chain.descending (I : Ideal α) : (const_chain I).descending :=
        fun _ => Subset.refl I
      theorem const_chain.is_prime {I : Ideal α} (hI : I.is_prime) : (const_chain I).is_prime :=
        fun _ => hI
      theorem const_chain.base (I : Ideal α) : (const_chain I).base I := rfl
      theorem const_chain.strict_stable (I : Ideal α) : (const_chain I).strict_stable :=
        ⟨0, fun _ => (absurd · (Nat.not_lt_zero _)), fun _ _ => rfl⟩
      theorem const_chain.is_stable (I : Ideal α) : (const_chain I).is_stable :=
        is_stable_of_strict_stable (const_chain.strict_stable I)
      theorem const_chain.length (I : Ideal α) : (const_chain I).stable_length (const_chain.strict_stable I) = 0 :=
        byContradiction fun h => ((const_chain I).stable_length_spec
          (const_chain.strict_stable I)).left 0 (Nat.zero_lt_iff_neq_zero.mpr h) rfl

      theorem const_chain.of_length_zero {hc₁ : c.strict_stable} (hc₂ : c.stable_length hc₁ = 0) : c = const_chain (c 0) :=
        chain.ext.mpr fun n => hc₂ ▸ (c.stable_length_spec hc₁).right n (hc₂ ▸ Nat.zero_le n)
      theorem const_chain.of_0_eq_1 (hc : c.strict_stable) (h01 : c 0 = c 1) : c = const_chain (c 0) :=
        of_length_zero (length_zero_of_strict_stable_0_eq_1 hc h01)

      section contract_chain
        variable [Ring α] [Ring β] {f : α →₋ β} (hf : Ideal.preserve_mul_left f)

        def contract_chain (c : chain β) : chain α := ⟨fun n => contraction hf (c n)⟩

        theorem contract_chain.ascending {c : chain β} (hc : c.ascending) : (contract_chain hf c).ascending :=
          fun n => contraction.subset hf (hc n)
        theorem contract_chain.descending {c : chain β} (hc : c.descending) : (contract_chain hf c).descending :=
          fun n => contraction.subset hf (hc n)
        theorem contract_chain.is_prime {f : α →ᵣ₁ β} {c : chain β} (hc : c.is_prime) :
          (contract_chain f.preserve_mul_left c).is_prime := fun n => contraction_prime f (hc n)
        theorem contract_chain.is_stable {c : chain β} : c.is_stable → (contract_chain hf c).is_stable :=
          fun ⟨N, hN⟩ => ⟨N, fun n hn => congrArg (contraction hf) (hN n hn)⟩
        theorem contract_chain.base {c : chain β} {I : Ideal β} (hc : c.base I) :
          (contract_chain hf c).base (contraction hf I) := congrArg (contraction hf) hc

        variable (hfs : Function.surjective f.hom)

        theorem contract_chain.is_stable_of_surjective {c : chain β} : (contract_chain hf c).is_stable → c.is_stable :=
          fun ⟨N, hN⟩ => ⟨N, fun n hn => contraction_injective_of_surjective hf hfs (hN n hn)⟩
        theorem contract_chain.strict_infinite_of_surjective {c : chain β} (hc : c.strict_infinite) :
          (contract_chain hf c).strict_infinite :=
            fun n h => hc n (contraction_injective_of_surjective hf hfs h)
        theorem contract_chain.strict_stable_of_surjective {c : chain β} (hc : c.strict_stable) :
          (contract_chain hf c).strict_stable :=
            let ⟨N, hN₁, hN₂⟩ := hc
            ⟨N, fun n hn h => hN₁ n hn (contraction_injective_of_surjective hf hfs h),
              fun n hn => congrArg (contraction hf) (hN₂ n hn)⟩

        theorem contract_chain.stable_length_eq_of_surjective {c : chain β} (hc : c.strict_stable) :
          c.stable_length hc = (contract_chain hf c).stable_length (contract_chain.strict_stable_of_surjective hf hfs hc) :=
            have hc' := contract_chain.strict_stable_of_surjective hf hfs hc
            Nat.le_antisymm (Nat.not_lt.mp (mt ((c.stable_length_spec hc).left ((contract_chain hf c).stable_length hc'))
              (iff_not_not.mpr (contraction_injective_of_surjective hf hfs (((contract_chain hf c).stable_length_spec hc').right
              _ (Nat.le_succ _)).symm))))
            (Nat.not_lt.mp (mt (((contract_chain hf c).stable_length_spec hc').left (c.stable_length hc)) (iff_not_not.mpr
              (congrArg (contraction hf) ((c.stable_length_spec hc).right _ (Nat.le_succ _)).symm))))

        theorem contract_chain.length_infinite {S : Set (chain β)}
          (hS : length_infinite S) : length_infinite (Function.image' (contract_chain hf) S) :=
            Or.imp (fun ⟨c, hcS, hc⟩ => ⟨contract_chain hf c, ⟨c, hcS, rfl⟩,
              contract_chain.strict_infinite_of_surjective hf hfs hc⟩)
              (fun h n => let ⟨c, hc, hcS, hcn⟩ := h n
                ⟨contract_chain hf c, contract_chain.strict_stable_of_surjective hf hfs hc,
                ⟨c, hcS, rfl⟩, contract_chain.stable_length_eq_of_surjective hf hfs hc ▸ hcn⟩) hS
      end contract_chain
      section extend_chain
        variable [Ring α] [Ring β] (f : α → β)

        noncomputable def extend_chain (c : chain α) : chain β := ⟨fun n => extension f (c n)⟩

        theorem extend_chain.ascending {c : chain α} (hc : c.ascending) : (extend_chain f c).ascending :=
          fun n => extension.subset f (hc n)
        theorem extend_chain.descending {c : chain α} (hc : c.descending) : (extend_chain f c).descending :=
          fun n => extension.subset f (hc n)
        theorem extend_chain.base {c : chain α} {I : Ideal α} (hc : c.base I) :
          (extend_chain f c).base (extension f I) := congrArg (extension f) hc

        theorem extension_contraction_of_isomorphism (c : chain α) (f : α ≅ᵣ β) :
          contract_chain f.preserve_mul_left (extend_chain f.hom c) = c :=
            chain.ext.mpr fun n => extension_contraction_eq_of_isomorphism f (c n)
      end extend_chain

      private noncomputable def strict_increasing_index [Ring α] {c : chain α} (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) : Nat → Nat
      | 0   => 0
      | n+1 => choose (h (strict_increasing_index h n))
      private theorem strict_increasing_index.idx_strict [Ring α] {c : chain α} (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (n : Nat) :
        strict_increasing_index h n < strict_increasing_index h n.succ :=
          Nat.lt_of_le_and_ne (choose (choose_spec (h (strict_increasing_index h n))))
            fun h' => choose_spec (choose_spec (h (strict_increasing_index h n))) (congrArg _ h'.symm)
      private theorem strict_increasing_index.strict [Ring α] {c : chain α} (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (n : Nat) :
        c (strict_increasing_index h n) ≠ c (strict_increasing_index h n.succ) :=
          (choose_spec (choose_spec (h (strict_increasing_index h n)))).symm

      private noncomputable def strictified [Ring α] {c : chain α} (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) : chain α where
        f := fun n => match n with
        | 0   => 1
        | n+1 => c (strict_increasing_index h (if c 0 = 1 then n.succ else n))
      private theorem strictified.base [Ring α] {c : chain α} (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) : (strictified h).base 1 := rfl
      private theorem strictified.base1 [Ring α] {c : chain α} (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (h0 : c 0 = 1) :
        ∀ n, strictified h n = c (strict_increasing_index h n)
      | 0   => base h ▸ h0.symm
      | n+1 => by simp only [strictified, h0, ite_true]; rfl
      private theorem strictified.not_base1 [Ring α] {c : chain α} (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (h0 : c 0 ≠ 1) (n : Nat) :
        strictified h n.succ = c (strict_increasing_index h n) := by simp only [strictified, h0, ite_false]
      private theorem strictified.descending [Ring α] {c : chain α} (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (hc : c.descending) : (strictified h).descending :=
        fun n => by
          byCases h0 : c 0 = 1
          { simp only [base1 h h0]; exact chain.subset_descending hc (Nat.le_of_lt (strict_increasing_index.idx_strict h n)) }
          { match n with
            | 0   => exact in_unit_ideal _
            | n+1 => simp only [not_base1 h h0]; exact chain.subset_descending hc (Nat.le_of_lt
              (strict_increasing_index.idx_strict h n)) }
      private theorem strictified.strict_infinite [Ring α] {c : chain α} (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) : (strictified h).strict_infinite :=
        fun n => by
          byCases h0 : c 0 = 1
          { simp only [base1 h h0]; exact strict_increasing_index.strict h n }
          { simp only [not_base1 h h0]
            match n with
            | 0   => exact Ne.symm h0
            | n+1 => simp only [not_base1 h h0]; exact strict_increasing_index.strict h n }

      section strict_index
        -- i.e. `k` greater than previous index `n`, representing different ideal from `c n`,
        -- less than `m` (to avoid jumping past `m`) and different ideal from `c m` (to make sure we go to `m`, rather than an
        -- earlier ideal in the same block (we assume you never have the same ideal appear twice with any distinct ideals in between)
        abbrev next_term (c : chain α) (m n : Nat) : Prop := Nonempty ({k | n < k ∧ c n ≠ c k ∧ k < m ∧ ∀ l, l ≤ k → c l ≠ c m} : Set Nat)

        theorem next_term_ext {c : chain α} {m n N : Nat} (h : n < N ∧ c n ≠ c N ∧ N < m ∧ ∀ l, l ≤ N → c l ≠ c m) (hmin : ∀ k, n < k ∧ c n ≠ c k ∧
          k < m ∧ (∀ l, l ≤ k → c l ≠ c m) → N ≤ k) : choose (minimal.min_exists _ (⟨N, h⟩ : next_term c m n) id) = N :=
            let m := minimal.min_exists _ (⟨N, h⟩ : next_term c m n) id
            Nat.le_antisymm ((choose_spec m).right N h) (hmin (choose m) (choose_spec m).left)
        theorem not_next_term_m (c : chain α) (m : Nat) : ¬ next_term c m m := fun ⟨_, h₁, _, h₂, _⟩ => Nat.lt_not_symm ⟨h₁, h₂⟩

        -- index of `n`ᵗʰ unique ideal in chain `c` (stabilised such that `c (m+k) = c m` for all `k`)
        noncomputable def strict_index (c : chain α) (m : Nat) : Nat → Nat
        | 0   => if c 0 = c m then m else 0
        | n+1 => if h : next_term c m (strict_index c m n) then choose (minimal.min_exists _ h id) else m

        theorem strict_index.def_zero_m {c : chain α} {m : Nat} (h : c 0 = c m) : strict_index c m 0 = m := by
          simp only [strict_index, h, ite_true]
        theorem strict_index.def_zero_0 {c : chain α} {m : Nat} (h : c 0 ≠ c m) : strict_index c m 0 = 0 := by
          simp only [strict_index, h, ite_false]
        theorem strict_index.zero_or_m (c : chain α) (m : Nat) : strict_index c m 0 = 0 ∨ strict_index c m 0 = m := by
          byCases h : c 0 = c m
          { exact Or.inr (def_zero_m h) }
          { exact Or.inl (def_zero_0 h) }
        theorem strict_index.c_zero (c : chain α) (m : Nat) : c (strict_index c m 0) = c 0 := by
          byCases h : c 0 = c m
          { exact (congrArg (c ·) (def_zero_m h)).trans h.symm }
          { exact (congrArg (c ·) (def_zero_0 h)) }
        theorem strict_index.def_exists {c : chain α} {m n : Nat} (h : next_term c m (strict_index c m n)) :
          strict_index c m n.succ = choose (minimal.min_exists _ h id) := by simp only [strict_index, h, dite_true]
        theorem strict_index.neq_m_of_exists {c : chain α} {m n : Nat} (h : next_term c m (strict_index c m n)) :
          strict_index c m n.succ ≠ m :=
            def_exists h ▸ Nat.ne_of_lt (choose_spec (minimal.min_exists _ h id)).left.right.right.left
        theorem strict_index.def_not_exists {c : chain α} {m n : Nat} (h : ¬next_term c m (strict_index c m n)) :
          strict_index c m n.succ = m := by simp only [strict_index, h, dite_false]

        theorem strict_index.spec (c : chain α) (m n : Nat) : strict_index c m n.succ = m ∨
          (strict_index c m n < strict_index c m n.succ ∧ c (strict_index c m n) ≠ c (strict_index c m n.succ) ∧
          strict_index c m n.succ < m ∧ (∀ l, l ≤ strict_index c m n.succ → c l ≠ c m) ∧
          ∀ k, strict_index c m n ≤ k → k < strict_index c m n.succ → c k = c (strict_index c m n)) := by
            byCases h : next_term c m (strict_index c m n)
            { apply Or.inr;
              have hmin := minimal.min_exists _ h id
              have ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ := choose_spec hmin;
              rw [def_exists h];
              exact ⟨h₁, h₂, h₃, h₄, fun k hk₁ hk₂ => (Nat.lt_or_eq_of_le hk₁).elim
                (fun hk₁ => byContradiction fun h => have hkm := Nat.lt_trans hk₂ h₃; absurd (h₅ k ⟨hk₁, Ne.symm h, hkm, fun l hl =>
                  h₄ l (Nat.le_trans hl (Nat.le_of_lt hk₂))⟩) (Nat.not_le.mpr hk₂))
                fun h => by rw [h]⟩ }
            { exact Or.inl (strict_index.def_not_exists h) }
        theorem strict_index.const_after_m {c : chain α} {m n : Nat} (h : strict_index c m n = m) : ∀ k, n ≤ k → strict_index c m k = m := fun k hk =>
            have : ∀ k, strict_index c m (n + k) = m := fun k => by
              induction k with
              | zero      => exact h
              | succ k ih => exact def_not_exists fun ⟨_, h₁, _, h₂, _⟩ => absurd ih (Nat.ne_of_lt (Nat.lt_trans h₁ h₂))
            let ⟨k, hk⟩ := Nat.le.dest hk
            hk ▸ this k
        theorem strict_index.le_m (c : chain α) (m : Nat) : (n : Nat) → strict_index c m n ≤ m
        | 0   => (zero_or_m c m).elim (Eq.symm · ▸ Nat.zero_le m) (Eq.symm · ▸ Nat.le_refl m)
        | n+1 => (spec c m n).elim Nat.le_of_eq (fun h => Nat.le_of_lt h.right.right.left)
        theorem strict_index.increasing (c : chain α) (m n : Nat) : strict_index c m n ≤ strict_index c m n.succ :=
          (spec c m n).elim (Eq.symm · ▸ le_m c m n) fun h => Nat.le_of_lt h.left
        theorem strict_index.m_of_stable {c : chain α} {m n : Nat} (h : strict_index c m n = strict_index c m n.succ) :
          strict_index c m n = m := h ▸ (spec c m n).resolve_right fun h' => absurd h (Nat.ne_of_lt h'.left)
        theorem strict_index.stable_of_m {c : chain α} {m n : Nat} (h : strict_index c m n = m) : strict_index c m n = strict_index c m n.succ :=
          h.trans (const_after_m h n.succ (Nat.le_succ _)).symm
        theorem strict_index.stable_after {c : chain α} {m n : Nat} (h : strict_index c m n = strict_index c m n.succ) :
          ∀ k, n ≤ k → strict_index c m k = m := const_after_m (m_of_stable h)
        theorem strict_index.strict_before {c : chain α} {m n : Nat} (h : strict_index c m n ≠ strict_index c m n.succ) :
          ∀ k, k ≤ n → strict_index c m k ≠ strict_index c m k.succ :=
            fun k hk h' => absurd (stable_of_m (stable_after h' n hk)) h
        theorem strict_index.strict_increasing {c : chain α} {m n : Nat} (h : strict_index c m n ≠ strict_index c m n.succ) :
          ∀ k, k ≤ n.succ → k ≤ strict_index c m k := fun k hk => by
            induction k with
            | zero      => exact Nat.zero_le _
            | succ k ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih (Nat.le_trans (Nat.le_succ k) hk))
              (Nat.lt_of_le_and_ne (increasing c m k) (strict_before h k (Nat.le_of_succ_le_succ hk))))
        theorem strict_index.m_eq_m (c : chain α) (m : Nat) : strict_index c m m = m := by
          byCases h : strict_index c m m = strict_index c m m.succ
          { exact m_of_stable h }
          { exact Nat.le_antisymm (le_m c m m) (strict_increasing h m (Nat.le_succ m)) }
        theorem strict_index.strict_stable (c : chain α) (m : Nat) : ∃ N, (∀ n, n < N → strict_index c m n ≠ strict_index c m n.succ)
          ∧ ∀ n, N ≤ n → strict_index c m n = m :=
            let ⟨N, hN, hNmax⟩ := minimal.min_exists {k | strict_index c m k = m} ⟨m, m_eq_m c m⟩ id
            ⟨N, fun n hn => match N with
              | 0   => absurd hn (Nat.not_lt_zero n)
              | N+1 => by
                have : strict_index c m N ≠ strict_index c m N.succ := fun h =>
                  absurd (hNmax N (m_of_stable h)) (Nat.not_le.mpr (Nat.lt.base N))
                exact strict_before this n (Nat.le_of_lt_succ hn), (const_after_m hN ·)⟩
        noncomputable abbrev strict_index.length (c : chain α) (m : Nat) : Nat := choose (strict_stable c m)
        theorem strict_index.length_spec (c : chain α) (m : Nat) : (∀ n, n < length c m → strict_index c m n ≠ strict_index c m n.succ)
          ∧ ∀ n, length c m ≤ n → strict_index c m n = m := choose_spec (strict_stable c m)
        theorem strict_index.stable_length_le (c : chain α) (m : Nat) : length c m ≤ m :=
          Nat.not_lt.mp (mt ((choose_spec (strict_stable c m)).left m) (iff_not_not.mpr (stable_of_m (m_eq_m c m))))
        theorem strict_index.neq_m_lt_length {c : chain α} {m n : Nat} (hn : n < length c m) : strict_index c m n ≠ m :=
          fun h => absurd (stable_of_m h) ((length_spec c m).left n hn)
        theorem strict_index.eq_m_ge_length {c : chain α} {m n : Nat} (hn : length c m ≤ n) : strict_index c m n = m :=
          (length_spec c m).right n hn
        theorem strict_index.length_zero {c : chain α} {m : Nat} : length c m = 0 ↔ c m = c 0 :=
          ⟨fun h => c_zero c m ▸ (congrArg (c ·) (eq_m_ge_length (h ▸ Nat.le_refl 0)).symm),
          fun h => Nat.le_zero.mp (Nat.le_of_succ_le_succ (Nat.not_le.mp (mt neq_m_lt_length (iff_not_not.mpr (def_zero_m h.symm)))))⟩

        abbrev monotone_chain (c : chain α) : Prop := ∀ i k, i ≤ k → c i = c k → ∀ j, i ≤ j → j ≤ k → c j = c i
        theorem monotone_of_ascending {c : chain α} (hc : c.ascending) : monotone_chain c :=
          fun i k hik hcik j hij hjk => Ideal.antisymm (hcik ▸ subset_ascending hc hjk) (subset_ascending hc hij)
        theorem monotone_of_descending {c : chain α} (hc : c.descending) : monotone_chain c :=
          fun i k hik hcik j hij hjk => Ideal.antisymm (subset_descending hc hij) (hcik ▸ subset_descending hc hjk)

        theorem strict_index.next_term_m_succ {c : chain α} {m n : Nat} (hmonotone : monotone_chain c) (h : strict_index c m n = strict_index c m.succ n)
          (nt : next_term c m (strict_index c m n)) : ∃ nt' : next_term c m.succ (strict_index c m.succ n), choose (minimal.min_exists _ nt id) = choose (minimal.min_exists _ nt' id) :=
            let h' := minimal.min_exists _ nt id
            have : strict_index c m.succ n < choose h' ∧ c (strict_index c m.succ n) ≠ c (choose h') ∧ choose h' < m.succ ∧ ∀ l, l ≤ choose h' → c l ≠ c m.succ :=
              ⟨h ▸ (choose_spec h').left.left, h ▸ (choose_spec h').left.right.left, Nat.lt_trans (choose_spec h').left.right.right.left (Nat.lt.base m),
                fun l hl h'' => absurd (hmonotone l m.succ (Nat.le_trans hl (Nat.le_of_lt (Nat.lt.step (choose_spec h').left.right.right.left))) h'' m
                  (Nat.le_trans hl (Nat.le_of_lt (choose_spec h').left.right.right.left)) (Nat.le_succ m)) ((choose_spec h').left.right.right.right l hl).symm⟩
            ⟨⟨choose h', this⟩, (next_term_ext this fun k hk => by
              byCases hk' : k = m
              { exact hk'.symm ▸ Nat.le_of_lt (choose_spec h').left.right.right.left }
              { byCases hk'' : ∃ l, l ≤ k ∧ c l = c m;
                { let ⟨l, hl, h⟩ := hk''; exact Nat.le_trans (Nat.le_of_lt (Nat.not_le.mp (imp_not_comm.mp
                  ((choose_spec h').left.right.right.right l) h))) hl }
                { simp only [not_exists, not_and] at hk''
                  exact (choose_spec h').right k ⟨h ▸ hk.left, h ▸ hk.right.left, Nat.lt_of_le_and_ne
                    (Nat.le_of_succ_le_succ hk.right.right.left) hk', hk''⟩} } ).symm⟩

        theorem strict_index.lt_length_m_succ {c : chain α} {m n : Nat} (hmonotone : monotone_chain c)
          (hn : n < length c m) : strict_index c m n = strict_index c m.succ n := by
            induction n with
            | zero      =>
              have h0 := mt def_zero_m (neq_m_lt_length hn);
              have h0' := def_zero_0 fun h' => absurd (hmonotone 0 m.succ (Nat.zero_le _) h' m (Nat.zero_le m) (Nat.le_succ m)).symm h0;
              exact (def_zero_0 h0).trans h0'.symm
            | succ n ih =>
              have : next_term c m (strict_index c m n) := of_not_not (mt def_not_exists (neq_m_lt_length hn))
              let ⟨k, hk⟩ := next_term_m_succ hmonotone (ih (Nat.lt_trans (Nat.lt.base n) hn)) this;
              exact (def_exists this).trans (hk.trans (def_exists k).symm)
        
        theorem strict_index.ge_length_of_m_eq_m_succ {c : chain α} {m n : Nat} (hmonotone : monotone_chain c)
          (hm : c m = c m.succ) (hn : length c m ≤ n) : strict_index c m.succ n = m.succ := by
            induction n with
            | zero => exact def_zero_m ((length_zero.mp (Nat.le_zero.mp hn)).symm.trans hm)
            | succ n ih =>
              exact (Nat.lt_or_eq_of_le hn).elim (fun hn => stable_after (stable_of_m (ih (Nat.le_of_succ_le_succ hn))) n.succ (Nat.le_succ n))
                fun hn =>
                  have he := lt_length_m_succ hmonotone (hn ▸ Nat.lt.base n : n < length c m)
                  have : ¬next_term c m (strict_index c m n) := fun h => absurd (eq_m_ge_length (Nat.le_of_eq hn)) (neq_m_of_exists h)
                  have : ¬next_term c m.succ (strict_index c m.succ n) := fun ⟨k, h₁, h₂, h₃, h₄⟩ =>
                    absurd ⟨k, he ▸ h₁, he ▸ h₂, Nat.lt_of_le_and_ne (Nat.le_of_succ_le_succ h₃) fun h =>
                      absurd hm (h ▸ h₄ k (Nat.le_refl k)), fun l hl => hm ▸ h₄ l hl⟩ this
                  def_not_exists this

        theorem strict_index.neq_succ_injective {c : chain α} {m n : Nat} (h : strict_index c m n ≠ strict_index c m n.succ) : c (strict_index c m n) ≠ c (strict_index c m n.succ) := by
          byCases h' : strict_index c m n.succ = m
          { match n with
            | 0   =>
              rw [h'] at h ⊢; have := mt def_zero_m h
              rw [def_zero_0 this]; exact this
            | n+1 => rw [h']; exact ((spec c m n).resolve_left (fun h' => h (stable_of_m h'))).right.right.right.left _ (Nat.le_refl _) }
          { exact ((spec c m n).resolve_left h').right.left }
        theorem strict_index.eq_succ_injective {c : chain α} {m n : Nat} (h : c (strict_index c m n) = c (strict_index c m n.succ)) : strict_index c m n = strict_index c m n.succ :=
          of_not_not (mt neq_succ_injective (iff_not_not.mpr h))
        theorem strict_index.m_injective {c : chain α} {m n : Nat} (h : c (strict_index c m n) = c m) : strict_index c m n = m :=
          match n with
          | 0   => def_zero_m (c_zero c m ▸ h)
          | n+1 => by
            byCases h' : next_term c m (strict_index c m n)
            { have h'' := minimal.min_exists _ h' id;
              exact absurd (def_exists h' ▸ h) ((choose_spec h'').left.right.right.right
                (choose h'') (Nat.le_refl _)); }
            { exact def_not_exists h' }

        theorem strict_index.eq_length_of_m_neq_m_succ {c : chain α} {m : Nat} (hmonotone : monotone_chain c)
          (hm : c m ≠ c m.succ) : c (strict_index c m.succ (length c m)) = c m := by
            byCases hl : length c m = 0
            { exact hl ▸ c_zero c m.succ ▸ (length_zero.mp hl).symm }
            { let ⟨k, hk⟩ := Nat.ne_zero_dest hl;
              rw [hk];
              have hk' : k < length c m := hk ▸ Nat.lt.base k
              have he := lt_length_m_succ hmonotone hk'
              let ⟨n, hn, hnmin⟩ := minimal.min_exists {n | c n = c m} ⟨m, rfl⟩ id
              have hm' := hnmin m rfl
              have hn' : strict_index c m.succ k < n ∧ c (strict_index c m.succ k) ≠ c n ∧ n < m.succ ∧
                ∀ l, l ≤ n → c l ≠ c m.succ := ⟨he ▸ byContradiction fun h => absurd (m_injective (hn ▸
                  hmonotone n m hm' hn (strict_index c m k) (Nat.not_lt.mp h) (le_m c m k)))
                  (neq_m_lt_length hk'), fun h => absurd (m_injective (hn ▸ he ▸ h)) (neq_m_lt_length hk'),
                  Nat.succ_le_succ hm', fun l hl hl' => absurd ((hmonotone l m.succ (Nat.le_trans hl
                  (Nat.le_step hm')) hl' m (Nat.le_trans hl hm') (Nat.le_succ m)).trans hl') hm⟩;
              rw [def_exists ⟨n, hn'⟩, next_term_ext hn' fun x ⟨h₁, h₂, h₃, h₄⟩ => byContradiction fun h =>
                have h := Nat.not_le.mp h
                have : next_term c m (strict_index c m k) := ⟨x, he ▸ h₁, he ▸ h₂,
                  Nat.lt_of_le_and_ne (Nat.le_of_succ_le_succ h₃) (fun h' => absurd hm' (Nat.not_le.mpr (h' ▸ h))),
                  fun l hl h' => absurd (Nat.lt_of_le_of_lt hl (Nat.lt_of_lt_of_le h (hnmin l h'))) (Nat.lt_irrefl l)⟩
                absurd (eq_m_ge_length (Nat.le_refl (length c m))) (hk ▸ neq_m_of_exists this)]; exact hn }
        theorem strict_index.length_succ_of_m_neq_m_succ {c : chain α} {m : Nat} (hmonotone : monotone_chain c)
          (hm : c m ≠ c m.succ) : strict_index c m.succ (length c m).succ = m.succ :=
            have : ¬ next_term c m.succ (strict_index c m.succ (length c m)) := fun ⟨x, h₁, h₂, h₃, h₄⟩ => absurd (hmonotone (strict_index c m.succ
              (length c m)) m (Nat.le_trans (Nat.le_of_lt h₁) (Nat.le_of_succ_le_succ h₃)) (eq_length_of_m_neq_m_succ hmonotone hm) x (Nat.le_of_lt h₁)
              (Nat.le_of_succ_le_succ h₃)).symm h₂;
            def_not_exists this

        theorem strict_index.succ_length_le {c : chain α} (hmonotone : monotone_chain c) (m : Nat) : length c m ≤ length c m.succ :=
          Nat.not_lt.mp fun h => by
            have := le_m c m (length c m.succ)
            rw [lt_length_m_succ hmonotone h, eq_m_ge_length (Nat.le_refl _)] at this
            exact absurd this (Nat.not_le.mpr (Nat.lt.base m))
        theorem strict_index.succ_length_succ {c : chain α} {m : Nat} (hc : c m ≠ c m.succ) (hmonotone : monotone_chain c) :
          length c m.succ = (length c m).succ :=
            Nat.le_antisymm
            (Nat.not_lt.mp (mt ((length_spec c m.succ).left (length c m).succ) (iff_not_not.mpr
              (stable_of_m (length_succ_of_m_neq_m_succ hmonotone hc)))))
            (Nat.succ_le_of_lt (Nat.not_le.mp (mt ((length_spec c m.succ).right (length c m)) fun h =>
              absurd ((eq_length_of_m_neq_m_succ hmonotone hc).symm.trans (congrArg (c ·) h)) hc)))
        theorem strict_index.succ_length_eq {c : chain α} {m : Nat} (hc : c m = c m.succ) (hmonotone : monotone_chain c) :
          length c m.succ = length c m :=
            Nat.le_antisymm
            (Nat.not_lt.mp (mt ((length_spec c m.succ).left (length c m)) (iff_not_not.mpr ((ge_length_of_m_eq_m_succ
              hmonotone hc (Nat.le_refl _)).trans (ge_length_of_m_eq_m_succ hmonotone hc (Nat.le_succ _)).symm))))
            (succ_length_le hmonotone m)
      end strict_index

      noncomputable def strict_stabilised (c : chain α) (m : Nat) : chain α := ⟨fun n => c (strict_index c m n)⟩

      theorem strict_stabilised.base (c : chain α) (m : Nat) : (strict_stabilised c m).base (c 0) := strict_index.c_zero c m
      theorem strict_stabilised.descending {c : chain α} (hc : c.descending) (m : Nat) : (strict_stabilised c m).descending :=
        fun n => subset_descending hc (strict_index.increasing c m n)

      theorem strict_stabilised.strict_stable (c : chain α) (m : Nat) : (strict_stabilised c m).strict_stable :=
        let ⟨N, hN₁, hN₂⟩ := strict_index.strict_stable c m
        ⟨N, fun n hn => strict_index.neq_succ_injective (hN₁ n hn),
        fun n hn => congrArg (c ·) ((hN₂ n hn).trans (hN₂ N (Nat.le_refl _)).symm)⟩
      noncomputable abbrev strict_stabilised.length (c : chain α) (m : Nat) : Nat :=
        (strict_stabilised c m).stable_length (strict_stable c m)
      theorem strict_stabilised.length_eq_length (c : chain α) (m : Nat) : length c m = strict_index.length c m :=
        Nat.le_antisymm (Nat.not_lt.mp (mt (((strict_stabilised c m).stable_length_spec (strict_stable c m)).left (strict_index.length c m))
          (iff_not_not.mpr (congrArg (c ·) (((strict_index.length_spec c m).right (strict_index.length c m) (Nat.le_refl _)).trans
            ((strict_index.length_spec c m).right (strict_index.length c m).succ (Nat.le_succ _)).symm)))))
          (Nat.not_lt.mp (mt ((strict_index.length_spec c m).left (length c m)) (iff_not_not.mpr (strict_index.eq_succ_injective
            (((strict_stabilised c m).stable_length_spec (strict_stable c m)).right (length c m).succ (Nat.le_succ _)).symm))))
      theorem strict_stabilised.length_le (c : chain α) (m : Nat) : length c m ≤ m :=
        length_eq_length c m ▸ strict_index.stable_length_le c m

      theorem strict_stabilised.succ_length_le {c : chain α} (hmonotone : monotone_chain c) (m : Nat) :
        length c m ≤ length c m.succ := length_eq_length c m ▸ length_eq_length c m.succ ▸ strict_index.succ_length_le hmonotone m
      theorem strict_stabilised.succ_length_succ {c : chain α} {m : Nat} (hmonotone : monotone_chain c) (hc : c m ≠ c m.succ) :
        length c m.succ = (length c m).succ := length_eq_length c m ▸ length_eq_length c m.succ ▸ strict_index.succ_length_succ hc hmonotone
      theorem strict_stabilised.succ_length_eq {c : chain α} {m : Nat} (hmonotone : monotone_chain c) (hc : c m = c m.succ) :
        length c m.succ = length c m := length_eq_length c m ▸ length_eq_length c m.succ ▸ strict_index.succ_length_eq hc hmonotone

    end chain
  end Ideal

  open Ideal

  namespace Ring
    namespace krull_dim

      def krull_dim_infinite (α : Type _) [Ring α] : Prop := chain.length_infinite fun c : chain α => c.is_prime ∧ c.ascending

      def has_krull_dim (α : Type _) [Ring α] : Prop := chain.length_finite (fun c : chain α => c.is_prime ∧ c.ascending)

      theorem has_krull_dim_iff_not_infinite [NonTrivialRing α] : has_krull_dim α ↔ ¬krull_dim_infinite α :=
        let ⟨I, hI⟩ := exists_prime_ideal α
        chain.length_finite_iff_not_infinite ⟨chain.const_chain I, ⟨chain.const_chain.is_prime hI,
          chain.const_chain.ascending I⟩, chain.const_chain.strict_stable I⟩

      noncomputable def dim [Ring α] : has_krull_dim α → Nat := chain.length_of_finite

    end krull_dim
  end Ring

  namespace Ideal
    variable [Ring α] (I : Ideal α)

    protected def length_finite : Prop := chain.length_finite (fun c : chain α => c.base I ∧ c.descending)
    protected def length_infinite : Prop := chain.length_infinite (fun c : chain α => c.base I ∧ c.descending)

    theorem exists_ideal_length_chain : ∃ c : chain α, (c.base I ∧ c.descending) ∧ c.strict_stable :=
      ⟨chain.const_chain I, ⟨chain.const_chain.base I, chain.const_chain.descending I⟩, chain.const_chain.strict_stable I⟩

    protected theorem length_finite_iff_not_infinite : I.length_finite ↔ ¬I.length_infinite :=
      chain.length_finite_iff_not_infinite (exists_ideal_length_chain I)

    structure height_chain extends chain α where
      hbase : f 0 = I
      hprime : tochain.is_prime
      hdescend : tochain.descending
    theorem height_chain.subset_base [Ring α] {I : Ideal α} (c : height_chain I) : ∀ n, c.tochain n ⊆ I :=
      chain.subset_base c.hbase c.hdescend
    theorem height_chain.base_prime [Ring α] {I : Ideal α} (c : height_chain I) : I.is_prime :=
      chain.base_prime c.hbase c.hprime

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
      h.elim (fun ⟨c, _⟩ => c.base_prime) fun ⟨c, _⟩ => c.base_prime

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

  namespace Ring
    variable (α : Type _) [Ring α]

    protected def length_finite : Prop := Ideal.length_finite (1 : Ideal α)
    protected def length_infinite : Prop := Ideal.length_infinite (1 : Ideal α)

    variable {α}

    protected theorem length_finite_iff_not_infinite : Ring.length_finite α ↔ ¬Ring.length_infinite α :=
      Ideal.length_finite_iff_not_infinite 1

    theorem length_infinite_of_isomorphism [Ring β] (f : α ≅ᵣ β) (h : Ring.length_infinite β) :
      Ring.length_infinite α := by
        simp only [Ring.length_infinite, Ideal.length_infinite]
        have : Function.image' (chain.contract_chain f.preserve_mul_left) {c | c.base 1 ∧ c.descending} =
          {c | c.base 1 ∧ c.descending} := Set.ext.mp fun x => ⟨fun ⟨y, ⟨hy₁, hy₂⟩, hyx⟩ => by
            exact ⟨hyx ▸ contraction_unit _ ▸ chain.contract_chain.base _ hy₁, hyx ▸ chain.contract_chain.descending _ hy₂⟩,
              fun ⟨hx₁, hx₂⟩ => ⟨chain.extend_chain f.hom x, ⟨extension_unit_of_surjective f.toMIsomorphism.to_surjective ▸
                chain.extend_chain.base f.hom hx₁, chain.extend_chain.descending f.hom hx₂⟩, x.extension_contraction_of_isomorphism f⟩⟩
        exact this ▸ chain.contract_chain.length_infinite f.preserve_mul_left f.toMIsomorphism.to_surjective h

    open NCSemiring Group

    theorem NonTrivial_of_length_infinite : Ring.length_infinite α → Ring.is_NonTrivial α :=
      chain.NonTrivial_of_length_infinite

    theorem field_length_finite [Ring α] (h : Ring.is_Field α) : Ring.length_finite α :=
      chain.field_length_finite_of_descending h (exists_ideal_length_chain 1) (fun _ => And.right)

    theorem finite_chain_ends_zero [Ring α] {c : chain α} (N : Nat) (hltN : ∀ n, n < N → c n ≠ c n.succ) (hNle : ∀ n, N ≤ n → c n = c N)
      (hbase : c.base 1) (hdesc : c.descending) (hmax : ∀ (d : chain α) (hd : d.strict_stable),
        (d.base 1 ∧ d.descending) → d.stable_length hd ≤ c.stable_length ⟨N, hltN, hNle⟩) : c N = 0 := by
          apply Classical.byContradiction; intro h0
          let d : chain α := ⟨fun n => if n ≤ N then c n else 0⟩
          have hd₁ : ∀ {n}, n ≤ N → d n = c n := fun hn => by simp only [hn, ite_true]
          have hd₂ : ∀ {n}, ¬n ≤ N → d n = 0 := fun hn => by simp only [hn, ite_false]
          have hdlt : ∀ n, n < N.succ → d n ≠ d n.succ := fun n hn =>
            have hn := Nat.le_of_lt_succ hn
            hd₁ hn ▸ (Nat.lt_or_eq_of_le hn).elim (fun hn => by rw [hd₁ hn]; exact hltN n hn)
              (fun hn => by rw [hn, hd₂ (Nat.not_le.mpr (Nat.lt.base N))]; exact h0)
          have hdle : ∀ n, N.succ ≤ n → d n = d N.succ := fun n hn => by
            rw [hd₂ (Nat.not_le.mpr hn), hd₂ (Nat.not_le.mpr (Nat.lt.base N))]
          exact absurd (hmax d ⟨N.succ, hdlt, hdle⟩ ⟨(hd₁ (Nat.zero_le N) ▸ hbase : d 0 = 1),
            fun n => (Nat.lt_trichotomy n N).elim (fun hn => by rw [hd₁ hn, hd₁ (Nat.le_of_lt hn)]; exact hdesc n)
            (Or.elim · (fun hn => by rw [hn, hd₂ (Nat.not_le.mpr (Nat.lt.base N))]; exact Ideal.zero_ideal_in _)
              (fun hn => by rw [hd₂ (Nat.not_le.mpr (Nat.lt.step hn))]; exact Ideal.zero_ideal_in _))⟩)
            (by
              rw [chain.stable_length_eq N hltN hNle, chain.stable_length_eq N.succ hdlt hdle]
              exact Nat.not_le.mpr (Nat.lt.base N))

    theorem length_finite_of_ses [Ring α] [Ring β] [Ring γ] {f₁ : α →₋ β} (hf₁ : preserve_mul_left f₁)
      (hf₁' : Function.injective f₁.hom) (hf₁'' : ∀ I, (extension f₁.hom I).subset = Function.image' f₁.hom I.subset)
      {f₂ : β →ᵣ₁ γ} (hf₂ : Function.surjective f₂.hom) (hexact : f₁.image = f₂.kernel)
        (hα : Ring.length_finite α) (hγ : Ring.length_finite γ) : Ring.length_finite β :=
          have hstrict : ∀ I J : Ideal β, I ⊊ J → contraction hf₁ I ≠ contraction hf₁ J ∨ extension f₂.hom I ≠ extension f₂.hom J :=
            fun I J h => by
              byCases he : extension f₂.hom I = extension f₂.hom J
              { let ⟨x, hxI, hxJ, hxf⟩ := exists_kernel_element hf₂ h he;
                let ⟨y, hy⟩ := (hexact ▸ hxf : x ∈ f₁.image);
                exact Or.inl (fun h => absurd ((hy ▸ (Ideal.ext'.mp h y).mpr : x ∈ J → x ∈ I) hxJ) hxI) }
              { exact Or.inr he }
          ⟨fun c ⟨hc₁, hc₂⟩ hc₃ => by
            byCases h : ∀ (N : Nat), ∃ (n : Nat) (hn : N ≤ n), chain.contract_chain hf₁ c n ≠ chain.contract_chain hf₁ c N
            { exact absurd (chain.strictified.strict_infinite h) (hα.left (chain.strictified h) ⟨chain.strictified.base h,
              chain.strictified.descending h (chain.contract_chain.descending hf₁ hc₂)⟩) }
            { simp only [not_forall, not_exists, iff_not_not] at h
              let ⟨N, hN⟩ := h;
              have hstrict : ∀ n, N ≤ n → chain.extend_chain f₂.hom c n ≠ chain.extend_chain f₂.hom c n.succ :=
                fun n hn => ((hstrict (c n.succ) (c n) (chain.subsetneq_succ_of_strict_infinite_descending hc₃ hc₂ n)).resolve_left
                  (iff_not_not.mpr ((hN n.succ (Nat.le_trans hn (Nat.le_succ n))).trans (hN n hn).symm))).symm
              let c' : chain γ := ⟨fun n => match n with
                | 0   => 1
                | n+1 => (chain.extend_chain f₂.hom c).shift N.succ n⟩
              have hdesc' : c'.descending := fun n => match n with
                | 0   => in_unit_ideal _
                | n+1 => chain.shift_descending N.succ (chain.extend_chain.descending f₂.hom hc₂) n
              have : c'.strict_infinite := by
                intro n
                match n with
                | 0   => exact fun (h : 1 = c' 1) => hstrict N (Nat.le_refl N) (h ▸
                  Ideal.unit_ideal_in (h ▸ (chain.extend_chain.descending f₂.hom hc₂) N))
                | n+1 => exact hstrict (N.succ + n) (Nat.le_trans (Nat.le_succ N) (Nat.le_add_right N.succ n))
              exact absurd this (hγ.left c' ⟨rfl, hdesc'⟩) },
            let ⟨cα, ⟨Nα, hltNα, hNαle⟩, ⟨hbaseα, hdescα⟩, hmaxα⟩ := hα.right
            let ⟨cγ, ⟨Nγ, hltNγ, hNγle⟩, ⟨hbaseγ, hdescγ⟩, hmaxγ⟩ := hγ.right
            have hγ0 := finite_chain_ends_zero Nγ hltNγ hNγle hbaseγ hdescγ hmaxγ
            let c' : chain β := ⟨fun n =>
              if n ≤ Nγ then chain.contract_chain f₂.preserve_mul_left cγ n
              else chain.extend_chain f₁.hom cα (n - Nγ)⟩
            have hc'γ : ∀ {n}, n ≤ Nγ → c' n = chain.contract_chain f₂.preserve_mul_left cγ n :=
              fun h => by simp only [h, ite_true]
            have hc'α : ∀ {n}, ¬n ≤ Nγ → c' n = chain.extend_chain f₁.hom cα (n - Nγ) :=
              fun h => by simp only [h, ite_false]
            have hc'lt : ∀ n, n < Nα + Nγ → c' n ≠ c' n.succ := fun n hn =>
              (Nat.lt_trichotomy n Nγ).elim (fun hn => hc'γ (Nat.le_of_lt hn) ▸ hc'γ hn ▸ fun h =>
                hltNγ n hn (contraction_injective_of_surjective f₂.preserve_mul_left hf₂ h))
                (Or.elim · (fun hn' => by
                  rw [hc'γ (Nat.le_of_eq hn'), hc'α (Nat.not_le.mpr (hn' ▸ Nat.lt_succ_self n)),
                    hn', Nat.succ_sub (Nat.le_refl Nγ), Nat.sub_self]
                  have h₁ : chain.extend_chain f₁.hom cα 0 ⊆ chain.contract_chain f₂.preserve_mul_left cγ Nγ :=
                    fun x hx =>
                      have : f₂ x = 0 := (hexact ▸ Function.image'_sub_image _ _ (hf₁'' (cα 0) ▸
                        hx : x ∈ Function.image' f₁.hom (cα 0).subset) : x ∈ f₂.kernel)
                      (this ▸ (cγ Nγ).has_zero : f₂ x ∈ (cγ Nγ))
                  have h₂ : chain.extend_chain f₁.hom cα 1 ⊊ chain.extend_chain f₁.hom cα 0 :=
                    Ideal.subsetneq.mpr ⟨chain.extend_chain.descending _ hdescα 0, fun h =>
                      absurd (extension_injective_of_injective_eq_image hf₁ hf₁' hf₁'' h)
                        (hltNα 0 (Nat.of_lt_add_left (hn' ▸ hn : Nγ < Nα + Nγ))).symm⟩
                  exact fun h => absurd (h ▸ h₁) (ProperSubset.toNotSubset h₂))
                  (fun hn' => by
                    rw [hc'α (Nat.not_le.mpr hn'), hc'α (Nat.not_le.mpr (Nat.lt.step hn')),
                      Nat.succ_sub (Nat.le_of_lt hn')]
                    have := hltNα (n - Nγ) ((Nat.sub_lt_iff_right (Nat.le_of_lt hn')).mpr hn)
                    exact fun h => absurd (extension_injective_of_injective_eq_image hf₁ hf₁' hf₁'' h) this))
            have hc'le : ∀ n, Nα + Nγ ≤ n → c' n = c' (Nα + Nγ) := fun n hn => by
              byCases hnα : Nα = 0
              { rw [hnα, Nat.zero_add] at hn ⊢;
                exact (Nat.lt_or_eq_of_le hn).elim
                  (fun hnγ => by
                    rw [hc'α (Nat.not_le.mpr hnγ), hc'γ (Nat.le_refl Nγ)]
                    have h₁ : chain.extend_chain f₁ cα (n - Nγ) = extension f₁.hom 1 := by
                      have := hNαle (n - Nγ) (hnα ▸ Nat.zero_le _)
                      rw [hnα, hbaseα] at this
                      exact congrArg (extension f₁.hom) this
                    have h₂ : chain.contract_chain f₂.preserve_mul_left cγ Nγ = contraction f₂.preserve_mul_left 0 := by rw [←hγ0]; rfl
                    exact h₁ ▸ h₂ ▸ Ideal.ext'.mpr fun x => ⟨fun hx => (hexact ▸ Function.image'_sub_image _ _
                      ((Set.ext.mpr (hf₁'' 1) x).mp hx) : x ∈ f₂.kernel),
                      fun hx => let ⟨y, hy⟩ : x ∈ f₁.image := hexact ▸ hx; from_set.contains_mem ⟨y, trivial, hy⟩⟩)
                  (fun hnγ => by rw [hnγ]) }
              { rw [hc'α (Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.lt_add_pos_left Nγ hnα) hn)),
                  hc'α (Nat.not_le.mpr (Nat.lt_add_pos_left Nγ hnα)), Nat.add_sub_cancel]
                exact congrArg (extension f₁.hom) (hNαle (n - Nγ) ((Nat.le_sub_iff_right (Nat.le_trans
                  (Nat.le_add_left Nγ Nα) hn)).mpr hn)) }
            ⟨c', ⟨Nα + Nγ, hc'lt, hc'le⟩,
              ⟨have : contraction f₂.preserve_mul_left (cγ 0) = 1 := by rw [hbaseγ, contraction_unit];
                (hc'γ (Nat.zero_le Nγ) ▸ this : c' 0 = 1),
              fun n => (Nat.lt_trichotomy n Nγ).elim
                (fun hn => by
                  rw [hc'γ hn, hc'γ (Nat.le_of_lt hn)]
                  exact chain.contract_chain.descending f₂.preserve_mul_left hdescγ n)
                (Or.elim · (fun hn => by
                  rw [hn, hc'α (Nat.not_le.mpr (Nat.lt.base Nγ)), hc'γ (Nat.le_refl Nγ), Nat.succ_sub (Nat.le_refl Nγ),
                    Nat.sub_self]; exact fun x hx => (hγ0 ▸ (hexact ▸ Function.image'_sub_image _ _ ((Set.ext.mpr (hf₁''
                      (cα 1)) x).mp hx) : x ∈ f₂.kernel) : f₂ x ∈ cγ Nγ))
                  (fun hn => by
                    rw [hc'α (Nat.not_le.mpr (Nat.lt.step hn)), hc'α (Nat.not_le.mpr hn),
                      Nat.succ_sub (Nat.le_of_lt hn)]
                    exact chain.extend_chain.descending _ hdescα _))⟩,
              fun d hd ⟨hdbase, hddesc⟩ => by
                let dα    : ∀ n, chain α := chain.strict_stabilised (chain.contract_chain hf₁ d)
                have hdα₁ : ∀ n, (dα n).strict_stable := chain.strict_stabilised.strict_stable _
                have hdα₂ : ∀ n, (dα n).base 1 := contraction_unit hf₁ ▸ hdbase ▸ chain.strict_stabilised.base _
                have hdα₃ : ∀ n, (dα n).descending := chain.strict_stabilised.descending (chain.contract_chain.descending hf₁ hddesc)
                have hdα₄ : ∀ n, (dα n).stable_length (hdα₁ n) ≤ Nα := fun n => chain.stable_length_eq Nα hltNα hNαle ▸
                  hmaxα (dα n) (hdα₁ n) ⟨hdα₂ n, hdα₃ n⟩
                let dγ    : ∀ n, chain γ := chain.strict_stabilised (chain.extend_chain f₂ d)
                have hdγ₁ : ∀ n, (dγ n).strict_stable := chain.strict_stabilised.strict_stable _
                have hdγ₂ : ∀ n, (dγ n).base 1 := extension_unit_of_surjective hf₂ ▸ hdbase ▸ chain.strict_stabilised.base _
                have hdγ₃ : ∀ n, (dγ n).descending := chain.strict_stabilised.descending (chain.extend_chain.descending f₂ hddesc)
                have hdγ₄ : ∀ n, (dγ n).stable_length (hdγ₁ n) ≤ Nγ := fun n => chain.stable_length_eq Nγ hltNγ hNγle ▸
                  hmaxγ (dγ n) (hdγ₁ n) ⟨hdγ₂ n, hdγ₃ n⟩
                have : ∀ n, n ≤ d.stable_length hd → n ≤ (dα n).stable_length (hdα₁ n) + (dγ n).stable_length (hdγ₁ n) := fun n hn => by
                  induction n with
                  | zero      => exact Nat.zero_le _
                  | succ n ih =>
                    have hmonoα := chain.monotone_of_descending (chain.contract_chain.descending hf₁ hddesc)
                    have hmonoγ := chain.monotone_of_descending (chain.extend_chain.descending f₂.hom hddesc)
                    have := Nat.succ_le_succ (ih (Nat.le_trans (Nat.le_succ n) hn))
                    exact (hstrict (d n.succ) (d n) (Ideal.subsetneq.mpr ⟨hddesc n, ((d.stable_length_spec hd).left n hn).symm⟩)).elim
                      (fun h => Nat.le_trans this (Nat.succ_add _ _ ▸ Nat.add_le_add
                        (Nat.le_of_eq (chain.strict_stabilised.succ_length_succ hmonoα h.symm).symm)
                        (chain.strict_stabilised.succ_length_le hmonoγ n)))
                      fun h => Nat.le_trans this (Nat.add_succ _ _ ▸ Nat.add_le_add
                          (chain.strict_stabilised.succ_length_le hmonoα n)
                          (Nat.le_of_eq (chain.strict_stabilised.succ_length_succ hmonoγ h.symm).symm))
                rw [chain.stable_length_eq (Nα + Nγ) hc'lt hc'le]
                exact Nat.le_trans (this (d.stable_length hd) (Nat.le_refl _)) (Nat.add_le_add (hdα₄ (d.stable_length hd)) (hdγ₄ (d.stable_length hd)))⟩⟩
  end Ring

  def Ring.is_noetherian (α : Type _) [Ring α] : Prop := ∀ c : chain α, c.ascending → c.is_stable

  class NoetherianRing (α : Type _) extends Ring α where
    noetherian : Ring.is_noetherian α

  namespace NoetherianRing
    open Classical

    private noncomputable def no_maximal_seq [Ring α] {S : Set (Ideal α)} (hS : Nonempty S)
      (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) : Nat → Ideal α
    | 0   => (choice hS).val
    | n+1 => if hn : (no_maximal_seq hS h n) ∈ S then
        choose (h (no_maximal_seq hS h n) hn)
      else no_maximal_seq hS h n

    private theorem no_maximal_seq_in_S [Ring α] {S : Set (Ideal α)} (hS : Nonempty S)
      (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) (n : Nat) : no_maximal_seq hS h n ∈ S := by
    induction n with
    | zero      => exact (choice hS).property
    | succ n ih =>
      simp only [no_maximal_seq, ih, dite_true]
      exact (choose_spec (h (no_maximal_seq hS h n) ih)).left

    private theorem no_maximal_seq_def [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) (n : Nat) :
      no_maximal_seq hS h n.succ = choose (h (no_maximal_seq hS h n) (no_maximal_seq_in_S hS h n)) := by
        simp only [no_maximal_seq, no_maximal_seq_in_S hS h n]; rfl

    private theorem no_maximal_seq_subsetneq [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) :
      (n : Nat) → no_maximal_seq hS h n ⊊ no_maximal_seq hS h n.succ
    | 0 => no_maximal_seq_def hS h 0 ▸ (choose_spec (h (no_maximal_seq hS h 0)
      (no_maximal_seq_in_S hS h 0))).right
    | n+1 => no_maximal_seq_def hS h n.succ ▸ (choose_spec (h (no_maximal_seq hS h n.succ)
      (no_maximal_seq_in_S hS h n.succ))).right

    private theorem no_maximal_seq_subset [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) (n : Nat) :
      no_maximal_seq hS h n ⊆ no_maximal_seq hS h n.succ :=
        (no_maximal_seq_subsetneq hS h n).left

    private theorem no_maximal_seq_neq [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) (n : Nat) :
      no_maximal_seq hS h n ≠ no_maximal_seq hS h n.succ :=
        (Ideal.subsetneq.mp (no_maximal_seq_subsetneq hS h n)).right

    theorem exists_maximal [NoetherianRing α] {S : Set (Ideal α)} (hS : Nonempty S) : ∃ I ∈ S, ∀ J ∈ S, I ⊆ J → J = I :=
      byContradiction fun h => by
      simp only [not_exists, not_and, not_forall] at h
      have h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J := fun I hI =>
        let ⟨J, hJ₁, hJ₂, hJ₃⟩ := h I hI
        ⟨J, hJ₁, Ideal.subsetneq.mpr ⟨hJ₂, Ne.symm hJ₃⟩⟩
      let ⟨N, hN⟩ := NoetherianRing.noetherian ⟨no_maximal_seq hS h⟩ (no_maximal_seq_subset hS h)
      exact absurd (hN N.succ N.le_succ) (no_maximal_seq_neq hS h N).symm

    theorem ideal_finitely_generated [NoetherianRing α] (I : Ideal α) : I.finitely_generated :=
      let S : Set (Ideal α) := {J | J ⊆ I ∧ J.finitely_generated}
      let ⟨M, ⟨hM₁, hM₂⟩, hM₃⟩ := exists_maximal (⟨0, Ideal.zero_ideal_in I, finitely_generated.zero⟩ : Nonempty S)
      have : M = I := Ideal.antisymm hM₁ (fun x hx => by
        let ⟨f, hf⟩ := hM₂
        byCases hxf : x ∈ f.toSet
        { exact hf ▸ from_set.contains_mem hxf }
        { have := hM₃ (from_set (f.cons x hxf).toSet) ⟨from_set.ideal_contained fun y hy =>
            (Finset.mem_cons.mp hy).elim (· ▸ hx) fun hy => hM₁ (hf ▸ from_set.contains_mem hy), _, rfl⟩
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
          exact ⟨Q', delocalise_ideal.prime S hQ, Subset.trans (I.extension_contraction (natural_hom S).preserve_mul_left)
            (Ideal.contraction.subset (natural_hom S).preserve_mul_left hIQ), localise_ideal.prime_loc_deloc h.left hPS ▸
            Ideal.contraction.subset _ hQP₁, fun h' => hQP₂ (congrArg (localise_ideal S ·) h' ▸
            (delocalise_ideal.deloc_loc S Q).symm)⟩

    theorem localisation_noetherian [NoetherianRing α] (S : MultiplicativeSet α) : Ring.is_noetherian (localisation S) := fun c hc =>
      let ⟨N, hN⟩ := NoetherianRing.noetherian ⟨fun n => delocalise_ideal S (c n)⟩ fun n => contraction.subset (natural_hom S).preserve_mul_left (hc n)
      ⟨N, fun n hn => delocalise_ideal.deloc_loc S (c n) ▸ delocalise_ideal.deloc_loc S (c N) ▸ congrArg _ (hN n hn)⟩

    instance localisation_NoetherianRing [NoetherianRing α] (S : MultiplicativeSet α) : NoetherianRing (localisation S) where
      noetherian := localisation_noetherian S

    theorem surjective_noetherian [NoetherianRing α] [Ring β] {f : α →ᵣ β} (hf : Function.surjective f.hom) :
      Ring.is_noetherian β := fun c hc => chain.contract_chain.is_stable_of_surjective f.preserve_mul_left hf
        (NoetherianRing.noetherian (chain.contract_chain f.preserve_mul_left c)
        (chain.contract_chain.ascending f.preserve_mul_left hc))

    open QuotientRing

    theorem quotient_noetherian [NoetherianRing α] (I : Ideal α) : Ring.is_noetherian (QClass I) :=
      surjective_noetherian (natural_hom.surjective I)

    instance quotient_NoetherianRing [NoetherianRing α] (I : Ideal α) : NoetherianRing (QClass I) where
      noetherian := quotient_noetherian I
  end NoetherianRing

  def Ring.is_artinian (α : Type _) [Ring α] : Prop := ∀ c : chain α, c.descending → c.is_stable

  class ArtinianRing (α : Type _) extends Ring α where
    artinian : Ring.is_artinian α

  namespace ArtinianRing

    open Classical QuotientRing Monoid

    theorem artinian_of_finite_length [Ring α] (h : Ring.length_finite α) : Ring.is_artinian α :=
      Classical.byContradiction (fun h' => by
        simp only [Ring.is_artinian, not_forall] at h'
        let ⟨c, hdesc, hstab⟩ := h'
        simp only [chain.is_stable, not_exists, not_forall] at hstab
        exact absurd (chain.strictified.strict_infinite hstab) (h.left (chain.strictified hstab)
          ⟨chain.strictified.base hstab, chain.strictified.descending hstab hdesc⟩))

    theorem artinian_of_primes_maximal [NoetherianRing α] (hprime : Ring.Spec α ⊆ Ring.MaxSpec α) : Ring.is_artinian α :=
      artinian_of_finite_length (Ring.length_finite_iff_not_infinite.mpr fun h =>
        let S : Set (Ideal α) := {I | Ring.length_infinite (QClass I)}
        have hS : Nonempty S := ⟨0, Ring.length_infinite_of_isomorphism (quotient_zero_iso α).symm h⟩
        let ⟨I, hIinf, hImax⟩ := NoetherianRing.exists_maximal hS
        have hI : I.is_prime := ⟨NonTrivialRingProperIdeal (Ring.NonTrivial_of_length_infinite hIinf),
          fun a b hab => byContradiction fun h' =>
            have ⟨ha, hb⟩ := not_or_iff_and_not.mp h'
            have hsub := add.subset I (principal a)
            let f₁ := ideal_quotient_map I a
            have hf₁ := ideal_quotient_map.preserve_mul_left I a
            have hf₁' := ideal_quotient_map.injective I a
            have hf₁'' := ideal_quotient_map.extension_eq_image I a
            have hfin₁ : Ring.length_finite (QClass (ideal_quotient I a)) :=
              Ring.length_finite_iff_not_infinite.mpr (mt (hImax (ideal_quotient I a)) fun h =>
                hb (h (ideal_quotient.subset I a) ▸ hab))
            let f₂ := sub_quotient_hom hsub
            have hf₂ := sub_quotient_hom.surjective hsub
            have hfin₂ : Ring.length_finite (QClass (I + principal a)) :=
              Ring.length_finite_iff_not_infinite.mpr (mt (hImax (I + principal a)) fun h => by
                exact ha (h hsub ▸ ⟨0, I.has_zero, a, generator_in_principal a, zero_add a⟩))
            have hexact : f₁.image = f₂.kernel := (SubGroup.ext _ _).mp (by
              rw [sub_quotient_hom.kernel hsub, ideal_quotient_map.image I a, natural_hom.extension_add_I, extension_principal])
            absurd (Ring.length_finite_of_ses hf₁ hf₁' hf₁'' hf₂ hexact hfin₁ hfin₂)
              (mt Ring.length_finite_iff_not_infinite.mp (iff_not_not.mpr hIinf))⟩
        absurd hIinf (Ring.length_finite_iff_not_infinite.mp (Ring.field_length_finite (maximal_is_Field (hprime hI)))))
  end ArtinianRing
end M4R
