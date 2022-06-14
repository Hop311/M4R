import M4R.Algebra.Ring.Matsumura

namespace M4R

  namespace Ideal
    def chain (α : Type _) [Ring α] := Nat → Ideal α

    namespace chain
      variable [Ring α] (c : chain α)

      protected theorem ext {c₁ c₂ : chain α} : c₁ = c₂ ↔ ∀ n, c₁ n = c₂ n :=
        ⟨fun h _ => h ▸ rfl, funext⟩

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

      def shift (n : Nat) : chain α := fun k => c (n + k)

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
          (congrArg c (Nat.add_sub_of_le (Nat.le_of_lt h))).symm⟩ }
        { exact ⟨0, fun m hm => have h := Nat.not_lt.mp h
            (hN (n + m) (Nat.le_trans h (Nat.le_add_right n m))).trans (hN n h).symm⟩ }
      theorem shift_strict_infinite (n : Nat) (hc : c.strict_infinite) : (c.shift n).strict_infinite :=
        fun m => hc (n + m)
      theorem shift_strict_stable (n : Nat) (hc : c.strict_stable) : (c.shift n).strict_stable := by
        let ⟨N, hN₁, hN₂⟩ := hc
        byCases h : n < N
        { exact ⟨N - n, fun m hm => hN₁ (n + m) (Nat.add_comm m n ▸ (Nat.lt_sub_iff_right (Nat.le_of_lt h)).mp hm),
            fun m hm => (hN₂ (n + m) (Nat.add_comm n m ▸ Nat.sub_le_iff_right.mp hm)).trans (congrArg c
              (Nat.add_sub_of_le (Nat.le_of_lt h))).symm⟩ }
        { exact ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m), fun m hm =>
            have h := Nat.not_lt.mp h
            (hN₂ (n + m) (Nat.le_trans h (Nat.le_add_right n m))).trans (hN₂ n h).symm⟩ }
      theorem shift_stable_length (n : Nat) (hc : c.strict_stable) : (c.shift n).stable_length (shift_strict_stable n hc) =
        c.stable_length hc - n := by
          byCases h : n < c.stable_length hc
          { exact stable_length_eq _ (fun m hm => (c.stable_length_spec hc).left (n + m) (Nat.add_comm m n ▸
              (Nat.lt_sub_iff_right (Nat.le_of_lt h)).mp hm)) fun m hm => by
                have := (c.stable_length_spec hc).right _ (Nat.sub_le_iff_right.mp hm)
                rw [Nat.add_comm, ←Nat.sub_add_cancel (Nat.le_of_lt h), Nat.add_comm _ n] at this
                exact this }
          { exact Nat.sub_eq_zero_of_le (Nat.not_lt.mp h) ▸ stable_length_eq _ (fun m hm => absurd hm (Nat.not_lt_zero m))
              fun m hm => have h := Nat.not_lt.mp h; ((c.stable_length_spec hc).right (n + m) (Nat.le_trans h
                (Nat.le_add_right n m))).trans ((c.stable_length_spec hc).right n h).symm }

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

      theorem subsetneq_succ_of_strict_infinite_ascending (hc₁ : c.strict_infinite) (hc₂ : c.ascending) (n : Nat) :
        c n ⊊ c n.succ := Ideal.subsetneq.mpr ⟨hc₂ n, hc₁ n⟩
      theorem subsetneq_lt_of_strict_infinite_ascending (hc₁ : c.strict_infinite) (hc₂ : c.ascending) {m n : Nat} (h : m < n) :
        c m ⊊ c n := ProperSubset.trans_left (subsetneq_succ_of_strict_infinite_ascending hc₁ hc₂ m) (subset_ascending hc₂ h)

      theorem subsetneq_succ_of_strict_infinite_descending (hc₁ : c.strict_infinite) (hc₂ : c.descending) (n : Nat) :
        c n.succ ⊊ c n := Ideal.subsetneq.mpr ⟨hc₂ n, (hc₁ n).symm⟩
      theorem subsetneq_lt_of_strict_infinite_descending (hc₁ : c.strict_infinite) (hc₂ : c.descending) {m n : Nat} (h : m < n) :
        c n ⊊ c m := ProperSubset.trans_right (subset_descending hc₂ h) (subsetneq_succ_of_strict_infinite_descending hc₁ hc₂ m)

      theorem is_stable_of_strict_stable : c.strict_stable → c.is_stable :=
        fun ⟨N, hN⟩ => ⟨N, hN.right⟩

      theorem length_zero_of_strict_stable_0_eq_1 (hc : c.strict_stable) (h01 : c 0 = c 1) : c.stable_length hc = 0 :=
        Nat.le_zero.mp (Nat.not_lt.mp (mt ((c.stable_length_spec hc).left 0) (iff_not_not.mpr h01)))

      def length_infinite (S : Set (chain α)) : Prop := (∃ c ∈ S, c.strict_infinite) ∨
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
        have : ∀ I J : Ideal α, I = J := fun I J =>
          Ideal.ext.mp (Set.ext.mp fun _ => by simp only [all_trivial h10, I.has_zero, J.has_zero])
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

      theorem length_spec_of_finite {S : Set (chain α)} (h : length_finite S) :
        (∃ (c : chain α) (hc : c.strict_stable), c ∈ S ∧ c.stable_length hc = length_of_finite h) ∧
        ∀ (d : chain α) (hd : d.strict_stable), d ∈ S → d.stable_length hd  ≤ length_of_finite h :=
          have ⟨hc, hcS, h'⟩ := choose_spec h.right
          ⟨⟨choose h.right, hc, hcS, rfl⟩, h'⟩

      theorem length_eq_of_finite {S : Set (chain α)} (h₁ : ∀ c ∈ S, ¬c.strict_infinite) {c : chain α} (hc : c.strict_stable) (hcS : c ∈ S)
        (h₂ : ∀ (d : chain α) (hd : d.strict_stable), d ∈ S → d.stable_length hd  ≤ c.stable_length hc) :
          length_of_finite ⟨h₁, c, hc, hcS, h₂⟩ = c.stable_length hc :=
            have h := choose_spec (choose_spec (⟨h₁, c, hc, hcS, h₂⟩ : length_finite S).right)
            Nat.le_antisymm (h₂ _ _ h.left) (h.right c hc hcS)

      def const_chain (I : Ideal α) : chain α := fun _ => I

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
        variable [Ring α] [Ring β] {f : α →₊ β} (hf : Ideal.preserve_mul_right f)

        def contract_chain (c : chain β) : chain α := fun n => contraction hf (c n)

        theorem contract_chain.ascending {c : chain β} (hc : c.ascending) : (contract_chain hf c).ascending :=
          fun n => contraction.subset hf (hc n)
        theorem contract_chain.descending {c : chain β} (hc : c.descending) : (contract_chain hf c).descending :=
          fun n => contraction.subset hf (hc n)
        theorem contract_chain.is_prime {f : α →ᵣ₁ β} {c : chain β} (hc : c.is_prime) :
          (contract_chain f.preserve_mul_right c).is_prime := fun n => contraction_prime f (hc n)
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

        noncomputable def extend_chain (c : chain α) : chain β := fun n => extension f (c n)

        theorem extend_chain.ascending {c : chain α} (hc : c.ascending) : (extend_chain f c).ascending :=
          fun n => extension.subset f (hc n)
        theorem extend_chain.descending {c : chain α} (hc : c.descending) : (extend_chain f c).descending :=
          fun n => extension.subset f (hc n)
        theorem extend_chain.base {c : chain α} {I : Ideal α} (hc : c.base I) :
          (extend_chain f c).base (extension f I) := congrArg (extension f) hc

        theorem extension_contraction_of_isomorphism (c : chain α) (f : α ≅ᵣ β) :
          contract_chain f.preserve_mul_right (extend_chain f.hom c) = c :=
            chain.ext.mpr fun n => extension_contraction_eq_of_isomorphism f (c n)
      end extend_chain

      noncomputable def strict_increasing_index (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) : Nat → Nat
      | 0   => 0
      | n+1 => choose (h (strict_increasing_index h n))
      theorem strict_increasing_index.idx_strict (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (n : Nat) :
        strict_increasing_index h n < strict_increasing_index h n.succ :=
          Nat.lt_of_le_and_ne (choose (choose_spec (h (strict_increasing_index h n))))
            fun h' => choose_spec (choose_spec (h (strict_increasing_index h n))) (congrArg _ h'.symm)
      theorem strict_increasing_index.strict (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (n : Nat) :
        c (strict_increasing_index h n) ≠ c (strict_increasing_index h n.succ) :=
          (choose_spec (choose_spec (h (strict_increasing_index h n)))).symm

      noncomputable def strictified (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) : chain α :=
        fun n => match n with
        | 0   => 1
        | n+1 => c (strict_increasing_index h (if c 0 = 1 then n.succ else n))
      theorem strictified.base (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) : (strictified h).base 1 := rfl
      theorem strictified.base1 (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (h0 : c 0 = 1) :
        ∀ n, strictified h n = c (strict_increasing_index h n)
      | 0   => base h ▸ h0.symm
      | n+1 => by simp only [strictified, h0, ite_true]; rfl
      theorem strictified.not_base1 (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (h0 : c 0 ≠ 1) (n : Nat) :
        strictified h n.succ = c (strict_increasing_index h n) := by simp only [strictified, h0, ite_false]
      theorem strictified.descending (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) (hc : c.descending) : (strictified h).descending :=
        fun n => by
          byCases h0 : c 0 = 1
          { simp only [base1 h h0]; exact chain.subset_descending hc (Nat.le_of_lt (strict_increasing_index.idx_strict h n)) }
          { match n with
            | 0   => exact in_unit_ideal _
            | n+1 => simp only [not_base1 h h0]; exact chain.subset_descending hc (Nat.le_of_lt
              (strict_increasing_index.idx_strict h n)) }
      theorem strictified.strict_infinite (h : ∀ N, ∃ (n : Nat) (hn : N ≤ n), c n ≠ c N) : (strictified h).strict_infinite :=
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

        theorem next_term_ext {m n N : Nat} (h : n < N ∧ c n ≠ c N ∧ N < m ∧ ∀ l, l ≤ N → c l ≠ c m) (hmin : ∀ k, n < k ∧ c n ≠ c k ∧
          k < m ∧ (∀ l, l ≤ k → c l ≠ c m) → N ≤ k) : choose (minimal.min_exists _ (⟨N, h⟩ : next_term c m n) id) = N :=
            let m := minimal.min_exists _ (⟨N, h⟩ : next_term c m n) id
            Nat.le_antisymm ((choose_spec m).right N h) (hmin (choose m) (choose_spec m).left)
        theorem not_next_term_m (c : chain α) (m : Nat) : ¬ next_term c m m := fun ⟨_, h₁, _, h₂, _⟩ => Nat.lt_not_symm ⟨h₁, h₂⟩

        -- index of `n`ᵗʰ unique ideal in chain `c` (stabilised such that `c (m+k) = c m` for all `k`)
        noncomputable def strict_index (c : chain α) (m : Nat) : Nat → Nat
        | 0   => if c 0 = c m then m else 0
        | n+1 => if h : next_term c m (strict_index c m n) then choose (minimal.min_exists _ h id) else m

        theorem strict_index.def_zero_m {m : Nat} (h : c 0 = c m) : strict_index c m 0 = m := by
          simp only [strict_index, h, ite_true]
        theorem strict_index.def_zero_0 {m : Nat} (h : c 0 ≠ c m) : strict_index c m 0 = 0 := by
          simp only [strict_index, h, ite_false]
        theorem strict_index.zero_or_m (c : chain α) (m : Nat) : strict_index c m 0 = 0 ∨ strict_index c m 0 = m := by
          byCases h : c 0 = c m
          { exact Or.inr (def_zero_m h) }
          { exact Or.inl (def_zero_0 h) }
        theorem strict_index.c_zero (c : chain α) (m : Nat) : c (strict_index c m 0) = c 0 := by
          byCases h : c 0 = c m
          { exact (congrArg (c ·) (def_zero_m h)).trans h.symm }
          { exact (congrArg (c ·) (def_zero_0 h)) }
        theorem strict_index.def_exists {m n : Nat} (h : next_term c m (strict_index c m n)) :
          strict_index c m n.succ = choose (minimal.min_exists _ h id) := by simp only [strict_index, h, dite_true]
        theorem strict_index.neq_m_of_exists {m n : Nat} (h : next_term c m (strict_index c m n)) :
          strict_index c m n.succ ≠ m :=
            def_exists h ▸ Nat.ne_of_lt (choose_spec (minimal.min_exists _ h id)).left.right.right.left
        theorem strict_index.def_not_exists {m n : Nat} (h : ¬next_term c m (strict_index c m n)) :
          strict_index c m n.succ = m := by simp only [strict_index, h, dite_false]

        theorem strict_index.spec (c : chain α) (m n : Nat) : strict_index c m n.succ = m ∨
          (strict_index c m n < strict_index c m n.succ ∧ c (strict_index c m n) ≠ c (strict_index c m n.succ) ∧
          strict_index c m n.succ < m ∧ (∀ l, l ≤ strict_index c m n.succ → c l ≠ c m) ∧
          ∀ k, strict_index c m n ≤ k → k < strict_index c m n.succ → c k = c (strict_index c m n)) := by
            byCases h : next_term c m (strict_index c m n)
            { apply Or.inr
              have hmin := minimal.min_exists _ h id
              have ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ := choose_spec hmin;
              rw [def_exists h]
              exact ⟨h₁, h₂, h₃, h₄, fun k hk₁ hk₂ => (Nat.lt_or_eq_of_le hk₁).elim
                (fun hk₁ => byContradiction fun h => have hkm := Nat.lt_trans hk₂ h₃; absurd (h₅ k ⟨hk₁, Ne.symm h, hkm, fun l hl =>
                  h₄ l (Nat.le_trans hl (Nat.le_of_lt hk₂))⟩) (Nat.not_le.mpr hk₂))
                fun h => by rw [h]⟩ }
            { exact Or.inl (strict_index.def_not_exists h) }
        theorem strict_index.const_after_m {m n : Nat} (h : strict_index c m n = m) : ∀ k, n ≤ k → strict_index c m k = m := fun k hk =>
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
        theorem strict_index.m_of_stable {m n : Nat} (h : strict_index c m n = strict_index c m n.succ) :
          strict_index c m n = m := h ▸ (spec c m n).resolve_right fun h' => absurd h (Nat.ne_of_lt h'.left)
        theorem strict_index.stable_of_m {m n : Nat} (h : strict_index c m n = m) : strict_index c m n = strict_index c m n.succ :=
          h.trans (const_after_m h n.succ (Nat.le_succ _)).symm
        theorem strict_index.stable_after {m n : Nat} (h : strict_index c m n = strict_index c m n.succ) :
          ∀ k, n ≤ k → strict_index c m k = m := const_after_m (m_of_stable h)
        theorem strict_index.strict_before {m n : Nat} (h : strict_index c m n ≠ strict_index c m n.succ) :
          ∀ k, k ≤ n → strict_index c m k ≠ strict_index c m k.succ :=
            fun k hk h' => absurd (stable_of_m (stable_after h' n hk)) h
        theorem strict_index.strict_increasing {m n : Nat} (h : strict_index c m n ≠ strict_index c m n.succ) :
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
        theorem strict_index.neq_m_lt_length {m n : Nat} (hn : n < length c m) : strict_index c m n ≠ m :=
          fun h => absurd (stable_of_m h) ((length_spec c m).left n hn)
        theorem strict_index.eq_m_ge_length {m n : Nat} (hn : length c m ≤ n) : strict_index c m n = m :=
          (length_spec c m).right n hn
        theorem strict_index.length_zero {m : Nat} : length c m = 0 ↔ c m = c 0 :=
          ⟨fun h => c_zero c m ▸ (congrArg (c ·) (eq_m_ge_length (h ▸ Nat.le_refl 0)).symm),
          fun h => Nat.le_zero.mp (Nat.le_of_succ_le_succ (Nat.not_le.mp (mt neq_m_lt_length (iff_not_not.mpr (def_zero_m h.symm)))))⟩

        abbrev monotone_chain (c : chain α) : Prop := ∀ i k, i ≤ k → c i = c k → ∀ j, i ≤ j → j ≤ k → c j = c i
        theorem monotone_of_ascending (hc : c.ascending) : monotone_chain c :=
          fun i k hik hcik j hij hjk => Ideal.antisymm (hcik ▸ subset_ascending hc hjk) (subset_ascending hc hij)
        theorem monotone_of_descending (hc : c.descending) : monotone_chain c :=
          fun i k hik hcik j hij hjk => Ideal.antisymm (subset_descending hc hij) (hcik ▸ subset_descending hc hjk)

        theorem strict_index.next_term_m_succ {m n : Nat} (hmonotone : monotone_chain c) (h : strict_index c m n = strict_index c m.succ n)
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

        theorem strict_index.lt_length_m_succ {m n : Nat} (hmonotone : monotone_chain c)
          (hn : n < length c m) : strict_index c m n = strict_index c m.succ n := by
            induction n with
            | zero      =>
              have h0 := mt def_zero_m (neq_m_lt_length hn)
              have h0' := def_zero_0 fun h' => absurd (hmonotone 0 m.succ (Nat.zero_le _) h' m (Nat.zero_le m) (Nat.le_succ m)).symm h0
              exact (def_zero_0 h0).trans h0'.symm
            | succ n ih =>
              have : next_term c m (strict_index c m n) := of_not_not (mt def_not_exists (neq_m_lt_length hn))
              let ⟨k, hk⟩ := next_term_m_succ hmonotone (ih (Nat.lt_trans (Nat.lt.base n) hn)) this
              exact (def_exists this).trans (hk.trans (def_exists k).symm)

        theorem strict_index.ge_length_of_m_eq_m_succ {m n : Nat} (hmonotone : monotone_chain c)
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

        theorem strict_index.neq_succ_injective {m n : Nat} (h : strict_index c m n ≠ strict_index c m n.succ) : c (strict_index c m n) ≠ c (strict_index c m n.succ) := by
          byCases h' : strict_index c m n.succ = m
          { match n with
            | 0   =>
              rw [h'] at h ⊢; have := mt def_zero_m h
              rw [def_zero_0 this]; exact this
            | n+1 => rw [h']; exact ((spec c m n).resolve_left (fun h' => h (stable_of_m h'))).right.right.right.left _ (Nat.le_refl _) }
          { exact ((spec c m n).resolve_left h').right.left }
        theorem strict_index.eq_succ_injective {m n : Nat} (h : c (strict_index c m n) = c (strict_index c m n.succ)) : strict_index c m n = strict_index c m n.succ :=
          of_not_not (mt neq_succ_injective (iff_not_not.mpr h))
        theorem strict_index.m_injective {m n : Nat} (h : c (strict_index c m n) = c m) : strict_index c m n = m :=
          match n with
          | 0   => def_zero_m (c_zero c m ▸ h)
          | n+1 => by
            byCases h' : next_term c m (strict_index c m n)
            { have h'' := minimal.min_exists _ h' id;
              exact absurd (def_exists h' ▸ h) ((choose_spec h'').left.right.right.right
                (choose h'') (Nat.le_refl _)); }
            { exact def_not_exists h' }

        theorem strict_index.eq_length_of_m_neq_m_succ {m : Nat} (hmonotone : monotone_chain c)
          (hm : c m ≠ c m.succ) : c (strict_index c m.succ (length c m)) = c m := by
            byCases hl : length c m = 0
            { exact hl ▸ c_zero c m.succ ▸ (length_zero.mp hl).symm }
            { let ⟨k, hk⟩ := Nat.ne_zero_dest hl;
              rw [hk]
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
        theorem strict_index.length_succ_of_m_neq_m_succ {m : Nat} (hmonotone : monotone_chain c)
          (hm : c m ≠ c m.succ) : strict_index c m.succ (length c m).succ = m.succ :=
            have : ¬ next_term c m.succ (strict_index c m.succ (length c m)) := fun ⟨x, h₁, h₂, h₃, h₄⟩ => absurd (hmonotone (strict_index c m.succ
              (length c m)) m (Nat.le_trans (Nat.le_of_lt h₁) (Nat.le_of_succ_le_succ h₃)) (eq_length_of_m_neq_m_succ hmonotone hm) x (Nat.le_of_lt h₁)
              (Nat.le_of_succ_le_succ h₃)).symm h₂
            def_not_exists this

        theorem strict_index.succ_length_le (hmonotone : monotone_chain c) (m : Nat) : length c m ≤ length c m.succ :=
          Nat.not_lt.mp fun h => by
            have := le_m c m (length c m.succ)
            rw [lt_length_m_succ hmonotone h, eq_m_ge_length (Nat.le_refl _)] at this
            exact absurd this (Nat.not_le.mpr (Nat.lt.base m))
        theorem strict_index.succ_length_succ {m : Nat} (hc : c m ≠ c m.succ) (hmonotone : monotone_chain c) :
          length c m.succ = (length c m).succ :=
            Nat.le_antisymm
            (Nat.not_lt.mp (mt ((length_spec c m.succ).left (length c m).succ) (iff_not_not.mpr
              (stable_of_m (length_succ_of_m_neq_m_succ hmonotone hc)))))
            (Nat.succ_le_of_lt (Nat.not_le.mp (mt ((length_spec c m.succ).right (length c m)) fun h =>
              absurd ((eq_length_of_m_neq_m_succ hmonotone hc).symm.trans (congrArg (c ·) h)) hc)))
        theorem strict_index.succ_length_eq {m : Nat} (hc : c m = c m.succ) (hmonotone : monotone_chain c) :
          length c m.succ = length c m :=
            Nat.le_antisymm
            (Nat.not_lt.mp (mt ((length_spec c m.succ).left (length c m)) (iff_not_not.mpr ((ge_length_of_m_eq_m_succ
              hmonotone hc (Nat.le_refl _)).trans (ge_length_of_m_eq_m_succ hmonotone hc (Nat.le_succ _)).symm))))
            (succ_length_le hmonotone m)
      end strict_index

      noncomputable def strict_stabilised (c : chain α) (m : Nat) : chain α := fun n => c (strict_index c m n)

      theorem strict_stabilised.base (c : chain α) (m : Nat) : (strict_stabilised c m).base (c 0) := strict_index.c_zero c m
      theorem strict_stabilised.descending (hc : c.descending) (m : Nat) : (strict_stabilised c m).descending :=
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

      theorem strict_stabilised.succ_length_le (hmonotone : monotone_chain c) (m : Nat) :
        length c m ≤ length c m.succ := length_eq_length c m ▸ length_eq_length c m.succ ▸ strict_index.succ_length_le hmonotone m
      theorem strict_stabilised.succ_length_succ {m : Nat} (hmonotone : monotone_chain c) (hc : c m ≠ c m.succ) :
        length c m.succ = (length c m).succ := length_eq_length c m ▸ length_eq_length c m.succ ▸ strict_index.succ_length_succ hc hmonotone
      theorem strict_stabilised.succ_length_eq {m : Nat} (hmonotone : monotone_chain c) (hc : c m = c m.succ) :
        length c m.succ = length c m := length_eq_length c m ▸ length_eq_length c m.succ ▸ strict_index.succ_length_eq hc hmonotone

      def prefix_chain (I : Ideal α) (c : chain α) : chain α := fun n => match n with | 0 => I | n+1 => c n

      namespace prefix_chain

        theorem ascending {I : Ideal α} (hI : I ⊆ c 0) (hc : c.ascending) : (prefix_chain I c).ascending :=
          fun n => match n with | 0 => hI | n+1 => hc n
        theorem descending {I : Ideal α} (hI : c 0 ⊆ I) (hc : c.descending) : (prefix_chain I c).descending :=
          fun n => match n with | 0 => hI | n+1 => hc n
        theorem is_prime {I : Ideal α} (hI : I.is_prime) (hc : c.is_prime) : (prefix_chain I c).is_prime :=
          fun n => match n with | 0 => hI | n+1 => hc n

        theorem strict_stable {I : Ideal α} (hc : c.strict_stable) (hI : I ≠ c 0) : (prefix_chain I c).strict_stable :=
          ⟨(c.stable_length hc).succ, fun k hk => match k with | 0 => hI | k+1 => (c.stable_length_spec hc).left k (Nat.lt_of_succ_lt_succ hk),
            fun k hk => match k with | k+1 => (c.stable_length_spec hc).right k (Nat.le_of_succ_le_succ hk)⟩
        theorem stable_length {I : Ideal α} (hc : c.strict_stable) (hI : I ≠ c 0) :
          (prefix_chain I c).stable_length (strict_stable hc hI) = (c.stable_length hc).succ :=
            stable_length_eq _ (fun k hk => match k with | 0 => by exact hI | k+1 => (c.stable_length_spec hc).left k (Nat.lt_of_succ_lt_succ hk))
              fun k hk => match k with | k+1 => (c.stable_length_spec hc).right k (Nat.le_of_succ_le_succ hk)

        theorem strict_infinite {I : Ideal α} (hc : c.strict_infinite) (hI : I ≠ c 0) : (prefix_chain I c).strict_infinite :=
          fun n => match n with | 0 => hI | n+1 => hc n

      end prefix_chain
    end chain
  end Ideal
end M4R
