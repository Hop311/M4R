import M4R.Algebra.Ring.IdealChain

namespace M4R
  open Ideal

  namespace Ring.krull_dim
    open chain
    variable (α : Type _) [Ring α]

    def krull_chain : Set (chain α) := {c | c.is_prime ∧ c.ascending}

    def krull_dim_infinite : Prop := length_infinite (krull_chain α)
    def has_krull_dim : Prop := length_finite (krull_chain α)

    variable {α}

    theorem has_krull_dim_iff_not_infinite [Ring α] (h : Ring.is_NonTrivial α) : has_krull_dim α ↔ ¬krull_dim_infinite α :=
      let ⟨I, hI⟩ := exists_prime_ideal_of_nontrivial h
      length_finite_iff_not_infinite ⟨const_chain I, ⟨const_chain.is_prime hI,
        const_chain.ascending I⟩, const_chain.strict_stable I⟩

    noncomputable def dim : has_krull_dim α → Nat := length_of_finite
  end Ring.krull_dim

  namespace Ideal
    open chain
    variable [Ring α] (I : Ideal α)

    def length_chain : Set (chain α) := {c | c.base I ∧ c.descending}

    protected def length_finite : Prop := length_finite (length_chain I)
    protected def length_infinite : Prop := length_infinite (length_chain I)

    theorem exists_length_chain : ∃ c ∈ length_chain I, c.strict_stable :=
      ⟨const_chain I, ⟨const_chain.base I, const_chain.descending I⟩, const_chain.strict_stable I⟩

    protected theorem length_finite_iff_not_infinite {I : Ideal α} : I.length_finite ↔ ¬I.length_infinite :=
      length_finite_iff_not_infinite (exists_length_chain I)

    protected noncomputable def length : Ideal.length_finite I → Nat := chain.length_of_finite

    def height_chain : Set (chain α) := {c | c.base I ∧ c.descending ∧ c.is_prime}

    protected def height_finite : Prop := length_finite (height_chain I)
    protected def height_infinite : Prop := length_infinite (height_chain I)

    variable {P : Ideal α} (hP : P.is_prime)

    theorem height_chain.const : const_chain P ∈ height_chain P :=
      ⟨const_chain.base P, const_chain.descending P, const_chain.is_prime hP⟩

    theorem exists_height_chain : ∃ c ∈ height_chain P, c.strict_stable :=
      ⟨const_chain P, height_chain.const hP, const_chain.strict_stable P⟩

    protected theorem height_finite_iff_not_infinite : P.height_finite ↔ ¬P.height_infinite :=
      length_finite_iff_not_infinite (exists_height_chain hP)

    protected noncomputable def height : Ideal.height_finite P → Nat := length_of_finite

    protected theorem height_spec (h : Ideal.height_finite P) :
      (∃ (c : chain α) (hc : c.strict_stable), c ∈ height_chain P ∧ c.stable_length hc = Ideal.height h) ∧
      ∀ (d : chain α) (hd : d.strict_stable), d ∈ height_chain P → d.stable_length hd  ≤ Ideal.height h :=
        length_spec_of_finite h

    theorem height_chain.subset_base {c : chain α} (hc : c ∈ height_chain P) : ∀ n, c n ⊆ P :=
      chain.subset_base hc.left hc.right.left
    theorem height_chain.base_prime {c : chain α} (hc : c ∈ height_chain P) : P.is_prime :=
      chain.base_prime hc.left hc.right.right

    theorem is_prime_of_height_finite (h : Ideal.height_finite P) : P.is_prime :=
      let ⟨_, _, hc, _⟩ := (Ideal.height_spec h).left
      height_chain.base_prime hc

    def height_le (n : Nat) : Prop := ∃ h : I.height_finite, Ideal.height h ≤ n
    def height_eq (n : Nat) : Prop := ∃ h : I.height_finite, Ideal.height h = n

    theorem height_eq_rfl (h : Ideal.height_finite P) : P.height_eq (Ideal.height h) := ⟨h, rfl⟩

    theorem height_le_of_eq {n : Nat} : P.height_eq n → P.height_le n := fun ⟨h, hn⟩ => ⟨h, Nat.le_of_eq hn⟩
    theorem height_eq_of_le {n : Nat} : P.height_le n → ∃ m, P.height_eq m ∧ m ≤ n := fun ⟨h, hn⟩ => ⟨Ideal.height h, ⟨h, rfl⟩, hn⟩

    theorem height_le_trans {m n : Nat} (hmn : m ≤ n) : P.height_le m → P.height_le n := fun ⟨h, hm⟩ => ⟨h, Nat.le_trans hm hmn⟩

    theorem height_eq_of_finite (h₁ : ∀ c ∈ height_chain P, ¬c.strict_infinite) {c : chain α} (hc : c.strict_stable) (hch : c ∈ height_chain P)
      (h₂ : ∀ (d : chain α) (hd : d.strict_stable), d ∈ height_chain P → d.stable_length hd ≤ c.stable_length hc) :
        Ideal.height ⟨h₁, c, hc, hch, h₂⟩ = c.stable_length hc := length_eq_of_finite h₁ hc hch h₂

    theorem height_le_of_strict_lt {N : Nat} (h : ∀ c ∈ height_chain P, (∀ n, n < N → c n ≠ c n.succ) → c N = c N.succ) : P.height_le N :=
      have hle : ∀ c ∈ height_chain P, (hc : c.strict_stable) → c.stable_length hc ≤ N :=
        fun c hch hc => Classical.byContradiction fun hN => have hN := Nat.not_le.mp hN
          absurd (h c hch (fun n hn => (c.stable_length_spec hc).left n (Nat.lt_trans hn hN))) ((c.stable_length_spec hc).left N hN)
      have : P.height_finite := ⟨fun c hc hcstrict => absurd (h c hc (fun n _ => hcstrict n)) (hcstrict N),
        let ⟨⟨c, hc⟩, hch, hcmax⟩ := maximal.max_exists {c : (Subtype chain.strict_stable) | c.val ∈ height_chain P} ⟨⟨const_chain P, const_chain.strict_stable P⟩,
          height_chain.const hP⟩ (fun c => c.val.stable_length c.property) ⟨N, fun ⟨c, hc⟩ hch => hle c hch hc⟩
        ⟨c, hc, hch, fun d hd => hcmax ⟨d, hd⟩⟩⟩
      ⟨this, let ⟨c, hc, hch, hce⟩ := (Ideal.height_spec this).left; hce ▸ hle c hch hc⟩

    theorem height_eq_zero : P.height_eq 0 ↔ P.minimal_prime_ideal_of 0 :=
      ⟨fun ⟨hP, he⟩ => ⟨is_prime_of_height_finite hP, zero_ideal_in P, by
        intro J hJ _ hJP
        apply Classical.byContradiction; intro hJP'
        let c : chain α := prefix_chain P (const_chain J)
        let hc : c.strict_stable := prefix_chain.strict_stable (const_chain.strict_stable J) (Ne.symm hJP')
        have : c.stable_length hc = 0 := Nat.le_zero.mp (he ▸ (Ideal.height_spec hP).right c hc ⟨rfl, prefix_chain.descending
          hJP (const_chain.descending J), prefix_chain.is_prime (is_prime_of_height_finite hP) (const_chain.is_prime hJ)⟩)
        have : c 1 = c 0 := this ▸ (c.stable_length_spec hc).right 1 (this ▸ Nat.le_of_lt Nat.zero_lt_one)
        exact absurd this hJP'⟩,
      fun ⟨h₁, _, h₂⟩ =>
        let ⟨h, h0⟩ : P.height_le 0 := height_le_of_strict_lt h₁ (fun c hch h => hch.left ▸
          (h₂ (hch.right.right 1) (zero_ideal_in _) (hch.left ▸ hch.right.left 0)).symm)
        ⟨h, Nat.le_zero.mp h0⟩⟩

    theorem height_gt_one {I J K : Ideal α} (hI : I.is_prime) (hJ : J.is_prime) (hK : K.is_prime) (hIJ : I ⊊ J) (hJK : J ⊊ K) :
      ¬K.height_le 1 := fun ⟨h, h1⟩ =>
        let c : chain α := fun n => match n with | 0 => K | 1 => J | n+2 => I
        have hc₁ : ∀ n, n < 2 → c n ≠ c n.succ := fun n hn =>
          match n with
          | 0 => (Ideal.subsetneq.mp hJK).right.symm
          | 1 => (Ideal.subsetneq.mp hIJ).right.symm
          | n+2 => absurd hn (Nat.not_lt.mpr (Nat.le_add_left 2 n))
        have hc₂ : ∀ n, 2 ≤ n → c n = c 2 := fun n hn => match n with | n+2 => rfl
        have := (Ideal.height_spec h).right c ⟨2, hc₁, hc₂⟩ ⟨rfl,
          fun n => match n with | 0 => hJK.left | 1 => hIJ.left | n+2 => Subset.refl _,
          fun n => match n with | 0 => hK | 1 => hJ | n+2 => hI⟩
        absurd (chain.stable_length_eq 2 hc₁ hc₂ ▸ Nat.le_trans this h1 : 2 ≤ 1)
          (Nat.not_le.mpr (Nat.succ_lt_succ Nat.zero_lt_one))

    theorem height_le_succ {n : Nat} (h : ∀ Q : Ideal α, Q.is_prime → Q ⊊ P → Q.height_le n) : P.height_le n.succ := by
      have : ∀ c ∈ height_chain P, ¬c.strict_infinite := fun c hch hcstrict => by
        let ⟨h, hn⟩ := h (c 1) (hch.right.right 1) (Ideal.subsetneq.mpr ⟨hch.left ▸ hch.right.left 0, hch.left ▸ (hcstrict 0).symm⟩)
        exact absurd (chain.shift_strict_infinite 1 hcstrict) (h.left (c.shift 1) ⟨rfl, chain.shift_descending 1 hch.right.left,
          chain.shift_prime 1 hch.right.right⟩)
      byCases hex : ∃ Q : Ideal α, Q.is_prime ∧ Q ⊊ P
      { let ⟨m, hm, hmax⟩ := maximal.max_exists {m | ∃ Q : Ideal α, Q.is_prime ∧ Q ⊊ P ∧ Q.height_eq m}
          (let ⟨Q, hQ, hQP⟩ := hex; let ⟨h, _⟩ := h Q hQ hQP; ⟨Ideal.height h, Q, hQ, hQP, height_eq_rfl h⟩)
          id ⟨n, by intro m ⟨Q, hQ₁, hQ₂, ⟨h', hm⟩⟩; let ⟨_, hn⟩ := h Q hQ₁ hQ₂; exact hm ▸ hn⟩
        let ⟨Q, hQ₁, hQ₂, ⟨hQ₃, hQm⟩⟩ := hm
        let ⟨c, hcstrict, hch, hceq⟩ := (Ideal.height_spec hQ₃).left
        let d : chain α := prefix_chain P c
        have hPc : P ≠ c 0 := hch.left ▸ (Ideal.subsetneq.mp hQ₂).right.symm
        have hdh : d ∈ height_chain P := ⟨rfl, prefix_chain.descending (hch.left ▸ hQ₂.left) hch.right.left,
          prefix_chain.is_prime hP hch.right.right⟩
        have hdmax : ∀ (d' : chain α) (hd' : d'.strict_stable), d' ∈ height_chain P → d'.stable_length hd' ≤
          d.stable_length (prefix_chain.strict_stable hcstrict hPc) := by
            intro d' hd' hdh'; byCases hd'01 : d' 1 = P
            { exact Nat.le_trans (Nat.not_lt.mp (mt ((d'.stable_length_spec hd').left 0)
              (iff_not_not.mpr (hdh'.left ▸ hd'01.symm)))) (Nat.zero_le _) }
            { rw [prefix_chain.stable_length hcstrict hPc]
              let ⟨hd1, hd1n⟩ := h (d' 1) (hdh'.right.right 1) (Ideal.subsetneq.mpr ⟨hdh'.left ▸ hdh'.right.left 0, hd'01⟩)
              have := (Ideal.height_spec hd1).right (d'.shift 1) (chain.shift_strict_stable 1 hd')
                ⟨rfl, chain.shift_descending 1 hdh'.right.left, chain.shift_prime 1 hdh'.right.right⟩;
              rw [chain.shift_stable_length 1 hd'] at this
              exact Nat.le_trans (Nat.le_succ_pred _) (Nat.succ_le_succ (Nat.le_trans this (hceq ▸ hQm ▸ hmax (Ideal.height hd1)
                ⟨d' 1, hdh'.right.right 1, Ideal.subsetneq.mpr ⟨hdh'.left ▸ hdh'.right.left 0, hd'01⟩, height_eq_rfl hd1⟩))) }
        exact ⟨⟨this, ⟨d, prefix_chain.strict_stable hcstrict hPc, hdh, hdmax⟩⟩, by
          rw [height_eq_of_finite this (prefix_chain.strict_stable hcstrict hPc) hdh hdmax, prefix_chain.stable_length hcstrict hPc]
          let ⟨_, hn⟩ := h Q hQ₁ hQ₂; exact Nat.succ_le_succ (hceq ▸ hn)⟩ }
      { let ⟨h, h0⟩ := height_eq_zero.mpr ⟨hP, zero_ideal_in P, fun hJ _ hJP => Classical.byContradiction fun h =>
          absurd (Ideal.subsetneq.mpr ⟨hJP, h⟩) (not_and.mp (not_exists.mp hex _) hJ)⟩; exact ⟨h, h0 ▸ Nat.zero_le _⟩ }

    theorem height_le_subset {Q : Ideal α} (hPQ : P ⊆ Q) {n : Nat} (hQn : Q.height_le n) : P.height_le n := by
      byCases hPQeq : P = Q
      { exact hPQeq ▸ hQn }
      { let ⟨hQfin, hQfinn⟩ := hQn
        have : P.height_finite := Classical.byContradiction fun h => (of_not_not (mt (Ideal.height_finite_iff_not_infinite hP).mpr h)).elim
          (fun ⟨c, hch, hcstrict⟩ => absurd (prefix_chain.strict_infinite hcstrict (hch.left ▸ Ne.symm hPQeq))
            (hQfin.left (prefix_chain Q c) ⟨rfl, prefix_chain.descending (hch.left ▸ hPQ) hch.right.left,
              prefix_chain.is_prime (is_prime_of_height_finite hQfin) hch.right.right⟩))
          (fun h =>
            let ⟨c, hc, hch, hle⟩ := h (Ideal.height hQfin)
            have hQc : Q ≠ c 0 := hch.left ▸ Ne.symm hPQeq
            have := (Ideal.height_spec hQfin).right (prefix_chain Q c) (prefix_chain.strict_stable hc hQc) ⟨rfl, prefix_chain.descending
              (hch.left ▸ hPQ) hch.right.left, prefix_chain.is_prime (is_prime_of_height_finite hQfin) hch.right.right⟩
            absurd (prefix_chain.stable_length hc hQc ▸ this) (Nat.not_le.mpr (Nat.succ_le_succ hle)));
        exact ⟨this, Nat.le_trans (let ⟨c, hc, hch, hceq⟩ := (Ideal.height_spec this).left
          have hQc : Q ≠ c 0 := hch.left ▸ Ne.symm hPQeq
          have := (Ideal.height_spec hQfin).right (prefix_chain Q c) (prefix_chain.strict_stable hc hQc) ⟨rfl, prefix_chain.descending
            (hch.left ▸ hPQ) hch.right.left, prefix_chain.is_prime (is_prime_of_height_finite hQfin) hch.right.right⟩
          Nat.le_trans (Nat.le_succ _) (hceq ▸ prefix_chain.stable_length hc hQc ▸ this)) hQfinn⟩ }

    open localisation

    noncomputable def localise_chain (S : MultiplicativeSet α) (c : chain α) : chain (localisation S) :=
      extend_chain (natural_hom S).hom c

    noncomputable def delocalise_chain (S : MultiplicativeSet α) (c : chain (localisation S)) : chain α :=
      contract_chain (natural_hom S).preserve_mul_right c

    variable {S : MultiplicativeSet α} (hPS : Set.disjoint P.subset S.subset)

    theorem localise_chain.is_height_chain {c : chain α} (hc : c ∈ height_chain P) : localise_chain S c ∈ height_chain (localise_ideal S P) :=
      ⟨extend_chain.base _ hc.left, extend_chain.descending _ hc.right.left, fun n => localise_ideal.prime
        (hc.right.right n) (Set.disjoint.subset_left (height_chain.subset_base hc n) hPS)⟩

    theorem delocalise_chain.is_height_chain {c : chain (localisation S)} (hch : c ∈ height_chain (localise_ideal S P)) : delocalise_chain S c ∈ height_chain P :=
      ⟨(hch.left ▸ localise_ideal.prime_loc_deloc hP hPS : delocalise_ideal S (c 0) = P), contract_chain.descending _ hch.right.left,
      fun n => delocalise_ideal.prime (hch.right.right n)⟩

    theorem localise_chain.imp_strict_infinite {c : chain α} (hch : c ∈ height_chain P) (hc : c.strict_infinite) :
      (localise_chain S c).strict_infinite := fun n h => hc n (localise_ideal.prime_loc_deloc (hch.right.right n)
        (Set.disjoint.subset_left (height_chain.subset_base hch n) hPS) ▸ localise_ideal.prime_loc_deloc (hch.right.right n.succ)
          (Set.disjoint.subset_left (height_chain.subset_base hch n.succ) hPS) ▸ congrArg (delocalise_ideal S ·) h)

    theorem localise_chain.imp_strict_stable {c : chain α} (hch : c ∈ height_chain P) (hc : c.strict_stable) : (localise_chain S c).strict_stable :=
      let ⟨N, hN₁, hN₂⟩ := hc
      ⟨N, fun n hn heq => hN₁ n hn (by
        have : delocalise_ideal S (localise_ideal S (c n)) = delocalise_ideal S (localise_ideal S (c n.succ)) := congrArg (delocalise_ideal S ·) heq
        rw [localise_ideal.prime_loc_deloc (hch.right.right n) (Set.disjoint.subset_left (height_chain.subset_base hch n) hPS),
          localise_ideal.prime_loc_deloc (hch.right.right n.succ) (Set.disjoint.subset_left (height_chain.subset_base hch n.succ) hPS)] at this
        exact this),
      fun n hn => congrArg (localise_ideal S ·) (hN₂ n hn)⟩

    theorem delocalise_chain.imp_strict_stable {c : chain (localisation S)} (hch : c ∈ height_chain (localise_ideal S P)) (hc : c.strict_stable) :
      (delocalise_chain S c).strict_stable :=
        let ⟨N, hN₁, hN₂⟩ := hc
        ⟨N, fun n hn heq => hN₁ n hn (by
          have : localise_ideal S (delocalise_ideal S (c n)) = localise_ideal S (delocalise_ideal S (c n.succ)) := congrArg (localise_ideal S ·) heq
          simp only [delocalise_ideal.deloc_loc] at this; exact this),
        fun n hn => congrArg (delocalise_ideal S ·) (hN₂ n hn)⟩

    theorem localise_chain.preserve_length {c : chain α} (hch : c ∈ height_chain P) (hc : c.strict_stable) :
      (localise_chain S c).stable_length (localise_chain.imp_strict_stable hPS hch hc) = c.stable_length hc :=
        chain.stable_length_eq _ (fun n hn heq => (c.stable_length_spec hc).left n hn (by
          have : delocalise_ideal S (localise_ideal S (c n)) = delocalise_ideal S (localise_ideal S (c n.succ)) := congrArg (delocalise_ideal S ·) heq
          rw [localise_ideal.prime_loc_deloc (hch.right.right n) (Set.disjoint.subset_left (height_chain.subset_base hch n) hPS),
            localise_ideal.prime_loc_deloc (hch.right.right n.succ) (Set.disjoint.subset_left (height_chain.subset_base hch n.succ) hPS)] at this
          exact this))
        fun n hn => congrArg (localise_ideal S ·) ((c.stable_length_spec hc).right n hn)

    theorem delocalise_chain.preserve_length {c : chain (localisation S)} (hch : c ∈ height_chain (localise_ideal S P)) (hc : c.strict_stable) :
      (delocalise_chain S c).stable_length (delocalise_chain.imp_strict_stable hch hc) = c.stable_length hc :=
        chain.stable_length_eq _ (fun n hn heq => (c.stable_length_spec hc).left n hn (by
          have : localise_ideal S (delocalise_ideal S (c n)) = localise_ideal S (delocalise_ideal S (c n.succ)) := congrArg (localise_ideal S ·) heq
          simp only [delocalise_ideal.deloc_loc] at this; exact this))
        fun n hn => congrArg (delocalise_ideal S ·) ((c.stable_length_spec hc).right n hn)

    theorem local_height_finite (h : (localise_ideal S P).height_finite) : P.height_finite :=
      ⟨fun c hch hc => absurd (localise_chain.imp_strict_infinite hPS hch hc) (h.left (localise_chain S c) (localise_chain.is_height_chain hPS hch)),
      let ⟨c, hc, hch, hmax⟩ := h.right; ⟨delocalise_chain S c, delocalise_chain.imp_strict_stable hch hc, delocalise_chain.is_height_chain hP hPS hch,
      fun d hd hdh => localise_chain.preserve_length hPS hdh hd ▸ delocalise_chain.preserve_length hch hc ▸
        hmax (localise_chain S d) (localise_chain.imp_strict_stable hPS hdh hd) (localise_chain.is_height_chain hPS hdh)⟩⟩

    theorem local_height_preserve (h : (localise_ideal S P).height_finite) : Ideal.height h = Ideal.height (local_height_finite hP hPS h) :=
      Nat.le_antisymm
        (by
          let ⟨c, hc, hch, heq⟩ := (Ideal.height_spec h).left
          rw [←heq, ←delocalise_chain.preserve_length hch hc]
          exact (Ideal.height_spec (local_height_finite hP hPS h)).right (delocalise_chain S c)
            (delocalise_chain.imp_strict_stable hch hc) (delocalise_chain.is_height_chain hP hPS hch))
        (by
          let ⟨c, hc, hch, heq⟩ := (Ideal.height_spec (local_height_finite hP hPS h)).left
          rw [←heq, ←localise_chain.preserve_length hPS hch hc]
          exact (Ideal.height_spec h).right (localise_chain S c) (localise_chain.imp_strict_stable hPS hch hc) (localise_chain.is_height_chain hPS hch))

    theorem local_height_le (n : Nat) (h : (localise_ideal S P).height_le n) : P.height_le n :=
      let ⟨h, hn⟩ := h; ⟨local_height_finite hP hPS h, local_height_preserve hP hPS h ▸ hn⟩

  end Ideal

  namespace Ring
    variable [Ring α]

    private def reverse_chain_at (c : chain α) (N : Nat) (P : Ideal α) : chain α :=
      fun n => match n with | 0 => P | n+1 => c (N - n)

    namespace reverse_chain_at
      variable {c : chain α} (hcprime : c.is_prime) (hcasc : c.ascending) {N : Nat} (hcstrict : ∀ n, n < N → c n ≠ c n.succ)
        {P : Ideal α} (hP : P.is_prime) (hNP : c N ⊊ P)

      theorem is_strict_stable : (reverse_chain_at c N P).strict_stable :=
        ⟨N.succ, fun n hn => match n with
          | 0   => (Ideal.subsetneq.mp hNP).right.symm
          | n+1 => (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hn)) ▸ (hcstrict (N - n).pred
            (Nat.lt_of_succ_lt_succ ((Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hn))).symm ▸
            Nat.lt_of_le_of_lt (N.sub_le n) (Nat.lt.base N)))).symm : c (N - n) ≠ c (N - n).pred),
        fun n hn => match n with
          | n+1 => (N.sub_self ▸ congrArg _ ((N.sub_eq_zero_iff_le n).mpr (Nat.le_of_succ_le_succ hn)) : c (N - n) = c (N - N))⟩

      theorem is_height_chain : reverse_chain_at c N P ∈ height_chain P :=
          ⟨rfl, fun n => match n with | 0 => hNP.left | n+1 => chain.subset_ascending hcasc (N - n).pred_le,
            fun n => match n with | 0 => hP | n+1 => hcprime (N - n)⟩

      theorem length_eq_N_succ : (reverse_chain_at c N P).stable_length (is_strict_stable hcstrict hNP) = N.succ :=
        chain.stable_length_eq N.succ (fun n hn => match n with
          | 0   => by exact (Ideal.subsetneq.mp hNP).right.symm
          | n+1 => (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hn)) ▸ (hcstrict (N - n).pred
            (Nat.lt_of_succ_lt_succ ((Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hn))).symm ▸
            Nat.lt_of_le_of_lt (N.sub_le n) (Nat.lt.base N)))).symm : c (N - n) ≠ c (N - n).pred))
        fun n hn => match n with
          | n+1 => (N.sub_self ▸ congrArg _ ((N.sub_eq_zero_iff_le n).mpr (Nat.le_of_succ_le_succ hn)) : c (N - n) = c (N - N))
    end reverse_chain_at

    private def reverse_chain (c : chain α) (N : Nat) : chain α := fun n => c (N - n)

    namespace reverse_chain
      variable {c : chain α} (hcprime : c.is_prime) (hcdesc : c.descending) {N : Nat} (hcstrict : ∀ n, n < N → c n ≠ c n.succ)

      theorem is_strict_stable : (reverse_chain c N).strict_stable :=
        ⟨N, fun n hn => (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hn) ▸ (hcstrict (N - n).pred
          (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hn) ▸ N.sub_le n)).symm : c (N - n) ≠ c (N - n.succ)),
        fun n hn => (by rw [Nat.sub_self, Nat.sub_eq_zero_of_le hn] : c (N - n) = c (N - N))⟩

      theorem is_krull_chain : reverse_chain c N ∈ krull_dim.krull_chain α :=
        ⟨fun n => hcprime (N - n), fun n => (match N - n with | 0 => Subset.refl _ | n+1 => hcdesc n : c (N - n) ⊆ c (N - n).pred)⟩

      theorem length_eq_N : (reverse_chain c N).stable_length (is_strict_stable hcstrict) = N :=
        chain.stable_length_eq N
          (fun n hn => (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hn) ▸ (hcstrict (N - n).pred
            (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hn) ▸ N.sub_le n)).symm : c (N - n) ≠ c (N - n.succ)))
          fun n hn => (by rw [Nat.sub_self, Nat.sub_eq_zero_of_le hn] : c (N - n) = c (N - N))

    end reverse_chain

    theorem krull_dim.has_krull_dim_of_maximal_height_le (hnontriv : Nonempty (MaxSpec α)) (N : Nat) (hN : ∀ M : Ideal α, M.is_maximal → M.height_le N) :
      has_krull_dim α :=
        ⟨fun c ⟨hcprime, hcasc⟩ hcstrict => by
          let ⟨M, hNM, hM⟩ := exists_maximal_containing (proper_ideal_subsetneq (chain.subsetneq_succ_of_strict_infinite_ascending hcstrict hcasc N))
          have hcNM : c N ⊊ M := Ideal.subsetneq.mpr ⟨hNM, fun h => ((hM.right (h ▸ hcasc N)).elim (h ▸ (hcstrict N).symm) (hcprime N.succ).left)⟩
          let ⟨hfinM, hfinMN⟩ := hN M hM
          let ⟨⟨d, hd, hdh, hdfinM⟩, hmax⟩ := Ideal.height_spec hfinM
          have := hmax (reverse_chain_at c N M) (reverse_chain_at.is_strict_stable (fun n _ => hcstrict n) hcNM)
            (reverse_chain_at.is_height_chain hcprime hcasc (maximal_is_prime hM) hcNM)
          rw [reverse_chain_at.length_eq_N_succ (fun n _ => hcstrict n) hcNM] at this
          exact absurd (Nat.le_trans this hfinMN) (Nat.not_le.mpr (Nat.lt.base N)),
        let ⟨⟨M, hM⟩, _, hmax⟩ := maximal.max_exists (@Set.Universal (Subtype (MaxSpec α))) ⟨Classical.choice hnontriv, trivial⟩
          (fun ⟨M, hM⟩ => Classical.choose (height_eq_of_le (hN M hM)))
          ⟨N, fun ⟨M, hM⟩ _ => (Classical.choose_spec (height_eq_of_le (hN M hM))).right⟩
        let m := Classical.choose (height_eq_of_le (hN M hM))
        have ⟨⟨hfinM, hfinMm⟩, hmN⟩ := Classical.choose_spec (height_eq_of_le (hN M hM))
        let ⟨⟨c, hc, hch, hcfinM⟩, hcmax⟩ := Ideal.height_spec hfinM
        ⟨reverse_chain c (c.stable_length hc), reverse_chain.is_strict_stable (c.stable_length_spec hc).left,
          reverse_chain.is_krull_chain hch.right.right hch.right.left, fun d hd ⟨hdprime, hdasc⟩ => by
            rw [reverse_chain.length_eq_N (c.stable_length_spec hc).left]
            apply Classical.byContradiction; intro h
            have h := Nat.not_le.mp h
            let ⟨M', hcM', hM'⟩ := exists_maximal_containing (proper_ideal_subsetneq (Ideal.subsetneq.mpr ⟨hdasc _, (d.stable_length_spec hd).left _ h⟩))
            have hdcM' : d (c.stable_length hc) ⊊ M' := Ideal.subsetneq.mpr ⟨hcM', fun h' => (hM'.right (h' ▸ hdasc (c.stable_length hc))).elim
              (fun h'' => absurd (h'.trans h''.symm) ((d.stable_length_spec hd).left _ h)) (hdprime _).left⟩
            let m' := Classical.choose (height_eq_of_le (hN M' hM'))
            have ⟨⟨hfinM', hfinMm'⟩, hm'N⟩ := Classical.choose_spec (height_eq_of_le (hN M' hM'))
            let ⟨⟨c', hc', hch', hcfinM'⟩, hcmax'⟩ := Ideal.height_spec hfinM'
            have := hcmax' (reverse_chain_at d (c.stable_length hc) M') (reverse_chain_at.is_strict_stable
              (fun n hn => (d.stable_length_spec hd).left n (Nat.lt_trans hn h)) hdcM')
              (reverse_chain_at.is_height_chain hdprime hdasc (maximal_is_prime hM') hdcM')
            rw [reverse_chain_at.length_eq_N_succ (fun n hn => (d.stable_length_spec hd).left n (Nat.lt_trans hn h)) hdcM', hcfinM, hfinMm', hfinMm] at this
            exact absurd this (Nat.not_le.mpr (Nat.succ_le_succ (hmax ⟨M', hM'⟩ trivial)))⟩⟩

    variable (α : Type _) [Ring α]

    protected def length_finite : Prop := Ideal.length_finite (1 : Ideal α)
    protected def length_infinite : Prop := Ideal.length_infinite (1 : Ideal α)

    variable {α}

    protected theorem length_finite_iff_not_infinite : Ring.length_finite α ↔ ¬Ring.length_infinite α :=
      Ideal.length_finite_iff_not_infinite

    theorem length_infinite_of_isomorphism [Ring β] (f : α ≅ᵣ β) (h : Ring.length_infinite β) :
      Ring.length_infinite α := by
        simp only [Ring.length_infinite, Ideal.length_infinite]
        have : Function.image' (chain.contract_chain f.preserve_mul_right) (Ideal.length_chain 1) = Ideal.length_chain 1 :=
          Set.ext.mp fun x => ⟨fun ⟨y, ⟨hy₁, hy₂⟩, hyx⟩ => ⟨hyx ▸ contraction_unit _ ▸ chain.contract_chain.base _ hy₁, hyx ▸
            chain.contract_chain.descending _ hy₂⟩, fun ⟨hx₁, hx₂⟩ => ⟨chain.extend_chain f.hom x, ⟨extension_unit_of_surjective
            f.toMIsomorphism.to_surjective ▸ chain.extend_chain.base f.hom hx₁, chain.extend_chain.descending f.hom hx₂⟩,
            x.extension_contraction_of_isomorphism f⟩⟩
        exact this ▸ chain.contract_chain.length_infinite f.preserve_mul_right f.toMIsomorphism.to_surjective h

    open NCSemiring Group

    theorem NonTrivial_of_length_infinite : Ring.length_infinite α → Ring.is_NonTrivial α :=
      chain.NonTrivial_of_length_infinite

    theorem field_length_finite [Ring α] (h : Ring.is_Field α) : Ring.length_finite α :=
      chain.field_length_finite_of_descending h (exists_length_chain 1) (fun _ => And.right)

    theorem finite_chain_ends_zero [Ring α] {c : chain α} (N : Nat) (hltN : ∀ n, n < N → c n ≠ c n.succ) (hNle : ∀ n, N ≤ n → c n = c N)
      (hbase : c.base 1) (hdesc : c.descending) (hmax : ∀ (d : chain α) (hd : d.strict_stable),
        (d.base 1 ∧ d.descending) → d.stable_length hd ≤ c.stable_length ⟨N, hltN, hNle⟩) : c N = 0 := by
          apply Classical.byContradiction; intro h0
          let d : chain α := fun n => if n ≤ N then c n else 0
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

    theorem length_finite_of_ses [Ring α] [Ring β] [Ring γ] {f₁ : α →₊ β} (hf₁ : preserve_mul_right f₁)
      (hf₁' : Function.injective f₁.hom) (hf₁'' : ∀ I, (extension f₁.hom I).subset = Function.image' f₁.hom I.subset)
      {f₂ : β →ᵣ γ} (hf₂ : Function.surjective f₂.hom) (hexact : f₁.image.subset = f₂.kernel.subset)
        (hα : Ring.length_finite α) (hγ : Ring.length_finite γ) : Ring.length_finite β :=
          have hstrict : ∀ I J : Ideal β, I ⊊ J → contraction hf₁ I ≠ contraction hf₁ J ∨ extension f₂.hom I ≠ extension f₂.hom J :=
            fun I J h => by
              byCases he : extension f₂.hom I = extension f₂.hom J
              { let ⟨x, hxI, hxJ, hxf⟩ := exists_kernel_element hf₂ h he
                let ⟨y, hy⟩ := (hexact ▸ hxf : x ∈ f₁.image.subset);
                exact Or.inl (fun h => absurd ((hy ▸ (Ideal.ext'.mp h y).mpr : x ∈ J → x ∈ I) hxJ) hxI) }
              { exact Or.inr he }
          ⟨fun c ⟨hc₁, hc₂⟩ hc₃ => by
            byCases h : ∀ (N : Nat), ∃ (n : Nat) (hn : N ≤ n), chain.contract_chain hf₁ c n ≠ chain.contract_chain hf₁ c N
            { exact absurd (chain.strictified.strict_infinite h) (hα.left (chain.strictified h) ⟨chain.strictified.base h,
              chain.strictified.descending h (chain.contract_chain.descending hf₁ hc₂)⟩) }
            { simp only [not_forall, not_exists, iff_not_not] at h
              let ⟨N, hN⟩ := h
              have hstrict : ∀ n, N ≤ n → chain.extend_chain f₂.hom c n ≠ chain.extend_chain f₂.hom c n.succ :=
                fun n hn => ((hstrict (c n.succ) (c n) (chain.subsetneq_succ_of_strict_infinite_descending hc₃ hc₂ n)).resolve_left
                  (iff_not_not.mpr ((hN n.succ (Nat.le_trans hn (Nat.le_succ n))).trans (hN n hn).symm))).symm
              let c' : chain γ := fun n => match n with
                | 0   => 1
                | n+1 => (chain.extend_chain f₂.hom c).shift N.succ n
              have hdesc' : c'.descending := fun n => match n with
                | 0   => in_unit_ideal _
                | n+1 => chain.shift_descending N.succ (chain.extend_chain.descending f₂.hom hc₂) n
              have : c'.strict_infinite := by
                intro n
                match n with
                | 0   => exact fun (h : 1 = chain.extend_chain f₂.hom c N.succ) => hstrict N (Nat.le_refl N) (by
                  exact h ▸ Ideal.unit_ideal_in (h ▸ chain.extend_chain.descending f₂.hom hc₂ N))
                | n+1 => exact hstrict (N.succ + n) (Nat.le_trans (Nat.le_succ N) (Nat.le_add_right N.succ n))
              exact absurd this (hγ.left c' ⟨rfl, hdesc'⟩) },
            let ⟨cα, ⟨Nα, hltNα, hNαle⟩, ⟨hbaseα, hdescα⟩, hmaxα⟩ := hα.right
            let ⟨cγ, ⟨Nγ, hltNγ, hNγle⟩, ⟨hbaseγ, hdescγ⟩, hmaxγ⟩ := hγ.right
            have hγ0 := finite_chain_ends_zero Nγ hltNγ hNγle hbaseγ hdescγ hmaxγ
            let c' : chain β := fun n =>
              if n ≤ Nγ then chain.contract_chain f₂.preserve_mul_right cγ n
              else chain.extend_chain f₁.hom cα (n - Nγ)
            have hc'γ : ∀ {n}, n ≤ Nγ → c' n = chain.contract_chain f₂.preserve_mul_right cγ n :=
              fun h => by simp only [h, ite_true]
            have hc'α : ∀ {n}, ¬n ≤ Nγ → c' n = chain.extend_chain f₁.hom cα (n - Nγ) :=
              fun h => by simp only [h, ite_false]
            have hc'lt : ∀ n, n < Nα + Nγ → c' n ≠ c' n.succ := fun n hn =>
              (Nat.lt_trichotomy n Nγ).elim (fun hn => hc'γ (Nat.le_of_lt hn) ▸ hc'γ hn ▸ fun h =>
                hltNγ n hn (contraction_injective_of_surjective f₂.preserve_mul_right hf₂ h))
                (Or.elim · (fun hn' => by
                  rw [hc'γ (Nat.le_of_eq hn'), hc'α (Nat.not_le.mpr (hn' ▸ Nat.lt_succ_self n)),
                    hn', Nat.succ_sub (Nat.le_refl Nγ), Nat.sub_self]
                  have h₁ : chain.extend_chain f₁.hom cα 0 ⊆ chain.contract_chain f₂.preserve_mul_right cγ Nγ :=
                    fun x hx =>
                      have : f₂ x = 0 := (hexact ▸ Function.image'_sub_image _ _ (hf₁'' (cα 0) ▸
                        hx : x ∈ Function.image' f₁.hom (cα 0).subset) : x ∈ f₂.kernel.subset)
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
              { rw [hnα, Nat.zero_add] at hn ⊢
                exact (Nat.lt_or_eq_of_le hn).elim
                  (fun hnγ => by
                    rw [hc'α (Nat.not_le.mpr hnγ), hc'γ (Nat.le_refl Nγ)]
                    have h₁ : chain.extend_chain f₁ cα (n - Nγ) = extension f₁.hom 1 := by
                      have := hNαle (n - Nγ) (hnα ▸ Nat.zero_le _)
                      rw [hnα, hbaseα] at this
                      exact congrArg (extension f₁.hom) this
                    have h₂ : chain.contract_chain f₂.preserve_mul_right cγ Nγ = contraction f₂.preserve_mul_right 0 := by rw [←hγ0]; rfl
                    exact h₁ ▸ h₂ ▸ Ideal.ext'.mpr fun x => ⟨fun hx => (hexact ▸ Function.image'_sub_image _ _
                      ((Set.ext.mpr (hf₁'' 1) x).mp hx) : x ∈ f₂.kernel.subset),
                      fun hx => let ⟨y, hy⟩ : x ∈ f₁.image.subset := hexact ▸ hx; from_set.contains_mem ⟨y, trivial, hy⟩⟩)
                  (fun hnγ => by rw [hnγ]) }
              { rw [hc'α (Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.lt_add_pos_left Nγ hnα) hn)),
                  hc'α (Nat.not_le.mpr (Nat.lt_add_pos_left Nγ hnα)), Nat.add_sub_cancel]
                exact congrArg (extension f₁.hom) (hNαle (n - Nγ) ((Nat.le_sub_iff_right (Nat.le_trans
                  (Nat.le_add_left Nγ Nα) hn)).mpr hn)) }
            ⟨c', ⟨Nα + Nγ, hc'lt, hc'le⟩,
              ⟨have : contraction f₂.preserve_mul_right (cγ 0) = 1 := by rw [hbaseγ, contraction_unit]
                (hc'γ (Nat.zero_le Nγ) ▸ this : c' 0 = 1),
              fun n => (Nat.lt_trichotomy n Nγ).elim
                (fun hn => by
                  rw [hc'γ hn, hc'γ (Nat.le_of_lt hn)]
                  exact chain.contract_chain.descending f₂.preserve_mul_right hdescγ n)
                (Or.elim · (fun hn => by
                  rw [hn, hc'α (Nat.not_le.mpr (Nat.lt.base Nγ)), hc'γ (Nat.le_refl Nγ), Nat.succ_sub (Nat.le_refl Nγ),
                    Nat.sub_self]; exact fun x hx => (hγ0 ▸ (hexact ▸ Function.image'_sub_image _ _ ((Set.ext.mpr (hf₁''
                      (cα 1)) x).mp hx) : x ∈ f₂.kernel.subset) : f₂ x ∈ cγ Nγ))
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
      (h : ∀ I ∈ S, ∃ J ∈ S, I ⊊ J) : chain α
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
        let ⟨N, hN⟩ := NoetherianRing.noetherian (no_maximal_seq hS h) (no_maximal_seq_subset hS h)
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
          exact ⟨Q', delocalise_ideal.prime hQ, Subset.trans (I.extension_contraction (natural_hom S).preserve_mul_right)
            (Ideal.contraction.subset (natural_hom S).preserve_mul_right hIQ), localise_ideal.prime_loc_deloc h.left hPS ▸
            Ideal.contraction.subset _ hQP₁, fun h' => hQP₂ (congrArg (localise_ideal S ·) h' ▸
            (delocalise_ideal.deloc_loc Q).symm)⟩

    theorem localisation_noetherian [NoetherianRing α] (S : MultiplicativeSet α) : Ring.is_noetherian (localisation S) := fun c hc =>
      let ⟨N, hN⟩ := NoetherianRing.noetherian (fun n => delocalise_ideal S (c n)) fun n => contraction.subset (natural_hom S).preserve_mul_right (hc n)
      ⟨N, fun n hn => delocalise_ideal.deloc_loc (c n) ▸ delocalise_ideal.deloc_loc (c N) ▸ congrArg _ (hN n hn)⟩

    instance localisation_NoetherianRing [NoetherianRing α] (S : MultiplicativeSet α) : NoetherianRing (localisation S) where
      noetherian := localisation_noetherian S

    theorem surjective_noetherian [NoetherianRing α] [Ring β] {f : α →ᵣ β} (hf : Function.surjective f.hom) :
      Ring.is_noetherian β := fun c hc => chain.contract_chain.is_stable_of_surjective f.preserve_mul_right hf
        (NoetherianRing.noetherian (chain.contract_chain f.preserve_mul_right c)
        (chain.contract_chain.ascending f.preserve_mul_right hc))

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
    open Classical QuotientRing Monoid NCSemiring Semiring

    private noncomputable def no_minimal_seq [Ring α] {S : Set (Ideal α)} (hS : Nonempty S)
      (h : ∀ I ∈ S, ∃ J ∈ S, J ⊊ I) : chain α
    | 0   => (choice hS).val
    | n+1 => if hn : (no_minimal_seq hS h n) ∈ S then
        choose (h (no_minimal_seq hS h n) hn)
      else no_minimal_seq hS h n

    private theorem no_minimal_seq_in_S [Ring α] {S : Set (Ideal α)} (hS : Nonempty S)
      (h : ∀ I ∈ S, ∃ J ∈ S, J ⊊ I) (n : Nat) : no_minimal_seq hS h n ∈ S := by
    induction n with
    | zero      => exact (choice hS).property
    | succ n ih =>
      simp only [no_minimal_seq, ih, dite_true]
      exact (choose_spec (h (no_minimal_seq hS h n) ih)).left

    private theorem no_minimal_seq_def [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, J ⊊ I) (n : Nat) :
      no_minimal_seq hS h n.succ = choose (h (no_minimal_seq hS h n) (no_minimal_seq_in_S hS h n)) := by
        simp only [no_minimal_seq, no_minimal_seq_in_S hS h n]; rfl

    private theorem no_minimal_seq_subsetneq [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, J ⊊ I) :
      (n : Nat) → no_minimal_seq hS h n.succ ⊊ no_minimal_seq hS h n
    | 0 => no_minimal_seq_def hS h 0 ▸ (choose_spec (h (no_minimal_seq hS h 0)
      (no_minimal_seq_in_S hS h 0))).right
    | n+1 => no_minimal_seq_def hS h n.succ ▸ (choose_spec (h (no_minimal_seq hS h n.succ)
      (no_minimal_seq_in_S hS h n.succ))).right

    private theorem no_minimal_seq_subset [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, J ⊊ I) (n : Nat) :
      no_minimal_seq hS h n.succ ⊆ no_minimal_seq hS h n :=
        (no_minimal_seq_subsetneq hS h n).left

    private theorem no_minimal_seq_neq [Ring α] {S : Set (Ideal α)} (hS : Nonempty S) (h : ∀ I ∈ S, ∃ J ∈ S, J ⊊ I) (n : Nat) :
      no_minimal_seq hS h n ≠ no_minimal_seq hS h n.succ :=
        (Ideal.subsetneq.mp (no_minimal_seq_subsetneq hS h n)).right.symm

    theorem exists_minimal [Ring α] (hart : Ring.is_artinian α) {S : Set (Ideal α)} (hS : Nonempty S) : ∃ I ∈ S, ∀ J ∈ S, J ⊆ I → J = I :=
      byContradiction fun h => by
        simp only [not_exists, not_and, not_forall] at h
        have h : ∀ I ∈ S, ∃ J ∈ S, J ⊊ I := fun I hI =>
          let ⟨J, hJ₁, hJ₂, hJ₃⟩ := h I hI
          ⟨J, hJ₁, Ideal.subsetneq.mpr ⟨hJ₂, hJ₃⟩⟩
        let ⟨N, hN⟩ := hart (no_minimal_seq hS h) (no_minimal_seq_subset hS h)
        exact absurd (hN N.succ N.le_succ) (no_minimal_seq_neq hS h N).symm

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
            have hf₁ := ideal_quotient_map.preserve_mul_right I a
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
            have hexact : f₁.image.subset = f₂.kernel.subset := by
              rw [sub_quotient_hom.kernel hsub, ideal_quotient_map.image I a, natural_hom.extension_add_I, extension_principal]
            absurd (Ring.length_finite_of_ses hf₁ hf₁' hf₁'' hf₂ hexact hfin₁ hfin₂)
              (mt Ring.length_finite_iff_not_infinite.mp (iff_not_not.mpr hIinf))⟩
        absurd hIinf (Ring.length_finite_iff_not_infinite.mp (Ring.field_length_finite (maximal_is_Field (hprime hI)))))

    open Ring

    theorem nilradical_nilpotent [Ring α] (hart : is_artinian α) : ∃ n : Nat, n ≠ 0 ∧ nil_radical α ^ n = 0 := by
      let ⟨n, hn⟩ := hart (nil_radical α ^ ·) (product.pow_succ_subset _)
      byCases hn' : n = 0
      { exact ⟨1, Nat.one_ne_zero, eq_zero_ideal_of_trivial (mt Ring.nil_radical_proper (iff_not_not.mpr
        (pow_nat_0 (nil_radical α) ▸ hn' ▸ hn 1 (hn' ▸ Nat.le_of_lt Nat.zero_lt_one)))) _⟩ }
      { exact ⟨n, hn', byContradiction fun h => by
          let ⟨J, hJ, hJmin⟩ := @exists_minimal α _ hart {I : Ideal α | I * nil_radical α ^ n ≠ 0} ⟨nil_radical α,
            by rw [Semiring.mul_comm, ←pow_nat_succ]; exact fun h' => h (h' ▸ (hn n.succ n.le_succ).symm)⟩
          let ⟨a, haJ, ha⟩ : ∃ a ∈ J, principal a * nil_radical α ^ n ≠ 0 := byContradiction fun h =>
            hJ (in_zero_ideal (from_set.ideal_contained fun x ⟨i, hi, j, hj, hij⟩ => of_not_not (not_and.mp
              (not_exists.mp h i) hi) ▸ from_set.contains_mem ⟨i, generator_in_principal i, j, hj, hij⟩))
          have haJ' := hJmin (principal a) ha (principal_in haJ)
          have := hJmin (principal a * nil_radical α ^ n) (by
            have : nil_radical α ^ (n + n) = nil_radical α ^ n := hn (n + n) (n.le_add_left n)
            rw [mul_assoc, ←pow_nat_add_distrib, this]; exact ha : principal a * nil_radical α ^ n * nil_radical α ^ n ≠ 0)
            (haJ' ▸ product.subset_left)
          let ⟨b, hb, hab⟩ := ((Set.ext.mpr (product.principal_mul a (nil_radical α ^ n))) a).mp (this ▸ haJ)
          let ⟨m, hm, hbm⟩ := product.pow_subset (nil_radical α) n hn' hb
          have : ∀ m : Nat, a = a * b ^ m := fun m => by
            induction m with
            | zero      => exact (mul_one a).symm
            | succ m ih => rw [pow_nat_succ, Semiring.mul_comm _ b, ←mul_assoc, ←hab]; exact ih
          apply ha
          rw [this m, hbm, mul_zero, zero_principal, zero_mul]⟩ }
  end ArtinianRing
end M4R
