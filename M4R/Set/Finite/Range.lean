import M4R.Set.Finite.Finset

namespace List
  open M4R

  def range' : Nat → Nat → List Nat
  | s, 0     => []
  | s, (n+1) => s::range' (s+1) n

  @[simp] theorem range_zero : range 0 = [] := rfl

  @[simp] theorem range'_empty (n : Nat) : range' n 0 = [] := rfl
  @[simp] theorem range'_singleton (n : Nat) : range' n 1 = [n] := rfl

  theorem range_core_range' : ∀ s n : Nat, rangeAux s (range' s n) = range' 0 (n + s)
  | 0    , n => rfl
  | (s+1), n => by
    have : n+(s+1) = n+1+s := Nat.add_right_comm n s 1
    rw [this]
    exact range_core_range' s (n+1)

  theorem range_eq_range' (n : Nat) : range n = range' 0 n :=
    (range_core_range' n 0).trans (by rw [Nat.zero_add])

  theorem range'_start (s n : Nat) : range' s n.succ = [s] ++ range' s.succ n := rfl

  theorem range_start (n : Nat) : range n.succ = [0] ++ range' 1 n := by
    rw [range_eq_range', range'_start]

  @[simp] theorem range'_append : ∀ s m n : Nat, range' s m ++ range' (s+m) n = range' s (n+m)
  | s, 0  , n => rfl
  | s, m+1, n => by
    have : s :: (range' (s+1) m ++ range' (s+m+1) n) = s :: range' (s+1) (n+m) := by
      rw [Nat.add_right_comm, range'_append]
    exact this

  theorem range'_succ (s n : Nat) : range' s n.succ = range' s n ++ [s+n] := by
    rw [Nat.succ_eq_add_one, Nat.add_comm n 1]; exact (range'_append s n 1).symm

  theorem range_succ (n : Nat) : range n.succ = range n ++ [n] := by
    have := range'_succ 0 n; rw [←range_eq_range', ←range_eq_range', Nat.zero_add] at this
    exact this

  theorem range_add (a : Nat) : ∀ b, range (a + b) = range a ++ (range b).map (a + ·)
  | 0     => by rw [Nat.add_zero, range_zero, map_nil, append_nil]
  | b + 1 => by rw [Nat.add_succ, range_succ, range_add a b, range_succ, map_append, map_singleton, append_assoc]

  @[simp] theorem mem_range' : ∀ {m s n : Nat}, m ∈ range' s n ↔ s ≤ m ∧ m < s + n
  | m, s, Nat.zero => by
    rw [range'_empty, mem_nil_iff, false_iff, not_and_iff_or_not,
      Nat.add_zero, Nat.not_le, Nat.not_lt]; exact (Nat.le_or_lt s m).comm
  | m, s, Nat.succ n => by
    have : m = s → m < s + n + 1 := (· ▸ Nat.lt_succ_of_le (Nat.le_add_right _ _))
    have l : m = s ∨ s + 1 ≤ m ↔ s ≤ m := by
      conv => rhs rw [Nat.le_iff_eq_or_lt, Eq.comm]; exact Iff.rfl
    simp only [range', mem_cons_iff, mem_range', or_and_distrib_left,
      or_iff_right_of_imp this, l, Nat.add_right_comm]
    exact Iff.rfl

  @[simp] theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := by
    simp only [range_eq_range', mem_range', Nat.zero_le, true_and, Nat.zero_add]; exact Iff.rfl

  inductive chain (R : α → α → Prop) : α → List α → Prop
  | nil {a : α} : chain R a []
  | cons : ∀ {a b : α} {l : List α}, R a b → chain R b l → chain R a (b::l)

  variable {R : α → α → Prop}

  @[simp] theorem chain_cons {a b : α} {l : List α} : chain R a (b::l) ↔ R a b ∧ chain R b l :=
    ⟨fun p => by cases p with | cons n p => exact ⟨n, p⟩, fun ⟨n, p⟩ => p.cons n⟩

  theorem chain.imp' {S : α → α → Prop} (HRS : ∀ ⦃a b⦄, R a b → S a b)
    {a b : α} (Hab : ∀ ⦃c⦄, R a c → S b c)
    {l : List α} (p : chain R a l) : chain S b l := by
      induction p generalizing b with
      | nil => constructor
      | cons r c ih => exact chain.cons (Hab r) (ih (@HRS _))

  theorem chain.imp {S : α → α → Prop} (H : ∀ a b, R a b → S a b)
    {a : α} {l : List α} (p : chain R a l) : chain S a l :=
      p.imp' H (H a)

  theorem chain_of_pairwise {a : α} {l : List α} (p : Pairwise R (a::l)) : chain R a l := by
    let ⟨r, p'⟩ := Pairwise.consIff.mp p
    induction p' generalizing a with
    | nil => constructor
    | cons r' p ih =>
      simp only [chain_cons, forall_mem_cons] at r
      exact chain_cons.mpr ⟨r.left, ih (Pairwise.consIff.mp p).right r'⟩

  theorem chain_iff_pairwise (tr : ∀ ⦃x y z⦄, R x y → R y z → R x z) {a : α} {l : List α} :
    chain R a l ↔ Pairwise R (a::l) :=
      ⟨fun c => by
        induction c with
        | nil => exact Pairwise.singleton _ _
        | cons r p ih =>
          exact Pairwise.cons (fun x hx => Or.elim (eq_or_mem_of_mem_cons hx)
            (fun h => by rw [h]; exact r) (fun h => tr r ((Pairwise.consIff.mp ih).left x h))) ih,
      chain_of_pairwise⟩

  theorem chain_succ_range' : ∀ s n : Nat, chain (fun a b => b = Nat.succ a) s (range' (s+1) n)
  | s, 0     => chain.nil
  | s, (n+1) => (chain_succ_range' (s+1) n).cons rfl

  theorem chain_lt_range' (s n : Nat) : chain (fun a b => a < b) s (range' (s+1) n) :=
    (chain_succ_range' s n).imp (fun a b e => e.symm ▸ Nat.lt_succ_self _)

  theorem pairwise_lt_range' : ∀ s n : Nat, Pairwise (fun a b => a < b) (range' s n)
  | s, 0     => Pairwise.nil
  | s, (n+1) => (chain_iff_pairwise (by exact fun a b c => Nat.lt_trans)).mp (chain_lt_range' s n)

  theorem nodup_range' (s n : Nat) : nodup (range' s n) :=
    (pairwise_lt_range' s n).imp fun _ _ => Nat.ne_of_lt

  theorem nodup_range (n : Nat) : nodup (range n) := by
    simp only [range_eq_range', nodup_range']

  def antidiagonal (n : Nat) : List (Nat × Nat) :=
    (range (n+1)).map (fun i => (i, n - i))

  theorem nodup_antidiagonal (n : Nat) : nodup (antidiagonal n) :=
    nodup_map_on (fun _ _ _ _ hxy => by simp only [congrArg Prod.fst hxy]) (nodup_range (n+1))

end List

namespace M4R

  /-
      range n => [0, ..., n-1]
      e.g. : range 0 => [], range 1 => [0], range 2 => [0, 1], range 3 => [0, 1, 2]

      range m, n => [m, m+1, ..., m+n-1]
      e.g. : range 2 0 => [], range 2 1 => [2], range 2 2 => [2, 3], range 2 3 => [2, 3, 4]
  -/

  namespace UnorderedList

    def range (n : Nat) : UnorderedList Nat := List.range n
    def range' (m n : Nat) : UnorderedList Nat := List.range' m n

    def antidiagonal (n : Nat) : UnorderedList (Nat × Nat) := List.antidiagonal n

    def toInt (l : UnorderedList Nat) : UnorderedList Int := l.map Int.ofNat

    theorem range_eq_range' (n : Nat) : range n = range' 0 n :=
      Quot.sound (by rw [List.range_eq_range' n]; exact Perm.refl _)

    namespace range'

      @[simp] theorem zero (n : Nat) : range' n 0 = 0 := rfl
      @[simp] theorem singleton (n : Nat) : range' n 1 = UnorderedList.singleton n := rfl

      theorem append (s m n : Nat) : range' s m + range' (s+m) n = range' s (n+m) :=
        congrArg List.to_UnorderedList (List.range'_append s m n)

      theorem start (s n : Nat) : range' s n.succ = UnorderedList.singleton s + range' s.succ n := rfl

      theorem succ (s n : Nat) : range' s n.succ = range' s n + UnorderedList.singleton (s+n) :=
        congrArg List.to_UnorderedList (List.range'_succ s n)

      @[simp] theorem mem_range' {m s n : Nat} : m ∈ range' s n ↔ s ≤ m ∧ m < s + n :=
        List.mem_range'

    end range'
    namespace range

      @[simp] theorem zero : range 0 = 0 := rfl

      theorem succ (n : Nat) : range n.succ = range n + UnorderedList.singleton n :=
        congrArg List.to_UnorderedList (List.range_succ n)

      theorem start (n : Nat) : range n.succ = UnorderedList.singleton 0 + range' 1 n :=
        congrArg List.to_UnorderedList (List.range_start n)

      theorem add (a b : Nat) : range (a + b) = range a + (range b).map (a + ·) :=
        congrArg List.to_UnorderedList (List.range_add a b)

      @[simp] theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n :=
        List.mem_range

    end range

  end UnorderedList
  namespace Finset

    def range (n : Nat) : Finset Nat := ⟨UnorderedList.range n, List.nodup_range n⟩
    def range' (m n : Nat) : Finset Nat := ⟨UnorderedList.range' m n, List.nodup_range' m n⟩

    theorem range_eq_range' (n : Nat) : range n = range' 0 n := by
      apply Finset.val_inj.mp
      exact UnorderedList.range_eq_range' n

    def antidiagonal (n : Nat) : Finset (Nat × Nat) := ⟨UnorderedList.antidiagonal n, List.nodup_antidiagonal n⟩

    @[simp] theorem antidiagonal.zero : antidiagonal 0 = Finset.singleton (0, 0) := rfl

    def toInt (f : Finset Nat) : Finset Int := f.map_inj (fun _ _ => congrArg Int.toNat : Function.injective Int.ofNat)

    namespace range'

      @[simp] theorem zero (n : Nat) : range' n 0 = ∅ := rfl
      @[simp] theorem singleton (n : Nat) : range' n 1 = Finset.singleton n := rfl

      @[simp] theorem mem_range' {m s n : Nat} : m ∈ range' s n ↔ s ≤ m ∧ m < s + n :=
        UnorderedList.range'.mem_range'

      theorem not_mem_front {s n} : s ∉ range' s.succ n := by
        rw [mem_range', not_and_iff_or_not, Nat.not_le, Nat.not_lt]
        exact Or.inl (Nat.lt_succ_self s)

      theorem not_mem_back {s n} : s+n ∉ range' s n := by
        rw [mem_range', not_and_iff_or_not, Nat.not_le, Nat.not_lt]
        exact Or.inr (Nat.le_refl _)

      theorem start (s n : Nat) : range' s n.succ = (range' s.succ n).cons s not_mem_front := rfl

      theorem succ (s n : Nat) : range' s n.succ = (range' s n).cons (s+n) not_mem_back :=
        Finset.ext fun _ => by
          rw [Finset.mem_cons, mem_range', mem_range', or_and_distrib_left,
            or_iff_right_of_imp (· ▸ Nat.le_add_right s n), Nat.add_succ,
            ←Nat.le_iff_eq_or_lt, Nat.lt_succ_if_le]; exact Iff.rfl

      theorem append (s m n : Nat) : range' s m ∪ range' (s + m) n = range' s (m + n) := by
        have := UnorderedList.range'.append s m n
        apply Finset.ext; intro k
        rw [Finset.mem_union, mem_range', mem_range', mem_range']
        exact ⟨fun h => h.elim
            (fun ⟨h₁, h₂⟩ => ⟨h₁, Nat.add_assoc _ _ _ ▸ Nat.lt_add_right _ _ _ h₂⟩)
            (fun ⟨h₁, h₂⟩ => ⟨Nat.le_trans (Nat.le_add_right s m) h₁, Nat.add_assoc _ _ _ ▸ h₂⟩),
          fun ⟨h₁, h₂⟩ => Or.elim (Nat.le_or_lt (s + m) k)
            (fun h => Or.inr ⟨h, Nat.add_assoc _ _ _ ▸ h₂⟩) (fun h => Or.inl ⟨h₁, h⟩)⟩

      theorem disjoint (s₁ n₁ s₂ n₂ : Nat) : disjoint (range' s₁ n₁) (range' s₂ n₂) ↔ s₁ + n₁ ≤ s₂ ∨ s₂ + n₂ ≤ s₁ ∨ n₁ = 0 ∨ n₂ = 0 := by
        simp only [Finset.disjoint]
        have : (range' s₁ n₁ ∩ range' s₂ n₂ = ∅) ↔ ∀ a, (a < s₁ ∨ s₁ + n₁ ≤ a) ∨ a < s₂ ∨ s₂ + n₂ ≤ a := by
          simp only [Finset.ext_iff, Finset.mem_empty, iff_false, Finset.mem_inter, not_and_iff_or_not,
            mem_range', not_and_iff_or_not, Nat.not_le, Nat.not_lt]; exact Iff.rfl
        rw [this]
        exact ⟨fun h => by
          have h₁ := h s₁
          have h₂ := h s₂
          simp only [Nat.lt_irrefl, false_or, Nat.add_le] at h₁ h₂
          exact Or.elim h₁ (fun h₁ => Or.inr (Or.inr (Or.inl h₁)))
            (Or.elim · (fun h₁ => Or.elim h₂
              (Or.elim · (absurd ⟨h₁, ·⟩ Nat.lt_not_symm) Or.inl)
              (fun h₂ => Or.inr (Or.inr (Or.inr h₂))))
              (fun h₁ => Or.inr (Or.inl h₁))),
          fun h a => by
            cases h with
            | inl h =>
              byCases h' : s₁ + n₁ ≤ a;
              { exact Or.inl (Or.inr h') }
              { exact Or.inr (Or.inl (Nat.lt_of_lt_of_le (Nat.not_le.mp h') h)) }
            | inr h =>
              cases h with
              | inl h =>
                byCases h' : s₂ + n₂ ≤ a;
                { exact Or.inr (Or.inr h') }
                { exact Or.inl (Or.inl (Nat.lt_of_lt_of_le (Nat.not_le.mp h') h)) }
              | inr h =>
                cases h with
                | inl h => rw [h, Nat.add_zero]; exact Or.inl (Nat.le_or_lt s₁ a).comm
                | inr h => rw [h, Nat.add_zero]; exact Or.inr (Nat.le_or_lt s₂ a).comm⟩

    end range'
    namespace range

      @[simp] theorem zero : range 0 = ∅ := rfl

      theorem not_mem_back {n} : n ∉ range n := by
        have := @range'.not_mem_back 0 n
        rw [Nat.zero_add, ←range_eq_range'] at this
        exact this

      theorem succ (n : Nat) : range n.succ = (range n).cons n not_mem_back :=
        Finset.ext fun x => by
          rw [range_eq_range', range'.succ, Finset.mem_cons, Finset.mem_cons,
            Nat.zero_add, range_eq_range']; exact Iff.rfl

      theorem start (n : Nat) : range n.succ = (range' 1 n).cons 0 range'.not_mem_front := by
        rw [range_eq_range', range'.start]

      @[simp] theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n :=
        UnorderedList.range.mem_range

      theorem append (m n : Nat) : range m ∪ range' m n = range (m + n) := by
        have := range'.append 0 m n
        simp only [Nat.zero_add, ←range_eq_range'] at this
        exact this

    end range
  end Finset
end M4R
