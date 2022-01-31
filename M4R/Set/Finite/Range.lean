import M4R.Set.Finite.Finset
import M4R.Numbers

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
          exact Pairwise.cons (fun x hx => Or.elim (List.eq_or_mem_of_mem_cons hx)
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
      @[simp] theorem singleton (n : Nat) : range' n 1 = [n] := rfl

      theorem cons (m n : Nat) : range' m (n+1) = (range' (m+1) n).cons m := rfl

      theorem append : ∀ s m n : Nat, range' s m + range' (s+m) n = range' s (n+m)
      | s, 0  , n => rfl
      | s, m+1, n => by
        have : (range' (s+1) m + range' (s+m+1) n).cons s = (range' (s+1) (n+m)).cons s := by
          rw [Nat.add_right_comm, append]
        exact this

      theorem succ (s n : Nat) : range' s n.succ = range' s n + [s+n] := by
        rw [Nat.succ_eq_add_one, Nat.add_comm n 1]; exact (append s n 1).symm

    end range'
    namespace range
      @[simp] theorem zero : range 0 = 0 := rfl

      theorem cons (n : Nat) : range (n+1) = (range' 1 n).cons 0 := by
        rw [range_eq_range', range'.cons]

      theorem succ (n : Nat) : range n.succ = range n + [n] := by
        have := range'.succ 0 n; rw [←range_eq_range', ←range_eq_range', Nat.zero_add] at this
        exact this

      theorem add (a : Nat) : ∀ b, range (a + b) = range a + (range b).map (a + ·)
      | 0     => by rw [Nat.add_zero, zero, map_nil, append.add_zero]
      | b + 1 => by
        rw [Nat.add_succ, succ, add a b, succ, map.add, singleton_eq, singleton_eq, map.singleton, append.assoc]

    end range

  end UnorderedList
  namespace Finset

    def range (n : Nat) : Finset Nat := ⟨UnorderedList.range n, List.nodup_range n⟩
    def range' (m n : Nat) : Finset Nat := ⟨UnorderedList.range' m n, List.nodup_range' m n⟩

    theorem range_eq_range' (n : Nat) : range n = range' 0 n := by
      apply Finset.val_inj.mp
      exact UnorderedList.range_eq_range' n

    def antidiagonal (n : Nat) : Finset (Nat × Nat) := ⟨UnorderedList.antidiagonal n, List.nodup_antidiagonal n⟩

    def toInt (f : Finset Nat) : Finset Int := f.map_inj (congrArg Int.toNat : Function.injective Int.ofNat)

  end Finset
end M4R
