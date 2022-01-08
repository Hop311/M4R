import M4R.Set.Finite.Finset
import M4R.Numbers

namespace List
  open M4R

  def range' : Nat → Nat → List Nat
  | s, 0     => []
  | s, (n+1) => s::range' (s+1) n

  theorem range_core_range' : ∀ s n : Nat, rangeAux s (range' s n) = range' 0 (n + s)
  | 0    , n => rfl
  | (s+1), n => by
    have : n+(s+1) = n+1+s := Nat.add_right_comm n s 1
    rw [this]
    exact range_core_range' s (n+1)

  theorem range_eq_range' (n : Nat) : range n = range' 0 n :=
    (range_core_range' n 0).trans (by rw [Nat.zero_add])

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

  theorem forall_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
      ⟨fun h => ⟨h a (mem_cons_self a l), fun x xl => h x (mem_cons_of_mem a xl)⟩, fun ⟨h₁, h₂⟩ x hx => by
        cases hx with
        | inl h => rw [h]; exact h₁
        | inr h => exact h₂ x h⟩

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
  | s, (n+1) => (chain_iff_pairwise (by exact fun a b c => Nat.lt_trans)).1 (chain_lt_range' s n)

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

  namespace UnorderedList
    
    def range (n : Nat) : UnorderedList Nat := List.range n

    def antidiagonal (n : Nat) : UnorderedList (Nat × Nat) := List.antidiagonal n

    def toInt (l : UnorderedList Nat) : UnorderedList Int := l.map Int.ofNat

  end UnorderedList
  namespace Finset

    def range (n : Nat) : Finset Nat := ⟨UnorderedList.range n, List.nodup_range n⟩
  
    def antidiagonal (n : Nat) : Finset (Nat × Nat) := ⟨UnorderedList.antidiagonal n, List.nodup_antidiagonal n⟩

    def toInt (f : Finset Nat) : Finset Int := f.map_inj (congrArg Int.toNat : Function.injective Int.ofNat)

  end Finset
end M4R
