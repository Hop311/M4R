import M4R.Algebra.Ring.RMorphism

namespace M4R
  open NCSemiring
  open Semiring

  namespace Finset.map_sum

    theorem mul_sum [NCSemiring β] (b : β) (f : α → β) (s : Finset α) :
      b * (∑ f in s) = ∑ (b * f ·) in s := by
        let h := NCSemiring.MulHomLeft b
        have : b * (∑ f in s) = h (∑ f in s) := rfl
        rw [this, h.map_sum]; rfl
    
    theorem sum_mul [NCSemiring β] (b : β) (f : α → β) (s : Finset α) :
      (∑ f in s) * b = ∑ (f · * b) in s := by
        let h := NCSemiring.MulHomRight b
        have : (∑ f in s) * b = h (∑ f in s) := rfl
        rw [this, h.map_sum]; rfl

  end Finset.map_sum

  def UnorderedList.prod [Semiring α] (s : UnorderedList α) : α := 
    s.fold (· * ·) (fun a b c => by simp only [mul_assoc, mul_comm b]) 1
  def UnorderedList.map_prod [Semiring β] (s : UnorderedList α) (f : α → β) : β :=
    (s.map f).prod

  def Finset.prod [Semiring α] (s : Finset α) : α := s.elems.prod
  def Finset.map_prod [Semiring β] (s : Finset α) (f : α → β) : β := s.elems.map_prod f

  theorem binomial' [Semiring α] (a b : α) (n : Nat) : (a + b)^n =
    ∑ (fun x => Nat.choose n x.fst * a ^ x.fst * b ^ x.snd) in (Finset.antidiagonal n) := by
      induction n with
      | zero => simp only [Nat.zero_eq, NCSemiring.pow_nat_0, Finset.antidiagonal.zero,
        Finset.map_sum.singleton, NCSemiring.mul_one]; rfl
      | succ n ih =>
        rw [NCSemiring.pow_nat_succ, ih, Finset.map_sum.sum_mul]
        have : (fun (x : Nat × Nat) => Nat.choose n x.fst * a ^ x.fst * b ^ x.snd * (a + b)) =
          (fun (x : Nat × Nat) => Nat.choose n x.fst * a ^ x.fst.succ * b ^ x.snd +
            Nat.choose n x.fst * a ^ x.fst * b ^ x.snd.succ) := funext fun x => by
              rw [NCSemiring.mul_distrib_left, Semiring.mul_right_comm,
              NCSemiring.mul_assoc _ _ a, NCSemiring.mul_assoc _ _ b, pow_nat_succ, pow_nat_succ]
        rw [this]; simp only [Finset.map_sum.antidiagonal_eq_range]
        rw [Finset.map_sum.distrib, CommMonoid.add_comm, Finset.map_sum.range_start,
          Finset.map_sum.range_succ, ←Monoid.add_assoc, Monoid.add_assoc (_ * _)]
        have : (∑ k in Finset.range' 1 n, Nat.choose n k * a ^ k * b ^ (n - k).succ) +
          (∑ k in Finset.range n, Nat.choose n k * a ^ k.succ * b ^ (n - k)) =
            ∑ k in Finset.range' 1 n, Nat.choose n.succ k * a ^ k * b ^ (n.succ - k) := by
              rw [Finset.map_sum.range_shift, ←Finset.map_sum.distrib]
              exact Finset.map_sum.congr rfl (fun x hx => by
                simp only [Function.comp]
                have ⟨h₁, h₂⟩ := Finset.range'.mem_range'.mp hx
                have h₂ : x ≤ n := Nat.le_of_lt_succ (Nat.one_add n ▸ h₂)
                rw [Nat.succ_pred_eq_of_pos h₁, Nat.succ_sub h₂, Nat.sub_pred h₁ h₂,
                  ←NCSemiring.mul_distrib_right, ←NCSemiring.mul_distrib_right,
                  ←ofNat.preserve_add, Nat.choose_pred h₁])
        rw [this, Finset.map_sum.range_succ, Finset.map_sum.range_start, Nat.choose_zero_right_succ,
          Nat.sub_zero, Nat.sub_zero, Nat.choose_self_succ, Nat.sub_self, Nat.sub_self]

end M4R
