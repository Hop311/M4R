import M4R.Algebra.Ring.Defs

namespace M4R

  namespace NCSemiring

    protected instance Product (α₁ : Type _) (α₂ : Type _) [NCSemiring α₁] [NCSemiring α₂] : NCSemiring (α₁ × α₂) where
      one               := (1, 1)
      mul               := fun (a₁, a₂) (b₁, b₂) => (a₁ * b₁, a₂ * b₂)
      mul_one           := fun (a₁, a₂) => by simp [HMul.hMul, Mul.mul]; exact ⟨mul_one a₁, mul_one a₂⟩
      one_mul           := fun (a₁, a₂) => by simp [HMul.hMul, Mul.mul]; exact ⟨one_mul a₁, one_mul a₂⟩
      mul_assoc         := fun (a₁, a₂) (b₁, b₂) (c₁, c₂) => by
        simp [HMul.hMul, Mul.mul];exact ⟨mul_assoc a₁ b₁ c₁, mul_assoc a₂ b₂ c₂⟩
      mul_distrib_left  := fun (a₁, a₂) (b₁, b₂) (c₁, c₂) => by
        simp [HMul.hMul, Mul.mul, HAdd.hAdd, Add.add]; exact ⟨mul_distrib_left a₁ b₁ c₁, mul_distrib_left a₂ b₂ c₂⟩
      mul_distrib_right := fun (a₁, a₂) (b₁, b₂) (c₁, c₂) => by
        simp [HMul.hMul, Mul.mul, HAdd.hAdd, Add.add]; exact ⟨mul_distrib_right a₁ b₁ c₁, mul_distrib_right a₂ b₂ c₂⟩
      mul_zero          := fun (a₁, a₂) => by
        simp [HMul.hMul, Mul.mul, Monoid.product_zero]; exact ⟨mul_zero a₁, mul_zero a₂⟩
      zero_mul          := fun (a₁, a₂) => by
        simp [HMul.hMul, Mul.mul, Monoid.product_zero]; exact ⟨zero_mul a₁, zero_mul a₂⟩

    protected instance multi_product.One {ι : Type _} (fι : ι → Type _) [∀ i, One (fι i)] : One (MultiProd fι) where
      one := fun _ => 1
    protected theorem multi_product.One_def {ι : Type _} {fι : ι → Type _} [∀ i, One (fι i)] : ∀ i, (1 : MultiProd fι) i = 1 :=
      fun _ => rfl
    
    protected instance multi_product.Mul {ι : Type _} (fι : ι → Type _) [∀ i, Mul (fι i)] : Mul (MultiProd fι) where
      mul := fun a b i => a i * b i
    protected theorem multi_product.Mul_def {ι : Type _} {fι : ι → Type _} [∀ i, Mul (fι i)] (a b : MultiProd fι) :
      ∀ i, (a * b) i = a i * b i := fun _ => rfl

    protected instance multi_product {ι : Type _} (fι : ι → Type _) [∀ i, NCSemiring (fι i)] : NCSemiring (MultiProd fι) where
      mul_one           := fun a => funext fun i => NCSemiring.mul_one (a i)
      one_mul           := fun a => funext fun i => NCSemiring.one_mul (a i)
      mul_assoc         := fun a b c => funext fun i => NCSemiring.mul_assoc (a i) (b i) (c i)
      mul_distrib_left  := fun a b c => funext fun i => NCSemiring.mul_distrib_left (a i) (b i) (c i)
      mul_distrib_right := fun a b c => funext fun i => NCSemiring.mul_distrib_right (a i) (b i) (c i)
      mul_zero          := fun a => funext fun i => NCSemiring.mul_zero (a i)
      zero_mul          := fun a => funext fun i => NCSemiring.zero_mul (a i)

    theorem ofNat.preserve_succ [NCSemiring α] (n : Nat) : n.succ = (n : α) + 1 := by
      induction n with
      | zero => simp only [NCSemiring.ofNat, Monoid.zero_add]
      | succ k ih => simp only [NCSemiring.ofNat]

    theorem ofNat.preserve_add [NCSemiring α] (m n : Nat) : m + n = (m : α) + n := by
      induction n with
      | zero => simp only [NCSemiring.ofNat, Monoid.add_zero]; rfl
      | succ k ih => rw [Nat.add_succ, preserve_succ, preserve_succ, ih, Monoid.add_assoc]

    theorem mul_nat_succ [NCSemiring α] (a : α) (n : Nat) : n.succ * a = n * a + a := by
      rw [ofNat.preserve_succ, mul_distrib_right, one_mul]

    theorem pow_nat_succ [NCSemiring α] (a : α) (x : Nat) : a ^ (Nat.succ x) = a^x * a :=
      match x with
      | Nat.zero => by simp only [HPow.hPow, Pow.pow, NCSemiring.pow_nat, one_mul]
      | Nat.succ k  => rfl

    theorem pow_nat_one [NCSemiring α] (n : Nat) : (1 : α)^n = 1 := by
      induction n with
      | zero      => rfl
      | succ k ih => rw [pow_nat_succ, ih, one_mul];
    theorem pow_nat_0 [NCSemiring α] (a : α) : a ^ (0 : Nat) = 1 := rfl
    theorem pow_nat_1 [NCSemiring α] (a : α) : a ^ (1 : Nat) = a := rfl

    theorem pow_nat_add_distrib [NCSemiring α] (a : α) (m n : Nat) : a^(m + n) = a^m * a^n := by
      induction n with
      | zero      => rw [Nat.add_zero, pow_nat_0, mul_one]
      | succ k ih => rw [Nat.add_succ, pow_nat_succ, pow_nat_succ, ←mul_assoc, ih]

    protected class constructor_ncsr (α : Type _) extends CommMonoid.constructor_cm α, One α, Mul α where
      mul_one           : ∀ a : α, a * 1 = a
      one_mul           : ∀ a : α, 1 * a = a
      mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
      mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
      mul_distrib_right : ∀ a b c : α, (a + b) * c = a * c + b * c
      mul_zero          : ∀ a : α, a * 0 = 0
      zero_mul          : ∀ a : α, 0 * a = 0

    protected instance construct {α : Type _} (c : NCSemiring.constructor_ncsr α) : NCSemiring α where
      toCommMonoid := CommMonoid.construct c.toconstructor_cm
      mul_one           := c.mul_one
      one_mul           := c.one_mul
      mul_assoc         := c.mul_assoc
      mul_distrib_left  := c.mul_distrib_left
      mul_distrib_right := c.mul_distrib_right
      mul_zero          := c.mul_zero
      zero_mul          := c.zero_mul

    protected def to_constructor (α : Type _) [NCSemiring α] : NCSemiring.constructor_ncsr α where
      toconstructor_cm := CommMonoid.to_constructor α
      mul_one           := NCSemiring.mul_one
      one_mul           := NCSemiring.one_mul
      mul_assoc         := NCSemiring.mul_assoc
      mul_distrib_left  := NCSemiring.mul_distrib_left
      mul_distrib_right := NCSemiring.mul_distrib_right
      mul_zero          := NCSemiring.mul_zero
      zero_mul          := NCSemiring.zero_mul

  end NCSemiring

  namespace Semiring
    open NCSemiring

    protected instance Product (α₁ : Type _) (α₂ : Type _) [Semiring α₁] [Semiring α₂] : Semiring (α₁ × α₂) where
      mul_comm := fun (a₁, a₂) (b₁, b₂) => by simp [HMul.hMul, Mul.mul]; exact ⟨mul_comm a₁ b₁, mul_comm a₂ b₂⟩

    protected instance multi_product {ι : Type _} (fι : ι → Type _) [∀ i, Semiring (fι i)] : Semiring (MultiProd fι) where
      mul_comm := fun a b => funext fun i => Semiring.mul_comm (a i) (b i)

    theorem mul_right_comm [Semiring α] (a b c : α) : a * b * c = a * c * b := by
      rw [mul_assoc, mul_comm b, ←mul_assoc]
    theorem mul_left_comm [Semiring α] (a b c : α) : a * (b * c) = b * (a * c) := by
      rw [←mul_assoc, mul_comm a, mul_assoc]

    theorem divides_self [Semiring α] (a : α) : a ÷ a := ⟨1, mul_one a⟩
    theorem divides_zero [Semiring α] (a : α) : a ÷ 0 := ⟨0, mul_zero a⟩
    theorem divides_add [Semiring α] {a b c : α} : a ÷ b → a ÷ c → a ÷ (b + c)
    | ⟨x, axb⟩, ⟨y, ayc⟩ => ⟨x + y, by rw [mul_distrib_left, axb, ayc]⟩
    theorem divides_mul [Semiring α] {a b : α} (c : α) : a ÷ b → a ÷ (b * c)
    | ⟨x, axb⟩ => ⟨x * c, by rw [←mul_assoc, axb]⟩
    theorem divides_mul' [Semiring α] {a c : α} (b : α) : a ÷ c → a ÷ (b * c) := by
      rw [mul_comm]; exact divides_mul b

    theorem isUnit_1 [Semiring α] : isUnit (1 : α) := ⟨1, by simp [one_mul]⟩
    theorem notUnit_0 [Semiring α] : (0 : α) ≠ (1 : α) → ¬isUnit (0 : α) := by
      intro h₁ ⟨_, h₂⟩; rw [zero_mul] at h₂; exact h₁ h₂
    theorem unit_mul [Semiring α] {a b : α} : isUnit a → isUnit b → isUnit (a * b)
    | ⟨x, xs⟩, ⟨y, ys⟩ => by
      apply Exists.intro (y * x); rw [mul_assoc, ←mul_assoc b, ys, one_mul, xs];
    theorem divides_unit [Semiring α] {a b : α} : isUnit b → a ÷ b → isUnit a := by
      intro ub ab;
      let ⟨binv, bbinv⟩ := Classical.indefiniteDescription _ ub;
      let ⟨c, ac⟩ := Classical.indefiniteDescription _ ab;
      exact ⟨c * binv, by rw [←mul_assoc, ac, bbinv];⟩
    theorem unit_divides [Semiring α] : ∀ a b : α, isUnit a → a ÷ b := by
      intro a b ⟨c, ac⟩; exact ⟨c * b, by rw [←mul_assoc, ac, one_mul];⟩

    def unit_set (α : Type _) [Semiring α] : Set α := {x | isUnit x}

    noncomputable def unit_inv [Semiring α] {a : α} (h : isUnit a) : α :=
      Classical.choose h
    theorem mul_unit_inv [Semiring α] {a : α} (h : isUnit a) : a * unit_inv h = 1 :=
      Classical.choose_spec h
    theorem unit_inv_mul [Semiring α] {a : α} (h : isUnit a) : unit_inv h * a = 1 := by
      rw [mul_comm]; exact mul_unit_inv h

    noncomputable instance UnitGroup [Semiring α] : Group ↑(unit_set α) := Group.construct
    {  
      zero := ⟨1, ⟨1, by rw [mul_one]⟩⟩
      add := fun a b => ⟨a.val * b.val, unit_mul a.property b.property⟩
      neg := fun ⟨x, xs⟩ => ⟨unit_inv xs, x, unit_inv_mul xs⟩
      add_zero := fun ⟨a, _⟩ => Set.elementExt (mul_one a)
      add_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_assoc a b c)
      add_neg := fun ⟨a, as⟩ => Set.elementExt (mul_unit_inv as)
    }

    theorem pow_nat_mul_distrib [Semiring α] (a b : α) (m : Nat) : (a * b)^m = a^m * b^m := by
      induction m with
      | zero      => simp only [Nat.zero_eq, pow_nat_0, mul_one]
      | succ k ih => simp only [pow_nat_succ, ←mul_assoc, ih, mul_comm]

    theorem pow_nat_comp [Semiring α] (a : α) (m n : Nat) : (a^m)^n = a^(m*n) := by 
      induction m with
      | zero => rw [Nat.zero_mul, pow_nat_0, pow_nat_one]
      | succ k ih => rw [pow_nat_succ, Nat.succ_mul, pow_nat_mul_distrib, ih, pow_nat_add_distrib]

    protected class constructor_sr (α : Type _) extends CommMonoid.constructor_cm α, One α, Mul α where
      mul_one           : ∀ a : α, a * 1 = a
      mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
      mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
      mul_zero          : ∀ a : α, a * 0 = 0
      mul_comm          : ∀ a b : α, a * b = b * a

    protected instance construct {α : Type _} (c : Semiring.constructor_sr α) : Semiring α where
      toCommMonoid      := CommMonoid.construct c.toconstructor_cm
      mul_one           := c.mul_one
      one_mul           := fun a => by rw [c.mul_comm]; exact c.mul_one a
      mul_assoc         := c.mul_assoc
      mul_distrib_left  := c.mul_distrib_left
      mul_distrib_right := fun a b _ => by rw [c.mul_comm, c.mul_comm a, c.mul_comm b]; exact c.mul_distrib_left _ _ _
      mul_zero          := c.mul_zero
      zero_mul          := fun a => by rw [c.mul_comm]; exact c.mul_zero a
      mul_comm          := c.mul_comm

    protected def to_constructor (α : Type _) [Semiring α] : Semiring.constructor_sr α where
      toconstructor_cm  := CommMonoid.to_constructor α
      mul_one           := mul_one
      mul_assoc         := mul_assoc
      mul_distrib_left  := mul_distrib_left
      mul_zero          := mul_zero
      mul_comm          := mul_comm

  end Semiring

  instance NatSemiring : Semiring Nat := Semiring.construct
    {
      add_zero          := Nat.add_zero
      add_assoc         := Nat.add_assoc
      add_comm          := Nat.add_comm
      mul_one           := Nat.mul_one
      mul_assoc         := Nat.mul_assoc
      mul_distrib_left  := Nat.left_distrib
      mul_zero          := Nat.mul_zero
      mul_comm          := Nat.mul_comm
    }

end M4R
