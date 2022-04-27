import M4R.Algebra.Ring.MapRings

namespace M4R

  def Polynomial (α : Type _) [Semiring α] := Nat →₀ α

  def PowerSeries (α : Type _) [Semiring α] := Nat → α

  def MVPolynomial (σ : Type _) (α : Type _) [Semiring α] := (σ →₀ Nat) →₀ α

  def MVPowerSeries (σ : Type _) (α : Type _) [Semiring α] := (σ →₀ Nat) → α

  noncomputable instance PolynomialSemiring (α : Type _) [Semiring α] : Semiring (Polynomial α) :=
    Finsupp.toSemiring
  noncomputable instance MVPolynomialSemiring (σ : Type _) (α : Type _) [Semiring α] : Semiring (MVPolynomial σ α) :=
    Finsupp.toSemiring

  noncomputable instance PolynomialCoe (α : Type _) [Semiring α] : Coe (Polynomial α) (MVPolynomial Unit α) where
    coe := fun f => by
      simp only [Polynomial, MVPolynomial] at f ⊢
      exact {
        support := Finset.map_inj Finsupp.UnitFinsuppMonoid.right_inv.inv_injective f.support
        to_fun := fun x => f (x Unit.unit)
        mem_support_to_fun := fun x =>
          ⟨fun h => by
            let ⟨n, hnf, hnx⟩ := Finset.map_inj_mem.mp h
            rw [←hnx]; simp only [Finsupp.UnitFinsuppMonoid]
            rw [←Finsupp.mem_support_to_fun, Finsupp.single.eq_same]
            exact hnf,
          fun h => by
            rw [Finset.map_inj_mem]
            exact ⟨x Unit.unit, (Finsupp.mem_support_to_fun f _).mpr h, Finsupp.UnitFinsuppMonoid.left_inv x⟩⟩
      }

  instance PowerSeriesCoe (α : Type _) [Semiring α] : Coe (PowerSeries α) (MVPowerSeries Unit α) where
    coe := fun x y => x (y.to_fun Unit.unit)

  noncomputable def monomial [Semiring α] (s : σ →₀ Nat) : α →₊ MVPolynomial σ α := Finsupp.single_add_hom s

  theorem single_eq_monomial [Semiring α] (s : σ →₀ Nat) (a : α) : Finsupp.single s a = monomial s a := rfl

  theorem mul_def [Semiring α] {p q : MVPolynomial σ α} :
    (p * q) = ∑ fun m a => ∑ fun n b => monomial (m + n) (a * b) in q in p := rfl

  noncomputable def C [Semiring α] : α →*₁ MVPolynomial σ α where
    toMHomomorphism := monomial 0
    preserve_one  := rfl
    preserve_mul  := fun a b => by simp only [←single_eq_monomial, mul_def, Finsupp.map_sum.single,
      Monoid.add_zero, NCSemiring.mul_zero, NCSemiring.zero_mul, Finsupp.single.zero]

  noncomputable def X [Semiring α] (n : σ) : MVPolynomial σ α := monomial (Finsupp.single n 1) 1

  theorem C_apply [Semiring α] : (C a : MVPolynomial σ α) = monomial 0 a := rfl

  @[simp] theorem C_0 [Semiring α] : C 0 = (0 : MVPolynomial σ α) := by
    simp only [C_apply, monomial, Finsupp.single_add_hom, Finsupp.single.zero]

  @[simp] theorem C_1 [Semiring α] : C 1 = (1 : MVPolynomial σ α) := rfl

  theorem C_mul_monomial [Semiring α] {a a' : α} {s : σ →₀ Nat} : C a * monomial s a' = monomial s (a * a') := by
    simp only [C_apply, monomial, Finsupp.single_add_hom]
    rw [Finsupp.single_mul_single, Monoid.zero_add]

  @[simp] theorem C_add [Semiring α] {a a' : α} : (C (a + a') : MVPolynomial σ α) = C a + C a' := by
    simp only [C_apply, monomial, Finsupp.single_add_hom]
    exact Finsupp.single.add 0 a a'

  @[simp] theorem C_mul [Semiring α] : (C (a * a') : MVPolynomial σ α) = C a * C a' := C_mul_monomial.symm

  @[simp] theorem C_pow [Semiring α] (a : α) (n : Nat) : (C (a^n) : MVPolynomial σ α) = (C a)^n := by
    induction n with
    | zero => rfl
    | succ k ih => simp only [NCSemiring.pow_nat_succ, C.preserve_mul, ih]

end M4R
