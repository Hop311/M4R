import M4R.Algebra.Ring.Ring
import M4R.Algebra.Ring.RMorphism

open Classical

namespace M4R

  namespace Finsupp

    protected noncomputable instance one (α : Type _) (β : Type _) [Zero α] [Zero β] [One β] :
      One (α →₀ β) where one := single 0 1

    theorem one_def [Zero α] [Zero β] [One β] : (1 : α →₀ β) = single 0 1 := rfl

    theorem all_trivial (α : Type _) (β : Type _) [Zero α] [NCSemiring β] (h10 : (1 : β) = 0)
      (x : α →₀ β) : x = 0 :=
        zero_fun fun a => NCSemiring.all_trivial h10 _

    protected noncomputable instance mul' [Monoid α] [NCSemiring β] : Mul (α →₀ β) where
      mul :=  fun x y => ∑ fun a₁ b₁ => ∑ fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) in y in x

    theorem mul_def [Monoid α] [NCSemiring β] {f g : α →₀ β} :
      f * g = ∑ fun a₁ b₁ => ∑ fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) in g in f := rfl

    noncomputable instance toNCSemiring [Monoid α] [NCSemiring β] : NCSemiring (α →₀ β) :=
      {
        mul_zero          := fun x => by simp only [mul_def, map_sum.zero_sum, map_sum.sum_zero]
        zero_mul          := fun x => by simp only [mul_def, map_sum.zero_sum]
        mul_one           := fun x => by
          have : (fun (a₁ : α) (b₁ : β) => ∑ fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) in single 0 1)
            = fun a₁ b₁ => single a₁ b₁ := by
              apply funext; intro a₁; apply funext; intro b₁
              rw [map_sum.single (0 : α) (1 : β) (fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂))
                (by simp only [NCSemiring.mul_zero, single.zero]),
                Monoid.add_zero, NCSemiring.mul_one]
          simp only [mul_def, one_def, mul_eq, this, map_sum.sum_single]
        one_mul           := fun x => by
          have : (fun (a₂ : α) (b₂ : β) => single (0 + a₂) (1 * b₂)) = fun a₂ b₂ => single a₂ b₂ := by
            apply funext; intro a₂; apply funext; intro b₂
            rw [Monoid.zero_add, NCSemiring.one_mul]
          simp only [mul_def, one_def, mul_eq]
          rw [map_sum.single 0 1 _ (by simp only [NCSemiring.zero_mul, single.zero, map_sum.sum_zero]),
            this, map_sum.sum_single]
        mul_assoc         := fun x y z => by
          simp only [mul_def]
          have h₁ : ∀ a, (∑ fun a₂ b₂ => single (a + a₂) (0 * b₂) in z) = 0 := by
            intros; simp only [NCSemiring.zero_mul, single.zero, map_sum.sum_zero]
          have h₂ : ∀ (a : α) (b₁ b₂ : β),
            (∑ fun a₂ b₂_1 => single (a + a₂) ((b₁ + b₂) * b₂_1) in z) =
              (∑ fun a₂ b₂ => single (a + a₂) (b₁ * b₂) in z) + ∑ fun a₂ b₂_1 => single (a + a₂) (b₂ * b₂_1) in z := by
                intro a b b'; simp only; rw [←map_sum.sum_add]; apply map_sum.congr
                intros; rw [←single.add, NCSemiring.mul_distrib_right]
          have h₃ : ∀ {a₁} a, single (a₁ + a) (to_fun x a₁ * 0) = 0 := by
            intros; rw [NCSemiring.mul_zero, single.zero]
          have h₄ : ∀ {a₁} (a) (b₁ b₂), single (a₁ + a) (to_fun x a₁ * (b₁ + b₂)) =
              single (a₁ + a) (to_fun x a₁ * b₁) + single (a₁ + a) (to_fun x a₁ * b₂) := by
                intros; rw [←single.add, NCSemiring.mul_distrib_left]
          rw [map_sum.sum_sum h₁ h₂]; apply map_sum.congr; intros
          rw [map_sum.sum_sum h₁ h₂, map_sum.sum_sum h₃ h₄]; apply map_sum.congr; intros
          rw [map_sum.single _ _ _ (by
            conv => rhs; rw [←map_sum.sum_zero z]
            apply map_sum.congr; intros; rw [NCSemiring.zero_mul, single.zero])]
          rw [map_sum.sum_sum h₃ h₄]; apply map_sum.congr; intros
          rw [map_sum.single _ _ _ (by rw [NCSemiring.mul_zero, single.zero]), Monoid.add_assoc, NCSemiring.mul_assoc]
        mul_distrib_left  := fun x y z => by
          simp only [mul_def]
          have : (fun a₁ b₁ => (∑ fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) in (y + z))) =
            fun a₁ b₁ => (∑ fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) in y) + ∑ fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) in z :=
              funext fun _ => funext fun _ =>
                map_sum.add_sum y z _ (fun _ => by rw [NCSemiring.mul_zero, single.zero])
                  (fun _ => by rw [←single.add, add_apply, NCSemiring.mul_distrib_left])
          rw [this]; exact map_sum.sum_add
        mul_distrib_right := fun x y z => by
          simp only [mul_def]
          exact map_sum.add_sum x y _ (fun _ =>
            map_sum.map_eq_zero (by intros; rw [NCSemiring.zero_mul, single.zero]))
              (fun _ => by
                rw [←map_sum.sum_add]; exact map_sum.congr (by
                  intros; rw [←single.add, add_apply, NCSemiring.mul_distrib_right]))
      }

    noncomputable instance toNonTrivialNCSemiring [Monoid α] [NonTrivialNCSemiring β] : NonTrivialNCSemiring (α →₀ β) where
      one_neq_zero := by
        intro h; simp only [one_def] at h
        have := congrArg (fun (x : α →₀ β) => x (0 : α)) h
        simp only [single.eq_same, zero_apply] at this
        exact absurd this NonTrivial.one_neq_zero

    noncomputable instance toSemiring [CommMonoid α] [Semiring β] : Semiring (α →₀ β) where
      mul_comm := fun x y => by
        simp only [mul_def, Finsupp.map_sum, Semiring.mul_comm]
        rw [Finset.map_sum.comm]; simp only [CommMonoid.add_comm]

    noncomputable instance toNCRing [Monoid α] [NCRing β] : NCRing (α →₀ β) where
      toNeg   := Finsupp.neg
      add_neg := toGroup.add_neg

    noncomputable instance toRing [CommMonoid α] [Ring β] : Ring (α →₀ β) where
      toNCRing := toNCRing
      mul_comm := toSemiring.mul_comm

    noncomputable instance UnitFinsuppNCSemiring [NCSemiring α] : (Unit →₀ α) ≅* α where
      toMHomomorphism := UnitFinsuppMonoid.toMHomomorphism
      preserve_mul := fun x y => by
        simp only [mul_def]
        have : (fun a₂ b₂ => single (Unit.unit + a₂) ((0 : α) * b₂)) = fun _ _ => (0 : Unit →₀ α) := by
          apply funext; intro u; cases u; apply funext; intro u
          rw [NCSemiring.zero_mul, single.zero]
        rw [map_sum.unit_sum x (by rw [this, map_sum.sum_zero]), map_sum.unit_sum y
          (by rw [NCSemiring.mul_zero, single.zero])]
        simp only [UnitFinsuppMonoid]; have : Unit.unit + Unit.unit = Unit.unit := rfl
        rw [this, single.eq_same]
      inv := UnitFinsuppMonoid.inv
      left_inv := UnitFinsuppMonoid.left_inv
      right_inv := UnitFinsuppMonoid.right_inv

    noncomputable instance UnitFinsuppNCRing [NCRing α] : (Unit →₀ α) ≅ᵣ α where
      toSMulMap := UnitFinsuppNCSemiring.toSMulMap
      preserve_neg := UnitFinsuppGroup.preserve_neg
      inv := UnitFinsuppMonoid.inv
      left_inv := UnitFinsuppMonoid.left_inv
      right_inv := UnitFinsuppMonoid.right_inv

    @[simp] theorem single_mul_single [Monoid α] [NCSemiring β] {a₁ a₂ : α} {b₁ b₂ : β} :
        single a₁ b₁ * single a₂ b₂ = single (a₁ + a₂) (b₁ * b₂) := by
          simp only [mul_def, map_sum.single, NCSemiring.zero_mul, NCSemiring.mul_zero, single.zero]

  end Finsupp
end M4R
