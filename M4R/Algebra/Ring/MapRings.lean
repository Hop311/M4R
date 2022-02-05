import M4R.Algebra.Ring.Semiring

open Classical

namespace M4R

  noncomputable instance MapOne (α : Type _) (β : Type _) [Zero α] [Zero β] [One β] : One (α → β) where
    one := fun a => if a = 0 then 1 else 0

  namespace Finsupp        

    protected noncomputable instance one (α : Type _) (β : Type _) [Zero α] [Zero β] [One β] :
      One (α →₀ β) where one := single 0 1

    theorem one_def [Zero α] [Zero β] [One β] : (1 : α →₀ β) = single 0 1 := rfl

    theorem non_trivial [Zero α] [Zero β] [One β] (h10 : (1 : β) ≠ 0) : (1 : α →₀ β) = single 0 1 :=
      rfl

    theorem all_trivial (α : Type _) (β : Type _) [Zero α] [NCSemiring β] (h10 : (1 : β) = 0) 
      (x : α →₀ β) : x = 0 :=
        zero_fun fun a => NCSemiring.all_trivial h10 _

    protected noncomputable instance mul' [Monoid α] [NCSemiring β] : Mul (α →₀ β) where
      mul :=  fun x y => ∑ fun a₁ b₁ => ∑ fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) in y in x

    theorem mul_def [Monoid α] [NCSemiring β] {f g : α →₀ β} :
      f * g = ∑ fun a₁ b₁ => ∑ fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) in g in f := rfl

    noncomputable instance toNCSemiring [Monoid α] [NCSemiring β] : NCSemiring (α →₀ β) :=
      if h10 : (1 : β) = 0 then
        have := all_trivial α β h10
        {
          mul_zero          := fun x => this (x * 0)
          zero_mul          := fun x => this (0 * x)
          mul_one           := fun x => (this (x * 1)).trans (this x).symm
          one_mul           := fun x => (this (1 * x)).trans (this x).symm
          mul_assoc         := fun x y z => (this (x * y * z)).trans (this (x * (y * z))).symm
          mul_distrib_left  := fun x y z => (this (x * (y + z))).trans (this (x * y + x * z)).symm
          mul_distrib_right := fun x y z => (this ((x + y) * z)).trans (this (x * z + y * z)).symm
        }
      else
        {
          mul_zero          := fun x => by simp only [mul_def, map_sum.zero_sum, map_sum.sum_zero]
          zero_mul          := fun x => by simp only [mul_def, map_sum.zero_sum]
          mul_one           := fun x => by
            have : (fun (a₁ : α) (b₁ : β) => ∑ fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) in single 0 1)
              = fun a₁ b₁ => single a₁ b₁ := by
                apply funext; intro a₁; apply funext; intro b₁;
                rw [map_sum.single (0 : α) (1 : β) (fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂))
                  (by simp only [NCSemiring.mul_zero, single.zero]),
                  Monoid.add_zero, NCSemiring.mul_one]
            simp only [mul_def, non_trivial h10, mul_eq, this, map_sum.id]
          one_mul           := fun x => by
            have : (fun (a₂ : α) (b₂ : β) => single (0 + a₂) (1 * b₂)) = fun a₂ b₂ => single a₂ b₂ := by  
              apply funext; intro a₂; apply funext; intro b₂
              rw [Monoid.zero_add, NCSemiring.one_mul]
            simp only [mul_def, non_trivial h10, mul_eq]
            rw [map_sum.single 0 1 _ (by simp only [NCSemiring.zero_mul, single.zero, map_sum.sum_zero]),
              this, map_sum.id]
          mul_assoc         := fun x y z => by
            sorry
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

  end Finsupp
end M4R
