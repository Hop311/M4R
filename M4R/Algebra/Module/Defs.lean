import M4R.Algebra.Ring

namespace M4R

  class Module (R : Type _) (M : Type _) [Ring R] [AbelianGroup M] extends HMul R M M where
    one_mul          : ∀ (x : M), (1 : R) * x = x
    mul_assoc        : ∀ (r s : R) (x : M), (r * s) * x = r * (s * x)
    mul_distrib_left  : ∀ (r : R) (x y : M), r * (x + y) = r * x + r * y
    mul_distrib_right : ∀ (r s : R) (x : M), (r + s) * x = r * x + s * x

  def RingModule (R : Type _) [r : Ring R] : Module R R where
    hMul              := r.mul
    one_mul           := r.one_mul
    mul_assoc         := r.mul_assoc
    mul_distrib_left  := r.mul_distrib_left
    mul_distrib_right := r.mul_distrib_right

  def IdealModule (R : Type _) [r : Ring R] (I : Ideal R) : Module R ↑I.subset where
    hMul              := fun s ⟨t, ts⟩ => ⟨s * t, I.mul_closed s ts⟩
    one_mul           := fun ⟨x, _⟩ => by simp only [Ideal.image_eq]; exact r.one_mul x
    mul_assoc         := fun s t ⟨x, _⟩ => by simp only [Ideal.image_eq]; exact r.mul_assoc s t x
    mul_distrib_left  := fun s ⟨x, _⟩ ⟨y, _⟩ => by simp only [Ideal.image_eq]; exact r.mul_distrib_left s x y
    mul_distrib_right := fun s t ⟨x, _⟩ => by simp only [Ideal.image_eq]; exact r.mul_distrib_right s t x

  def RHomomorphismModule (R : Type _) (S : Type _) [iR : Ring R] [iS : Ring S] (rh : RHomomorphism R S) : Module R S where
    hMul := fun r s => (rh r) * s
    one_mul := fun x => by have := iS.one_mul x; simp only [HMul.hMul] at *; rw [rh.preserve_one]; exact this
    mul_assoc := fun r s x => by
      have := iS.mul_assoc (rh r) (rh s) x;
      rw [←rh.preserve_mul] at this; simp only [HMul.hMul] at *; exact this
    mul_distrib_left := fun r x y => by
      have := iS.mul_distrib_left (rh r) x y;
      simp only [HMul.hMul] at *; exact this
    mul_distrib_right := fun r s x => by
      have := iS.mul_distrib_right (rh r) (rh s) x;
      rw [←rh.preserve_add] at this; simp only [HMul.hMul] at *; exact this

end M4R
