import M4R.Algebra.Ring

namespace M4R

  class Module (R : Type _) (M : Type _) [Ring R] [AbelianGroup M] extends HMul R M M where
    one_mul          : ∀ (x : M), (1 : R) * x = x
    mul_assoc        : ∀ (r s : R) (x : M), (r * s) * x = r * (s * x)
    mul_distrib_left  : ∀ (r : R) (x y : M), r * (x + y) = r * x + r * y
    mul_distrib_right : ∀ (r s : R) (x : M), (r + s) * x = r * x + s * x

  instance RingModule (R : Type _) [r : Ring R] : Module R R where
    hMul              := r.mul
    one_mul           := r.one_mul
    mul_assoc         := r.mul_assoc
    mul_distrib_left  := r.mul_distrib_left
    mul_distrib_right := r.mul_distrib_right

  instance IdealModule (R : Type _) [r : Ring R] (I : Ideal R) : Module R ↑I.subset where
    hMul              := fun s ⟨t, ts⟩ => ⟨s * t, I.closed_mul s t ts⟩
    one_mul           := by intro ⟨x, _⟩; simp [Ideal.image_eq]; exact r.one_mul x
    mul_assoc         := by intro s t ⟨x, _⟩; simp [Ideal.image_eq]; exact r.mul_assoc s t x
    mul_distrib_left  := by intro s ⟨x, _⟩ ⟨y, _⟩; simp [Ideal.image_eq]; exact r.mul_distrib_left s x y
    mul_distrib_right := by intro s t ⟨x, _⟩; simp [Ideal.image_eq]; exact r.mul_distrib_right s t x
    
  instance RHomomorphismModule (R : Type _) (S : Type _) [iR : Ring R] [iS : Ring S] (rh : RHomomorphism R S) : Module R S where
    hMul := fun r s => (rh.hom r) * s
    one_mul := by intro x; have := iS.one_mul x; simp [HMul.hMul] at *; rw [rh.preserve_one]; exact this
    mul_assoc := by
      intro r s x; have := iS.mul_assoc (rh.hom r) (rh.hom s) x;
      rw [rh.preserve_mul] at this; simp [HMul.hMul] at *; exact this
    mul_distrib_left := by
      intro r x y; have := iS.mul_distrib_left (rh.hom r) x y;
      simp [HMul.hMul] at *; exact this
    mul_distrib_right := by
      intro r s x; have := iS.mul_distrib_right (rh.hom r) (rh.hom s) x;
      rw [←rh.preserve_add] at this; simp [HMul.hMul] at *; exact this

end M4R