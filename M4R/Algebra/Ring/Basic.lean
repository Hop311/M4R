import M4R.Algebra.Ring.Defs

namespace M4R
  namespace Ring
    
    theorem one_mul [Ring α] (a : α) : 1 * a = a := by
      rw [mul_comm, mul_one]
    theorem mul_distrib_right [r : Ring α] (a b c: α) : (a + b) * c = a * c + b * c := by
      rw [mul_comm, mul_distrib_left, mul_comm c, mul_comm c, r.add_comm]

    theorem mul_zero [r : Ring α] (a : α) : a * 0 = 0 := by
      rw [←r.add_right_cancel _ _ (a * 0), r.zero_add, ←mul_distrib_left, r.zero_add]
    theorem zero_mul [Ring α] (a : α) : 0 * a = 0 := by
      rw [mul_comm, mul_zero]

    theorem neg_mul [r : Ring α] (a b : α) : -a * b = -(a * b) := by
      rw [←r.add_right_cancel _ _ (a * b), r.neg_add, ←mul_distrib_right, r.neg_add, zero_mul]
    theorem mul_neg [r : Ring α] (a b : α) : a * -b = -(a * b) := by
      rw [mul_comm, neg_mul, mul_comm]

    theorem divides_self [Ring α] (a : α) : divides a a := ⟨1, mul_one a⟩
    theorem divides_zero [Ring α] (a : α) : divides a 0 := ⟨0, mul_zero a⟩
    theorem divides_add [Ring α] (a b c : α) : divides a b → divides a c → divides a (b + c)
    | ⟨x, axb⟩, ⟨y, ayc⟩ => ⟨x + y, by rw [mul_distrib_left, axb, ayc]⟩
    theorem divides_mul [Ring α] (a b c : α) : divides a b → divides a (b * c)
    | ⟨x, axb⟩ => ⟨x * c, by rw [←mul_assoc, axb]⟩

    theorem isUnit_1 [Ring α] : isUnit (1 : α) := ⟨1, show 1 * 1 = 1 by rw [mul_one]⟩
    theorem notUnit_0 [Ring α] : (0 : α) ≠ (1 : α) → ¬isUnit (0 : α) := by
      intro h₁ ⟨_, h₂⟩; rw [zero_mul] at h₂; exact h₁ h₂
    theorem unit_mul [Ring α] {a b : α} : isUnit a → isUnit b → isUnit (a * b)
    | ⟨x, xs⟩, ⟨y, ys⟩ => by
      apply Exists.intro (y * x); rw [mul_assoc, ←mul_assoc b, ys, one_mul, xs];

    /-def unit_set (α : Type _) [Ring α] : Set α := {x | is_unit x}
    instance UnitGroup [Ring α] : Group ↑(unit_set α) where
      zero := ⟨1, ⟨1, by rw [mul_one]⟩⟩
      add := fun a b => ⟨a.val * b.val, unit_mul a.property b.property⟩
      neg := fun ⟨x, xs⟩ => by
          simp [unit_set, is_unit, divides] at xs;
          match xs with
          | ⟨y, yy⟩ => sorry-/

  end Ring
end M4R