import M4R.Algebra.Ring.Defs

namespace M4R

    structure PowerSeries (α : Type _) [Ring α] where
      coeff : Nat → α

    -- 0 has degree 0 here, not -∞, might have to change later
    structure Polynomial [Ring α] extends PowerSeries α where
      degree : Nat
      finite : (degree = 0 ∨ coeff degree ≠ 0) ∧ ∀ n, n > degree → coeff n = 0
  
end M4R