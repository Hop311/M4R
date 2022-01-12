import M4R.Notation

namespace M4R
  
  instance MemSubset [Mem α γ] : Subset γ where
    subset (a b : γ) := ∀ ⦃x : α⦄, x ∈ a → x ∈ b

  instance MemProperSubset [Mem α γ] : ProperSubset γ where
    propersubset (a b : γ) := (a ⊆ b) ∧ ∃ x : α, x ∉ a ∧ x ∈ b

  instance MemNotSubset [Mem α γ] : NotSubset γ where
    notsubset (a b : γ) := ¬(a ⊆ b)

  namespace Subset

    @[simp] theorem antisymm [Mem α γ] (a b : γ) : a ⊆ b ∧ b ⊆ a ↔ ∀ x : α, x ∈ a ↔ x ∈ b :=
      ⟨fun ⟨ab, ba⟩ x => ⟨@ab x, @ba x⟩, fun h =>
        ⟨fun x => (h x).mp, fun x => (h x).mpr⟩⟩

    @[simp] theorem toSuperset [Mem α γ] (a b : γ) (x : α) : x ∈ a → a ⊆ b → x ∈ b :=
      fun xa ab => @ab x xa

    @[simp] protected theorem refl [Mem α γ] (a : γ) : a ⊆ a := fun _ => id

    @[simp] protected theorem trans [Mem α γ] {a b c : γ} : a ⊆ b → b ⊆ c → a ⊆ c := fun ab bc x xa => bc (ab xa)

  end Subset
  namespace ProperSubset

    @[simp] theorem toSubset [Mem α γ] (a b : γ) : a ⊊ b → a ⊆ b := And.left

  end ProperSubset

end M4R