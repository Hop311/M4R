import M4R.Algebra.Ring.Quotient

namespace M4R
  namespace Ideal
    def subtype_subset [Ring α] {S : Set (Ideal α)} : S → S → Prop := fun (x y : S) => x.val ⊆ y.val
    local infix:50 " ≤ " => subtype_subset

    def subtype_set {s : Set α} (ss : Set ↑s) : Set α := {x | ∃ y ∈ ss, y.val = x}
    theorem subtype_set.subset {s : Set α} (ss : Set ↑s) : (subtype_set ss) ⊆ s := by
      intro _ ⟨⟨_, ys⟩, _, hyx⟩;
      rw [←hyx]; exact ys

    theorem ideal_zorn [Ring α] (S : Set (Ideal α)) (h : ∀ c : Set (Ideal α), c ⊆ S →
      Zorn.Chain Subset.subset c → ∃ ub ∈ S, ∀ a ∈ c, a ⊆ ub) : ∃ m ∈ S, ∀ a ∈ S, m ⊆ a → a = m := by
        have : ∀ c : Set S, Zorn.Chain subtype_subset c → ∃ ub : S, ∀ a ∈ c, a ≤ ub := fun c hc =>
          have : Zorn.Chain Subset.subset (subtype_set c) := by
            intro x xc y yc hxy;
            let ⟨a, ac, hax⟩ := xc
            let ⟨b, bc, hbx⟩ := yc
            have := hc a ac b bc (by intro hab; apply hxy; rw [←hax, ←hbx]; exact congrArg Subtype.val hab)
            rw [←hax, ←hbx]; exact this
          have ⟨ub, ubS, hub⟩ := h (subtype_set c) (subtype_set.subset c) this
          ⟨⟨ub, ubS⟩, fun ⟨a, aS⟩ ac => hub a ⟨⟨a, aS⟩, ac, rfl⟩⟩
        let ⟨⟨m, mS⟩, hm⟩ := Zorn.lemma_eq (@subtype_subset _ _ S) this
          Subset.trans (fun hab hbc => Set.elementExt (Ideal.antisymm hab hbc))
        exact ⟨m, mS, fun a as hma =>
          have := hm ⟨a, as⟩ hma
          congrArg Subtype.val this⟩
  end Ideal
end M4R