import M4R.Algebra.Ring.Ideal

namespace M4R
  namespace Ideal
    def subtype_subset [Ring α] {S : Set (Ideal α)} : S → S → Prop := fun (x y : S) => x.val ⊆ y.val
    local infix:50 " ≤ " => subtype_subset

    def of_subtype_set {s : Set α} (ss : Set ↑s) : Set α := {x | ∃ y ∈ ss, y.val = x}
    theorem of_subtype_set.subset {s : Set α} (ss : Set ↑s) : (of_subtype_set ss) ⊆ s := by
      intro _ ⟨⟨_, ys⟩, _, hyx⟩
      rw [←hyx]; exact ys

    theorem ideal_zorn [Ring α] (S : Set (Ideal α)) (h : ∀ c : Set (Ideal α), c ⊆ S →
      Zorn.Chain Subset.subset c → ∃ ub ∈ S, ∀ a ∈ c, a ⊆ ub) : ∃ m ∈ S, ∀ a ∈ S, m ⊆ a → a = m := by
        have : ∀ c : Set S, Zorn.Chain subtype_subset c → ∃ ub : S, ∀ a ∈ c, a ≤ ub := fun c hc =>
          have : Zorn.Chain Subset.subset (of_subtype_set c) := by
            intro x xc y yc hxy
            let ⟨a, ac, hax⟩ := xc
            let ⟨b, bc, hbx⟩ := yc
            have := hc a ac b bc (fun hab => hxy (by rw [←hax, ←hbx]; exact congrArg Subtype.val hab))
            rw [←hax, ←hbx]; exact this
          have ⟨ub, ubS, hub⟩ := h (of_subtype_set c) (of_subtype_set.subset c) this
          ⟨⟨ub, ubS⟩, fun ⟨a, aS⟩ ac => hub a ⟨⟨a, aS⟩, ac, rfl⟩⟩
        let ⟨⟨m, mS⟩, hm⟩ := Zorn.lemma_eq (@subtype_subset _ _ S) this
          Subset.trans (fun hab hbc => Set.elementExt (Ideal.antisymm hab hbc))
        exact ⟨m, mS, fun a as hma =>
          have := hm ⟨a, as⟩ hma
          congrArg Subtype.val this⟩

    def ideal_chain [Ring α] (S : Set (Ideal α)) (hS : Nonempty S) (hc : Zorn.Chain Subset.subset S) : Ideal α where
      subset := ⋃₀ (Set.toSetSet S Ideal.subset)
      has_zero :=
        let ⟨x, xS⟩ := Classical.choice hS
        ⟨x.subset, ⟨x, xS, rfl⟩, x.has_zero⟩
      add_closed := by
        intro a b ⟨i, ⟨I, IS, Ii⟩, ai⟩ ⟨j, ⟨J, JS, Jj⟩, bj⟩
        cases Classical.em (I = J) with
        | inl h =>
          rw [←Ii] at ai; rw [←h] at Jj; rw [←Jj] at bj
          exact ⟨I.subset, ⟨I, IS, rfl⟩, I.add_closed ai bj⟩
        | inr h =>
          cases hc I IS J JS h with
          | inl h =>
            rw [←Ii] at ai; rw [←Jj] at bj
            exact ⟨J.subset, ⟨J, JS, rfl⟩, J.add_closed (h ai) bj⟩
          | inr h =>
            rw [←Ii] at ai; rw [←Jj] at bj
            exact ⟨I.subset, ⟨I, IS, rfl⟩, I.add_closed ai (h bj)⟩
      mul_closed := by
        intro a b ⟨i, ⟨I, IS, Ii⟩, bi⟩
        rw [←Ii] at bi
        exact ⟨I.subset, ⟨I, IS, rfl⟩, I.mul_closed a bi⟩

    theorem ideal_chain_subset [Ring α] (S : Set (Ideal α)) {I : Ideal α} (IS : I ∈ S)
      (hc : Zorn.Chain Subset.subset S) : I ⊆ ideal_chain S ⟨I, IS⟩ hc :=
        fun x xI => ⟨I.subset, ⟨I, IS, rfl⟩, xI⟩

    theorem ideal_chain_proper [Ring α] (S : Set (Ideal α)) (hS : Nonempty S) (hc : Zorn.Chain Subset.subset S) :
      (∀ I ∈ S, I.proper_ideal) → (ideal_chain S hS hc).proper_ideal := by
        intro h hU
        let ⟨_, ⟨I, IS, hI⟩, hIu⟩ := is_unit_ideal.mp hU
        rw [←hI] at hIu
        exact absurd (is_unit_ideal.mpr hIu) (h I IS)

    theorem ideal_chain_disjoint [Ring α] (S : Set (Ideal α)) (hS : Nonempty S) (hc : Zorn.Chain Subset.subset S) (S' : Set α) :
      (∀ I ∈ S, Set.disjoint I.subset S') → (Set.disjoint (ideal_chain S hS hc).subset S') := by
        intro h
        apply Set.disjoint.elementwise.mpr
        intro x ⟨y, ⟨J, JS, hJy⟩, xy⟩; rw [←hJy] at xy
        exact Set.disjoint.elementwise.mp (h J JS) x xy
  end Ideal
end M4R