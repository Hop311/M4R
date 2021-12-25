import M4R.Algebra

namespace M4R

  variable {A : Type _} [Ring A] {I : Ideal A}

  def super_ideals (I : Ideal A) : Set (Ideal A) := {J | I ⊆ J ∧ J.proper_ideal}
  def subtype_subset : super_ideals I → super_ideals I → Prop := fun (x y : super_ideals I) => x.val ⊆ y.val
  local infix:50 " ⊆ " => subtype_subset
  def subtype_set {s : Set α} (ss : Set ↑s) : Set α := {x | ∃ y ∈ ss, y.val = x}

  theorem t1_1 : I.proper_ideal → ∃ J : Ideal A, I ⊆ J ∧ J.is_maximal := by
    intro hI;
    have : ∀ c : Set ↑(super_ideals I), Zorn.Chain subtype_subset c → ∃ ub : super_ideals I, ∀ a ∈ c, a ⊆ ub := by
      intro c hc;
      have hcc : Zorn.Chain Subset.subset (subtype_set c) := by
        intro X ⟨sX, hX₁, hX₂⟩ Y ⟨sY, hY₁, hY₂⟩ hXY
        rw [←hX₂, ←hY₂]; rw [←hX₂, ←hY₂] at hXY
        exact hc sX hX₁ sY hY₁ (by intro hs; apply hXY; rw [hs])
      cases Classical.em (Nonempty (subtype_set c)) with
      | inl h =>
        have hub₁ := fun (a : Ideal A) (ha : a ∈ subtype_set c) =>
          Ideal.ideal_chain_subset (subtype_set c) ha hcc
        have hub₂ := Ideal.ideal_chain_proper (subtype_set c) h hcc (fun I ⟨⟨I', ⟨_, hI'⟩⟩, _, hII'⟩ =>
          by rw [←hII']; exact hI');
        exact
          ⟨
            ⟨
              Ideal.ideal_chain (subtype_set c) h hcc,
              ⟨
                let ⟨⟨J, hJ⟩, _⟩ := Classical.exists_true_of_nonempty h
                let ⟨⟨J', hIJ'⟩, _, hJJ'⟩ := hJ
                Subset.trans (by rw [←hJJ']; exact hIJ'.left) (hub₁ J hJ),
                Ideal.ideal_chain_proper (subtype_set c) h hcc (fun I ⟨⟨I', ⟨_, hI'⟩⟩, _, hII'⟩ =>
                  by rw [←hII']; exact hI')
              ⟩
            ⟩,
            fun J hJ => hub₁ J.val ⟨J, hJ, rfl⟩
          ⟩
      | inr h =>
        exact ⟨⟨I, Subset.refl _, hI⟩, fun I hI => absurd ⟨I.val, I, hI, rfl⟩ h⟩
    have ⟨J, hJ⟩ := Zorn.lemma_eq subtype_subset this Subset.trans (fun hab hbc => Set.elementExt (Ideal.antisymm hab hbc))
    exact ⟨J, J.property.left, fun J' hJ' => by
      cases Classical.em (J'.proper_ideal) with
      | inl h =>
        exact Or.inl (by rw [←hJ ⟨J', Subset.trans J.property.left hJ', h⟩ hJ'])
      | inr h =>
        exact Or.inr (of_not_not h)⟩

  structure MultiplicativeSet (α : Type _) [Ring α] where
    subset : Set α
    has_one : 1 ∈ subset
    mul_closed : ∀ {a b : α}, a ∈ subset → b ∈ subset → a * b ∈ subset
  instance MultiplicativeSet.MultiplicativeSetMem [Ring α] : Mem α (MultiplicativeSet α) where mem := fun x I => x ∈ I.subset

  theorem t1_2 : ∀ (S : MultiplicativeSet A), Set.disjoint I.subset S.subset →
    ∃ J : Ideal A, I ⊆ J ∧ Set.disjoint J.subset S.subset ∧ J.is_prime :=
      sorry

end M4R