import M4R.Algebra

namespace M4R
  open Group
  open NCRing
  open Ring

  variable {A : Type _} [Ring A] {I : Ideal A}

  theorem t1_1 (hI : I.proper_ideal) : ∃ J : Ideal A, I ⊆ J ∧ J.is_maximal :=
    let ⟨m, hm₁, hm₂⟩ := Ideal.ideal_zorn {J | I ⊆ J ∧ J.proper_ideal} (by
      intro c cs hc
      cases Classical.em (Nonempty c) with
      | inl h =>
        have hub₁ := fun (a : Ideal A) (ha : a ∈ c) => Ideal.ideal_chain_subset c ha hc
        have hub₂ := Ideal.ideal_chain_proper c h hc (fun J Jc => (cs Jc).right)
        exact ⟨Ideal.ideal_chain c h hc, ⟨let ⟨J, Jc⟩ := Classical.choice h
          Subset.trans (cs Jc).left (hub₁ J Jc), hub₂⟩, hub₁⟩
      | inr h => exact ⟨I, ⟨Subset.refl _, hI⟩, fun a ac => absurd ⟨a, ac⟩ h⟩)
    ⟨m, hm₁.left, ⟨hm₁.right, by
      intro J mJ
      cases Classical.em (J.proper_ideal) with
      | inl h => exact Or.inl (hm₂ J ⟨Subset.trans hm₁.left mJ, h⟩ mJ)
      | inr h => exact Or.inr (of_not_not h)
    ⟩⟩

  structure MultiplicativeSet (A : Type _) [Ring A] where
    subset : Set A
    has_one : 1 ∈ subset
    mul_closed : ∀ {a b : A}, a ∈ subset → b ∈ subset → a * b ∈ subset
  instance MultiplicativeSet.MultiplicativeSetMem : Mem A (MultiplicativeSet A) where mem := fun x I => x ∈ I.subset

  theorem MultiplicativeSet.disjoint_ideal_proper {S : MultiplicativeSet A} (hIS : Set.disjoint I.subset S.subset) : I.proper_ideal :=
    fun h =>
      have : 1 ∉ I := Set.disjoint.elementwise.mp (hIS.comm) 1 S.has_one
      absurd (Ideal.is_unit_ideal.mp h) this

  theorem t1_2 (S : MultiplicativeSet A) (hIS : Set.disjoint I.subset S.subset) :
    ∃ J : Ideal A, I ⊆ J ∧ Set.disjoint J.subset S.subset ∧ J.is_prime :=
      let ⟨m, hm₁, hm₂⟩ := Ideal.ideal_zorn {J | I ⊆ J ∧ Set.disjoint J.subset S.subset} (by
        intro c cs hc
        cases Classical.em (Nonempty c) with
        | inl h =>
          have hub₁ := fun (a : Ideal A) (ha : a ∈ c) => Ideal.ideal_chain_subset c ha hc
          have hub₂ := Ideal.ideal_chain_disjoint c h hc S.subset (fun J Jc => (cs Jc).right)
          exact ⟨Ideal.ideal_chain c h hc, ⟨let ⟨J, Jc⟩ := Classical.choice h
            Subset.trans (cs Jc).left (hub₁ J Jc), hub₂⟩, hub₁⟩
        | inr h => exact ⟨I, ⟨Subset.refl _, hIS⟩, fun a ac => absurd ⟨a, ac⟩ h⟩)
      ⟨m, hm₁.left, hm₁.right, S.disjoint_ideal_proper hm₁.right, by
        intro r s hrs; apply Classical.byContradiction; rw [not_or_iff_and_not]; intro ⟨nrm, nsm⟩
        have : ∀ {x}, x ∉ m → ¬Set.disjoint (m + Ideal.principal x).subset S.subset := by
          intro x xnm h; apply xnm
          have := hm₂ (m + Ideal.principal x) ⟨Subset.trans hm₁.left (Ideal.add.subset m (Ideal.principal x)), h⟩
            (Ideal.add.subset m (Ideal.principal x))
          rw [←this]; exact ⟨0, m.has_zero, x, Ideal.generator_in_principal x, zero_add x⟩

        have ⟨r', ⟨r'i, r'im, r'j, ⟨r'', hr''⟩, hr'ij⟩, r'S⟩ := Classical.choice (Set.nonempty.mp (this nrm))
        have ⟨s', ⟨s'i, s'im, s'j, ⟨s'', hs''⟩, hs'ij⟩, s'S⟩ := Classical.choice (Set.nonempty.mp (this nsm))

        have h₁ := S.mul_closed r'S s'S
        rw [←hr'ij, ←hs'ij, ←hr'', ←hs'', mul_distrib_left, mul_distrib_right, mul_distrib_right, ←add_assoc] at h₁
        have h₂ : r'i * s'i + r * r'' * s'i + r'i * (s * s'') + r * r'' * (s * s'') ∈ m + Ideal.principal (r * s) :=
          ⟨r'i * s'i + r * r'' * s'i + r'i * (s * s''), m.add_closed (m.add_closed (m.mul_closed _ s'im)
            (m.mul_closed _ s'im)) (m.mul_closed' r'im _),
            r * r'' * (s * s''), ⟨r'' * s'', by
              rw [mul_assoc, ←mul_assoc s, mul_comm s,mul_assoc, ←mul_assoc r]⟩, rfl⟩
        have h₃ : m + Ideal.principal (r * s) = m := by
          rw [Ideal.add.comm]; exact Ideal.add.of_subset (Ideal.principal_in m _ hrs)
        rw [h₃] at h₂

        exact Set.nonempty.mpr (⟨_, h₂, h₁⟩ : Nonempty ↑(m.subset ∩ S.subset)) hm₁.right⟩

end M4R