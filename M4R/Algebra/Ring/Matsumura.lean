import M4R.Algebra.Ring.IdealZorn
import M4R.Algebra.Ring.Localisation
import M4R.Algebra.Ring.Radical

namespace M4R
  open Monoid NCSemiring Semiring NCRing

  variable {A : Type _} [Ring A] {I : Ideal A}

  -- Theorem 1.1
  private theorem t1_1 (hI : I.proper_ideal) : ∃ J : Ideal A, I ⊆ J ∧ J.is_maximal :=
    let ⟨m, hm₁, hm₂⟩ := Ideal.ideal_zorn {J | I ⊆ J ∧ J.proper_ideal} (by
      intro c cs hc
      cases Classical.em (Nonempty c) with
      | inl h =>
        have hub₁ := fun (a : Ideal A) (ha : a ∈ c) => Ideal.ideal_chain_subset c ha hc
        have hub₂ := Ideal.ideal_chain_proper c h hc (fun J Jc => (cs Jc).right)
        exact ⟨Ideal.ideal_chain c h hc, ⟨let ⟨J, Jc⟩ := Classical.choice h
          Subset.trans (cs Jc).left (hub₁ J Jc), hub₂⟩, hub₁⟩
      | inr h => exact ⟨I, ⟨Subset.refl _, hI⟩, fun a ac => absurd ⟨a, ac⟩ h⟩)
    ⟨m, hm₁.left, ⟨hm₁.right, by intro J mJ; exact (Classical.em J.proper_ideal).imp (fun h =>
      hm₂ J ⟨Subset.trans hm₁.left mJ, h⟩ mJ) of_not_not⟩⟩

  theorem Ideal.exists_maximal_containing (hI : I.proper_ideal) : ∃ J : Ideal A, I ⊆ J ∧ J.is_maximal := t1_1 hI
  theorem Ideal.exists_prime_containing (hI : I.proper_ideal) : ∃ J : Ideal A, I ⊆ J ∧ J.is_prime :=
    let ⟨J, hIJ, hJ⟩ := t1_1 hI; ⟨J, hIJ, maximal_is_prime hJ⟩

  theorem Ideal.exists_maximal_containing_nonunit {x : A} (hx : ¬isUnit x) : ∃ I : Ideal A, I.is_maximal ∧ x ∈ I :=
    let ⟨I, hxI, hI⟩ := t1_1 (unit_not_principal hx); ⟨I, hI, hxI (generator_in_principal x)⟩
  theorem Ideal.exists_maximal_ideal_of_nontrivial [Ring A] (h : Ring.is_NonTrivial A) : ∃ I : Ideal A, I.is_maximal :=
    let ⟨I, _, hI⟩ := t1_1 (zero_ideal_proper_of_nontrivial h)
    ⟨I, hI⟩
  theorem Ideal.exists_prime_ideal_of_nontrivial [Ring A] (h : Ring.is_NonTrivial A) : ∃ I : Ideal A, I.is_prime :=
    let ⟨I, hI⟩ := exists_maximal_ideal_of_nontrivial h; ⟨I, maximal_is_prime hI⟩
  theorem Ideal.exists_maximal_ideal (A) [NonTrivialRing A] : ∃ I : Ideal A, I.is_maximal :=
    let ⟨I, _, hI⟩ := t1_1 (zero_ideal_proper A); ⟨I, hI⟩
  theorem Ideal.exists_prime_ideal (A) [NonTrivialRing A] : ∃ I : Ideal A, I.is_prime :=
    let ⟨I, hI⟩ := exists_maximal_ideal A; ⟨I, maximal_is_prime hI⟩

  theorem Ring.jacobson_radical.units {x : A} : x ∈ jacobson_radical A ↔ ↑{y : A | ∃ r, 1 + r * x = y} ⊆ unit_set A :=
    ⟨fun hx => fun y ⟨r, hrxy⟩ => Classical.byContradiction fun hy => by
      let ⟨M, hM, hyM⟩ := Ideal.exists_maximal_containing_nonunit hy
      rw [←hrxy] at hyM
      have := M.add_closed hyM ((M.mul_closed (-r) (maximal_subset_jacobson hM hx)))
      rw [add_assoc, neg_mul, add_neg, add_zero] at this
      exact absurd (Ideal.is_unit_ideal.mpr this) hM.left,
    fun hx => Ideal.sIntersection.mem.mpr fun M hM => Classical.byContradiction fun h =>
      let ⟨m, hm, x', ⟨s, hs⟩, h'⟩ := Ideal.is_unit_ideal.mp ((hM.right (Ideal.add.subset M (Ideal.principal x))).resolve_left
        fun h' => h (h' ▸ Ideal.add.subset' _ _ (Ideal.generator_in_principal x)))
      absurd (Ideal.is_unit_ideal'.mpr ⟨1 + -s * x, hx ⟨-s, rfl⟩, by
        rw [←h', ←hs, mul_comm, neg_mul, add_assoc, add_neg, add_zero]; exact hm⟩) hM.left⟩

  theorem Ring.nakayama {M : Ideal A} (hM : M.finitely_generated) {I : Ideal A} (hI : I ⊆ Ring.jacobson_radical A)
    (hIM : M = I * M) : M = 0 := by
      let ⟨f, hfM, hfmax⟩ := hM.has_minimal_generating_set
      byCases hf : f = ∅
      { rw [hf, Finset.empty_toSet, Ideal.from_set.empty] at hfM; exact hfM }
      { let ⟨g, hg⟩ : ∃ g, g ∈ f := Classical.byContradiction fun h => hf (Finset.ext fun x => by
          rw [Finset.mem_empty, iff_false]; exact not_exists.mp h x)
        have : g ∈ I * M := hIM ▸ hfM ▸ Ideal.from_set.contains_mem hg
        let ⟨c, hcI, hfc⟩ : ∃ c : A → A, (∀ x, c x ∈ I) ∧ g = ∑ x in f, c x * x :=
          let ⟨fs, c, hf, hc⟩ := Ideal.from_set.mem_as_sum.mp this
          @Finset.cons_induction _ (fun fs : Finset A => fs.toSet ⊆ Ideal.product_gen I M → ∀ g, g = (∑ x in fs, c x * x) →
            ∃ c : A → A, (∀ x, c x ∈ I) ∧ g = ∑ x in f, c x * x) (fun _ g hg => ⟨fun _ => 0, fun _ => I.has_zero, by
            rw [hg, Finset.map_sum.empty, Finset.map_sum.eq_zero (fun _ _ => by rw [zero_mul])]⟩)
            (fun x fs hx ih hfs g hg =>
              let ⟨c', hc', hgc'⟩ := ih (Subset.trans (fun _ => Finset.mem_cons_self' hx) hfs) (g - c x * x)
                (by rw [Finset.map_sum.cons] at hg; exact Group.sub_eq.mpr hg)
              let ⟨i, hi, m, hm, him⟩ := hfs (Finset.mem_cons_self fs hx)
              let ⟨mc, hmc⟩ := Ideal.from_set.mem_as_sum_finset.mp (hfM ▸ hm : m ∈ Ideal.from_set f.toSet)
              ⟨fun y => c' y + c x * i * mc y, fun y => I.add_closed (hc' y) (mul_right_comm _ _ _ ▸ I.mul_closed _ hi),
              by simp only [mul_distrib_right, Finset.map_sum.distrib, mul_assoc,
                ←Finset.map_sum.mul_sum]; rw [←hgc', ←hmc, ←him, Group.sub_add]⟩) fs hf g hc
        let ⟨u, hu⟩ : isUnit (1 - c g) := by exact jacobson_radical.units.mp (hI (hcI g)) ⟨-1, by rw [neg_one_mul, Group.sub_def]⟩
        have : (1 - c g) * g = ∑ x in f.erase g, c x * x := by
          rw [sub_mul_distrib_right, one_mul, Group.sub_eq, ←Finset.map_sum.sum_term _ _ hg, hfc]
        have := hfmax (f.erase g) (hfM ▸ Ideal.antisymm (Ideal.from_set.ideal_contained fun x hx => by
          byCases hxg : x = g
          { exact Ideal.from_set.mem_as_sum_finset.mpr ⟨fun y => u * c y, by
              simp only [mul_assoc]; rw [←Finset.map_sum.mul_sum, ←this, ←mul_assoc, mul_comm u, hu, one_mul, hxg]⟩ }
          { exact Ideal.from_set.contains_mem (Finset.mem_erase.mpr ⟨hxg, hx⟩) })
              (Ideal.from_set.subset fun x hx => (Finset.mem_erase.mp hx).right));
        exact absurd this (have : (f.erase g).length.succ = f.length := by
            rw [congrArg Finset.length (Finset.erase_cons f hg), Finset.length_cons]
          Nat.not_le.mpr (this ▸ Nat.lt.base _)) }

  -- Theorem 1.2
  private theorem t1_2 (I) (S : MultiplicativeSet A) (hIS : Set.disjoint I.subset S.subset) :
    ∃ J : Ideal A, I ⊆ J ∧ Set.disjoint J.subset S.subset ∧ J.is_prime :=
      let ⟨m, hm₁, hm₂⟩ := Ideal.ideal_zorn {J | I ⊆ J ∧ Set.disjoint J.subset S.subset} (by
        intro c cs hc; byCases h : Nonempty c
        { have hub₁ := fun (a : Ideal A) (ha : a ∈ c) => Ideal.ideal_chain_subset c ha hc
          have hub₂ := Ideal.ideal_chain_disjoint c h hc S.subset fun J Jc => (cs Jc).right;
          exact ⟨Ideal.ideal_chain c h hc, ⟨let ⟨J, Jc⟩ := Classical.choice h
            Subset.trans (cs Jc).left (hub₁ J Jc), hub₂⟩, hub₁⟩ }
        { exact ⟨I, ⟨Subset.refl _, hIS⟩, fun a ac => absurd ⟨a, ac⟩ h⟩ })
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
            (m.mul_closed _ s'im)) (m.mul_closed' r'im _), r * r'' * (s * s''), ⟨r'' * s'', by
              rw [mul_assoc, ←mul_assoc s, mul_comm s, mul_assoc, ←mul_assoc r]⟩, rfl⟩
        have h₃ : m + Ideal.principal (r * s) = m := Ideal.add.of_subset (Ideal.principal_in hrs)
        rw [h₃] at h₂
        exact Set.nonempty.mpr (⟨_, h₂, h₁⟩ : Nonempty ↑(m.subset ∩ S.subset)) hm₁.right⟩

  theorem Ideal.radical_prime_intersection (I : Ideal A) : I.radical = ⋂₀ {J | I ⊆ J ∧ J.is_prime} :=
    Ideal.antisymm (fun x hx => propext sIntersection.mem ▸ fun J ⟨hIJ, hJ⟩ =>
      (prime_radical hJ).eq_rad ▸ radical.subset hIJ hx)
      fun x hx => Classical.byContradiction fun hxI =>
        let S : MultiplicativeSet A := {
          subset := {a | ∃ n : Nat, a = x ^ n}
          has_one := ⟨0, rfl⟩
          mul_closed := fun ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n,
            hm ▸ hn ▸ (pow_nat_add_distrib x m n).symm⟩
        }
        let ⟨J, hIJ, hJS, hJ⟩ := t1_2 I.radical S (by
          apply Set.disjoint.elementwise.mpr; intro a haI ⟨n, hn⟩
          byCases hn0 : n = 0
          { apply ((is_unit_ideal.mpr (pow_nat_0 x ▸ hn0 ▸ hn ▸ haI)) ▸ hxI : x ∉ (1 : Ideal A)); trivial }
          { exact absurd (radical.is_radical I x n hn0 (hn ▸ haI)) hxI })
        absurd ⟨1, rfl⟩ (Set.disjoint.elementwise.mp hJS x
          (sIntersection.mem.mp hx J ⟨Subset.trans (radical.sub_self I) hIJ, hJ⟩))

  theorem Ring.nil_radical.eq_prime_intersection (A : Type _) [Ring A] : Ring.nil_radical A = ⋂₀ Ring.Spec A :=
    (Ideal.radical_prime_intersection 0).trans (Ideal.ext'.mpr fun x => by
      rw [Ideal.sIntersection.mem, Ideal.sIntersection.mem]; exact forall_congr' fun P => (by
        simp only [P.zero_ideal_in, true_and]; exact Iff.rfl : _ ∧ _ → _ ↔ _))

  -- Theorem 1.3
  private theorem t1_3 (fI : Finset (Ideal A)) (hfI : ∀ I ∈ fI, ∀ J ∈ fI, I ≠ J → Ideal.coprime I J) :
    ⋂₀ fI.toSet = ∏ fI := @Finset.cons_induction _ (fun f => f ⊆ fI → ⋂₀ f.toSet = ∏ f)
      (fun _ => by rw [Finset.empty_toSet, Ideal.sIntersection.empty]; rfl)
      (fun J s hJs ih hsfI => by
        rw [Finset.prod.cons, Ideal.product.coprime_eq_inter ((Ideal.coprime.comm _ _).mp (Ideal.product.prod_coprime
          (fun K hK => hfI J (hsfI (s.mem_cons_self hJs)) K (hsfI (Finset.mem_cons_self' hJs hK))
          fun h => absurd (h ▸ hK) hJs))), ←ih fun x hx => hsfI (Finset.mem_cons_self' hJs hx),
          ←Ideal.sIntersection.insert, Finset.cons_toSet])
      fI (Subset.refl fI)

  open QuotientRing

  -- Theorem 1.4
  private noncomputable def t1_4 (fI : Finset (Ideal A)) (hfI : ∀ I ∈ fI, ∀ J ∈ fI, I ≠ J → Ideal.coprime I J) :
    QClass (⋂₀ fI.toSet) ≅ᵣ MultiProd (fun i : fI => QClass i.val) :=
      Classical.choice (@Finset.cons_induction _ (fun f : Finset (Ideal A) => f ⊆ fI →
        Nonempty (QClass (⋂₀ f.toSet) ≅ᵣ MultiProd (fun i : f => QClass i.val)))
        (fun _ => by
          rw [Finset.empty_toSet, Ideal.sIntersection.empty]
          exact ⟨{
            hom           := fun _ _ => 0
            preserve_zero := rfl
            preserve_add  := fun _ _ => (add_zero _).symm
            preserve_neg  := fun _ => Group.neg_zero.symm
            preserve_mul  := fun _ _ => (mul_zero _).symm
            inv           := fun _ => 0
            left_inv      := fun x => (QuotientRing.trivial_zero x).symm
            right_inv     := fun x => funext fun ⟨_, _⟩ => by contradiction
          }⟩)
        (fun I s hI ih hs => by
          have f₁ := chinese_remainder_theorem (⋂₀ s.toSet) I ((Ideal.coprime.comm _ _).mp (Ideal.sIntersection.sinter_coprime
            fun J hJ => hfI I (hs (s.mem_cons_self hI)) J (hs (Finset.mem_cons_self' hI hJ)) fun h => absurd (h ▸ hJ) hI))
          have f₂ : QClass (⋂₀Finset.toSet s) × QClass I ≅ᵣ MultiProd (fun i : s => QClass i.val) × QClass I :=
            (Classical.choice (ih (fun x hx => hs (Finset.mem_cons_self' hI hx)))).Product RIsomorphism.Identity
          rw [Finset.cons_toSet, Ideal.sIntersection.insert]
          exact ⟨(f₁.comp f₂).comp (RIsomorphism.MultiProd_cons QClass hI)⟩) fI (Subset.refl _))

end M4R
