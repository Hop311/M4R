import M4R.Set.Basic

namespace M4R
  namespace Zorn

    open Classical

    variable (r : α → α → Prop)
    local infix:50 " ≤ " => r

    def Chain (c : Set α) := ∀ x ∈ c, ∀ y ∈ c, x ≠ y → r x y ∨ r y x

    theorem chain_insert {c : Set α} {a : α} (hc : Chain r c) (ha : ∀ b ∈ c, b ≠ a → a ≤ b ∨ b ≤ a) :
      Chain r (c.insert a) := by
        intro x hx y hy hxy;
        cases hx with
        | inl hx =>
          rw [hx] at hxy; rw [hx];
          exact ha y (hy.resolve_left hxy.symm) hxy.symm;
        | inr hx =>
          cases hy with
          | inl hy =>
            rw [hy] at hxy; rw [hy];
            exact (ha x hx hxy).comm
          | inr hy =>
            exact hc x hx y hy hxy;

    /-- `super_chain c₁ c₂` means that `c₂ is a chain that strictly includes `c₁`. -/
    def super_chain (c₁ c₂ : Set α) : Prop := Chain r c₂ ∧ c₁ ⊊ c₂

    /-- A chain `c` is a maximal chain if there does not exists a chain strictly including `c`. -/
    def is_max_chain (c : Set α) := Chain r c ∧ ¬ (∃ c', super_chain r c c')

    /-- Given a set `c`, if there exists a chain `c'` strictly including `c`, then `succ_chain c`
    is one of these chains. Otherwise it is `c`. -/
    def succ_chain (c : Set α) : Set α :=
      if h : ∃ c' : Set α, Chain r c ∧ super_chain r c c' then
        choose h
      else c

    theorem succ_spec {c : Set α} (h : ∃ c', Chain r c ∧ super_chain r c c') :
      super_chain r c (succ_chain r c) := by
        have ⟨_, h'⟩: Chain r c ∧ super_chain r c (choose h) := by
          exact @choose_spec _ (fun c' => Chain r c ∧ super_chain r c c') _
        simp only [succ_chain, dif_pos h, h']
      
    theorem chain_succ {c : Set α} (hc : Chain r c) : Chain r (succ_chain r c) :=
      if h : ∃c', Chain r c ∧ super_chain r c c' then
        (succ_spec r h).left
      else
        by simp only [succ_chain, dif_neg h]; exact hc

    theorem super_of_not_max {c : Set α} (hc₁ : Chain r c) (hc₂ : ¬ is_max_chain r c) :
      super_chain r c (succ_chain r c) := by
        simp only [is_max_chain, not_and_iff_or_not, iff_not_not] at hc₂;
        exact Or.elim hc₂ (fun _ => by contradiction) (fun ⟨c', hc'⟩ => succ_spec r ⟨c', hc₁, hc'⟩)

    theorem succ_increasing {c : Set α} : c ⊆ succ_chain r c :=
      if h : ∃c', Chain r c ∧ super_chain r c c' then
        (succ_spec r h).right.left
      else
        by simp only [succ_chain, dif_neg h, Subset.refl];

    /-- Set of sets reachable from `∅` using `succ_chain` and `⋃₀`. -/
    inductive chain_closure : Set α → Prop
    | succ : ∀ {s}, chain_closure s → chain_closure (succ_chain r s)
    | union : ∀ {s}, (∀ a ∈ s, chain_closure a) → chain_closure (⋃₀ s)

    theorem chain_closure_closure : chain_closure r (⋃₀ chain_closure r) :=
      chain_closure.union (fun _ => id)
      
    private theorem chain_closure_succ_total_aux (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂)
      (h : ∀{c₃}, chain_closure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ succ_chain r c₃ ⊆ c₂) : c₁ ⊆ c₂ ∨ succ_chain r c₂ ⊆ c₁ := by
        induction hc₁
        case succ c₃ hc₃ ih =>
          cases ih with
          | inl ih =>
            cases h hc₃ ih with
            | inl h => rw [h]; exact Or.inr (Subset.refl _)
            | inr h => exact Or.inl h
          | inr ih => exact Or.inr (Subset.trans ih (succ_increasing r))
        case union s hs ih =>
          exact or_iff_not_imp_right.mpr (fun hn =>
            Set.SoSUnion.subset (fun a ha =>
              (ih a ha).resolve_right (mt (fun h =>
                Subset.trans h (Set.SoSUnion.subset_of_mem ha)) hn)))

    private theorem chain_closure_succ_total (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂) (h : c₁ ⊆ c₂) :
      c₂ = c₁ ∨ succ_chain r c₁ ⊆ c₂ := by
        induction hc₂ generalizing c₁ hc₁;
        case succ c₂ hc₂ ih =>
          have : c₁ ⊆ c₂ ∨ succ_chain r c₂ ⊆ c₁ := chain_closure_succ_total_aux r hc₁ hc₂ ih
          cases this with
          | inl h₁ =>
            cases (ih hc₁ h₁) with
            | inl h₂ => rw [h₂]; exact Or.inr (Subset.refl _)
            | inr h₂ => exact Or.inr (Subset.trans h₂ (succ_increasing r))
          | inr h₁ => exact (Or.inl (Set.subset.antisymm h₁ h))
        case union s hs ih =>
          apply Or.imp_left (fun h' => Set.subset.antisymm h' h)
          apply byContradiction;
          simp [not_or_iff_and_not, Set.SoSUnion.subset_iff, not_forall, and_imp];
          intro c₃ hc₃ h₁ h₂;
          have := chain_closure_succ_total_aux r hc₁ (hs c₃ hc₃) (ih _ hc₃);
          cases this with
          | inl h =>
            cases ih c₃ hc₃ hc₁ h with
            | inl h' => apply h₁; rw [h']; exact Subset.refl _
            | inr h' => exact h₂ (Subset.trans h' (Set.SoSUnion.subset_of_mem hc₃))
          | inr h => exact h₁ (Subset.trans (succ_increasing r) h)

    theorem chain_closure_total (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂) : c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
      Or.imp_right (Subset.trans (succ_increasing r))
        (chain_closure_succ_total_aux r hc₁ hc₂ (fun hc₃ => chain_closure_succ_total r hc₃ hc₂))

    theorem chain_closure_succ_fixpoint (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂)
      (h_eq : succ_chain r c₂ = c₂) : c₁ ⊆ c₂ := by
        induction hc₁
        case succ c₁ hc₁ ih =>
          exact Or.elim (chain_closure_succ_total r hc₁ hc₂ ih)
            (fun h => by rw [←h, h_eq]; exact Subset.refl _) id
        case union s hs ih =>
          exact Set.SoSUnion.subset (fun c₁ hc₁ => ih c₁ hc₁)

    theorem chain_closure_succ_fixpoint_iff (hc : chain_closure r c) :
      succ_chain r c = c ↔ c = ⋃₀ chain_closure r :=
        ⟨fun h => Set.subset.antisymm
          (Set.SoSUnion.subset_of_mem hc)
          (chain_closure_succ_fixpoint r (chain_closure_closure r) hc h),
        fun (h : c = ⋃₀ {c : Set α | chain_closure r c}) => Set.subset.antisymm
          (by conv => rhs; rw [h]; exact Set.SoSUnion.subset_of_mem (chain_closure.succ hc))
          (succ_increasing r)⟩

    theorem chain_chain_closure (hc : chain_closure r c) : Chain r c := by
      induction hc
      case succ c hc ih => exact chain_succ r ih
      case union s hs ih =>
        exact fun c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq =>
          have : t₁ ⊆ t₂ ∨ t₂ ⊆ t₁ := chain_closure_total r (hs _ ht₁) (hs _ ht₂)
          Or.elim this
            (fun (h : t₁ ⊆ t₂) => ih t₂ ht₂ c₁ (h hc₁) c₂ hc₂ hneq)
            (fun (h : t₂ ⊆ t₁) => ih t₁ ht₁ c₁ hc₁ c₂ (h hc₂) hneq)

    /-- `max_chain` is the union of all sets in the chain closure. -/
    def max_chain : Set α := ⋃₀ chain_closure r

    /-- Hausdorff's maximality principle
    There exists a maximal totally ordered subset of `α`.
    Note that we do not require `α` to be partially ordered by `r`. -/
    theorem max_chain_spec : is_max_chain r (max_chain r) :=
      byContradiction fun h =>
        have ⟨_, h₁⟩ : super_chain r (⋃₀ chain_closure r) (succ_chain r (⋃₀ chain_closure r)) :=
          super_of_not_max r (chain_chain_closure r (chain_closure_closure r)) h
        have h₂ : succ_chain r (⋃₀ chain_closure r) = (⋃₀ chain_closure r) :=
          (chain_closure_succ_fixpoint_iff r (chain_closure_closure r)).mpr rfl
        Set.subset.proper_neq h₁ h₂.symm

    /-- Zorn's lemma
    If every chain has an upper bound, then there is a maximal element -/
    theorem exists_maximal_of_chains_bounded (h : ∀ c : Set α, Chain r c → ∃ ub : α, ∀ a ∈ c, a ≤ ub)
      (trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c) : ∃ m : α, ∀ a : α, m ≤ a → a ≤ m :=
        have ⟨ub, hub⟩ : ∃ ub : α, ∀ a ∈ max_chain r, a ≤ ub := h _ (max_chain_spec r).left;
        ⟨ub, fun a ha =>
          have : Chain r ((max_chain r).insert a) :=
            chain_insert r (max_chain_spec r).left (fun b hb _ => Or.inr (trans (hub b hb) ha))
          have : a ∈ (max_chain r) :=
            byContradiction (fun h : a ∉ (max_chain r) =>
            (max_chain_spec r).right ⟨(max_chain r).insert a, this, Set.subset.insert_neq h⟩)
          hub a this⟩

    theorem lemma_eq (h : ∀ c : Set α, Chain r c → ∃ ub : α, ∀ a ∈ c, a ≤ ub)
      (trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c) (antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b) :
        ∃ m : α, ∀ a : α, m ≤ a → a = m :=
          let ⟨m, hm⟩ := exists_maximal_of_chains_bounded r h trans
          ⟨m, fun a ha => antisymm (hm a ha) ha⟩

    theorem lemma_subset (h : ∀ c : Set (Set α), Chain Subset.subset c → ∃ ub : Set α, ∀ a ∈ c, a ⊆ ub) :
      ∃ m : Set α, ∀ a : Set α, m ⊆ a → a = m := lemma_eq Subset.subset h Subset.trans Set.subset.antisymm

  end Zorn
end M4R