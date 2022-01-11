import M4R.Set.Basic
import M4R.Set.Finite.Pairwise

import M4R.Function

namespace M4R

  inductive Perm : List α → List α → Prop
  | nil                           : Perm [] []
  | cons (x : α) {l₁ l₂ : List α} : Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
  | swap (x y : α) (l : List α)   : Perm (y::x::l) (x::y::l)
  | trans {l₁ l₂ l₃ : List α}     : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

  infix:50 " ~ " => Perm
  
  namespace Perm

    protected theorem refl : ∀ (x : List α), x ~ x
    | []      => Perm.nil
    | (x::xl) => (Perm.refl xl).cons x
    
    protected theorem symm {x y : List α} (h : x ~ y) : y ~ x := 
      @Perm.recOn α (fun (a b : List α) _ => b ~ a) x y h
        Perm.nil
        (fun x _ _ _ r₁ => r₁.cons x)
        (fun x y l => swap y x l)
        (fun _ _ p₂₁ p₃₂ => p₃₂.trans p₂₁)
    
    instance PermEquivalence : Equivalence (@Perm α) where
    refl  := Perm.refl
    symm  := Perm.symm
    trans := Perm.trans

    instance PermSetoid (α : Type _) : Setoid (List α) where
      r := Perm
      iseqv := PermEquivalence

    theorem subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ :=
      fun x => @Perm.recOn α (fun (a b : List α) _ => x ∈ a → x ∈ b) l₁ l₂ p id
          (fun y a b _ xab xya => Or.elim xya
            (fun exy => Or.inl exy)
            (fun xa => Or.inr (xab xa)))
          (fun y z a xzya => Or.elim xzya
              (fun exz => Or.inr (Or.inl exz))
              (fun xya => Or.elim xya
                  (fun exy => Or.inl exy)
                  (fun xa => Or.inr (Or.inr xa))))
          (fun _ _ x₁₂ x₂₃ x₁ => x₂₃ (x₁₂ x₁))

    theorem mem_iff {l₁ l₂ : List α} (p : l₁ ~ l₂) (a : α) : a ∈ l₁ ↔ a ∈ l₂ :=
      Iff.intro (fun x => p.subset x) (fun x => p.symm.subset x)
    
    theorem append_right {l₁ l₂ : List α} (t : List α) (p : l₁ ~ l₂) : l₁++t ~ l₂++t :=
      @Perm.recOn α (fun a b pab => a++t ~ b++t) _ _ p
        (Perm.refl ([] ++ t))
        (fun x _ _ _ r₁ => r₁.cons x)
        (fun x y _ => swap x y _)
        (fun _ _ r₁ r₂ => r₁.trans r₂)

    theorem append_left {t₁ t₂ : List α} (l : List α) (p : t₁ ~ t₂) : l++t₁ ~ l++t₂ :=
      match l with
      | [] => p
      | x::xs => (append_left xs p).cons x

    theorem append {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁++t₁ ~ l₂++t₂ :=
      (p₁.append_right t₁).trans (p₂.append_left l₂)

    theorem middle (a : α) : ∀ (l₁ l₂ : List α), l₁++a::l₂ ~ a::(l₁++l₂)
    | []     , l₂ => Perm.refl _
    | (b::l₁), l₂ => ((@middle α a l₁ l₂).cons b).trans (swap a b _)
    
    theorem append_singleton (a : α) (l : List α) : l ++ [a] ~ a::l := by
      have := middle a l []
      rw [List.append_nil] at this
      exact this

    theorem append_comm  (l₁ l₂ : List α) : (l₁++l₂) ~ (l₂++l₁) :=
      match l₁ with
      | []     => by simp; exact Perm.refl l₂
      | (a::t) => ((append_comm t l₂).cons a).trans (middle a l₂ t).symm

    theorem length_eq {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.length = l₂.length :=
      @Perm.recOn α (fun (a b : List α) _ => a.length = b.length) l₁ l₂ p rfl
        (fun _ _ _ _ h => by simp[h])
        (fun _ _ _ => by simp)
        (fun _ _ r₁₂ r₂₃ => Eq.trans r₁₂ r₂₃)

    theorem eq_nil {l : List α} (p : l ~ []) : l = [] :=
      List.eq_nil_of_length_eq_zero p.length_eq
    theorem nil_eq {l : List α} (p : [] ~ l) : l = [] :=
      eq_nil p.symm

    theorem inductionOn (motive : List α → List α → Prop) {l₁ l₂ : List α} (p : l₁ ~ l₂)
      (h₁ : motive [] [])
      (h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → motive l₁ l₂ → motive (x::l₁) (x::l₂))
      (h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → motive l₁ l₂ → motive (y::x::l₁) (x::y::l₂))
      (h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → motive l₁ l₂ → motive l₂ l₃ → motive l₁ l₃) : motive l₁ l₂ := by
        have P_refl : ∀ l, motive l l :=
          fun l => @List.recOn α (fun x => motive x x) l h₁ (fun x xs ih => h₂ x xs xs (Perm.refl xs) ih)
        exact Perm.recOn p h₁ h₂ (fun x y l => h₃ x y l l (Perm.refl l) (P_refl l)) (h₄ _ _ _)

    theorem invCore {a : α} {l₁ l₂ r₁ r₂ : List α} : l₁++a::r₁ ~ l₂++a::r₂ → l₁++r₁ ~ l₂++r₂ := by
      generalize e₁ : l₁++a::r₁ = s₁; generalize e₂ : l₂++a::r₂ = s₂;
      intro p; revert l₁ l₂ r₁ r₂ e₁ e₂;
      apply inductionOn (fun (t₁ t₂ : List α) => ∀ {l₁' l₂' r₁' r₂' : List α},
        l₁'++a::r₁' = t₁ → l₂'++a::r₂' = t₂ → l₁'++r₁' ~ l₂'++r₂') p
      { intro l₁ _ r₁ _ e₁ _
        have h₀ := List.notMemNil a; rw [←e₁] at h₀
        have : a ∈ l₁ ++ a :: r₁ := by apply (mem_iff (middle a l₁ r₁) _).mpr; apply Or.inl; rfl
        contradiction }
      { intro _ _ _ p₁₂ ih l₁ l₂ _ _ e₁ e₂;
        match l₁, l₂ with
        | [], [] =>
          simp at *; rw [e₁.right, e₂.right]; exact p₁₂
        | [], List.cons _ _ =>
          simp at *; rw [e₂.left, e₁.right, ←e₁.left]; apply trans p₁₂; rw [←e₂.right]; exact middle _ _ _
        | List.cons _ _, [] =>
          simp at *; rw [e₁.left, ←e₂.left, e₂.right]; apply Perm.symm; apply trans p₁₂.symm;
            rw [←e₁.right]; exact middle _ _ _
        | List.cons _ _, List.cons z l₂ =>
          simp at *; rw [e₁.left, e₂.left]; exact cons _ (ih e₁.right e₂.right) }
      { intro _ _ _ _ p₁₂ ih l₁ l₂ _ _ e₁ e₂
        match l₁, l₂ with
        | [], [] =>
          simp at *; rw [e₁.right, e₂.right, ←e₁.left, e₂.left]; exact Perm.cons _ p₁₂
        | [], List.cons _ l₂ =>
          match l₂ with
          | [] =>
            simp at *; rw [e₁.right, e₂.left, e₂.right.right]; exact Perm.cons _ p₁₂
          | List.cons _ _ =>
            simp at *; rw [e₁.right, e₂.left, e₂.right.left, ←e₁.left]; apply cons;
              apply trans p₁₂; rw [←e₂.right.right]; exact middle _ _ _
        | List.cons _ l₁, [] =>
          match l₁ with
          | [] =>
            simp at *; rw [e₁.right.right, e₂.right, e₁.left]; exact Perm.cons _ p₁₂
          | List.cons _ l₂ =>
            simp at *; rw [e₂.right, e₁.left, e₁.right.left, ←e₂.left]; apply cons;
              apply Perm.symm; apply trans p₁₂.symm; rw [←e₁.right.right]; exact middle _ _ _
        | List.cons _ l₁, List.cons _ l₂ =>
          match l₁, l₂ with
          | [], [] =>
            simp at *; rw [e₁.left, e₂.left, ←e₁.right.left, ←e₂.right.left, e₁.right.right, e₂.right.right]
              exact cons _ p₁₂
          | [], List.cons _ _ =>
            simp at *; rw [e₁.left, e₂.left, ←e₁.right.left, e₂.right.left, e₁.right.right];
              apply trans (cons _ p₁₂); rw [←e₂.right.right]; apply Perm.symm; apply trans (swap _ _ _);
                apply cons; apply Perm.symm; exact middle _ _ _
          | List.cons _ _, [] =>
            simp at *; rw [e₁.left, e₂.left, e₁.right.left, ←e₂.right.left]; apply trans (swap _ _ _); apply cons;
              rw [e₂.right.right]; apply Perm.symm; apply trans p₁₂.symm; rw [←e₁.right.right]; exact middle _ _ _
          | List.cons _ _, List.cons _ _ =>
            simp at *; rw [e₁.left, e₂.left, e₁.right.left, e₂.right.left]; apply trans (swap _ _ _); apply cons;
              apply cons; exact ih e₁.right.right e₂.right.right }
      { intro _ t₂ _ p₁₂ p₂₃ ih₁ ih₂ l₁ _ r₁ _ e₁ e₃;
          rw [←e₁] at p₁₂; rw [←e₃] at p₂₃;
          have : a ∈ t₂ := p₁₂.subset (by apply (mem_iff (middle a l₁ r₁) _).mpr; apply Or.inl; rfl)
          let ⟨l₂, r₂, e₂⟩ := List.mem_split this;
          exact trans (ih₁ e₁ e₂.symm) (ih₂ e₂.symm e₃) }

    theorem cons_inv {a : α} {l₁ l₂ : List α} : a::l₁ ~ a::l₂ → l₁ ~ l₂ :=
      @invCore _ _ [] [] _ _

    theorem pairwiseIff {r : α → α → Prop} (h : ∀ a b, r a b → r b a) :
      ∀ {l₁ l₂ : List α} (p : l₁ ~ l₂), Pairwise r l₁ ↔ Pairwise r l₂ := by
      have : ∀ {l₁ l₂}, l₁ ~ l₂ → Pairwise r l₁ → Pairwise r l₂ := by
        intro l₁ l₂ p₁₂ pwl₁;
        induction pwl₁ generalizing l₂ with
        | nil => rw [p₁₂.nil_eq]; constructor
        | @cons a l₃ hl₃ pwl₃ ih =>
          let ⟨s, t, e⟩ := List.mem_split (p₁₂.subset (List.mem_cons_self a l₃));
          rw [e, Pairwise.middle, Pairwise.consIff]; rw [e] at p₁₂;
          have p' : l₃ ~ s ++ t := (p₁₂.trans (middle _ _ _)).cons_inv;
          exact And.intro (fun x xst => hl₃ x ((mem_iff p' _).mpr xst)) (ih p')
          exact h
      exact fun _ _ p => ⟨this p, this p.symm⟩

    theorem nodupIff {l₁ l₂ : List α} : l₁ ~ l₂ → (l₁.nodup ↔ l₂.nodup) :=
      pairwiseIff (@Ne.symm α)

    theorem sizeOf_Eq_sizeOf {l₁ l₂ : List α} (h : l₁ ~ l₂) :
      sizeOf l₁ = sizeOf l₂ := by
      induction h with
      | nil => rfl
      | cons _ _ h => rw [List.sizeOf_cons, List.sizeOf_cons, h]
      | swap _ _ _ => rw [List.sizeOf_cons, List.sizeOf_cons, List.sizeOf_cons, List.sizeOf_cons]
      | trans _ _ h₁ h₂ => exact Eq.trans h₁ h₂

    theorem filterMap (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
      List.filterMap f l₁ ~ List.filterMap f l₂ := by
        induction p with
        | nil => simp only [List.filterMap]; exact Perm.nil
        | cons x p ih =>
          simp only [List.filterMap]
          cases f x with
          | none => exact ih
          | some a => exact cons a ih;
        | swap x y l =>
          simp only [List.filterMap]
          cases f x with
          | none =>
            cases f y with
            | none => exact Perm.refl _
            | some b => exact Perm.cons b (Perm.refl _)
          | some a =>
            cases f y with
            | none => exact Perm.refl _
            | some b => exact Perm.swap a b _
        | trans p₁₂ p₂₃ ih₁₂ ih₂₃ => exact ih₁₂.trans ih₂₃

    theorem map (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.map f ~ l₂.map f := by
      rw [←List.filterMap_Eq_map f]; exact filterMap (some ∘ f) p

    theorem exists_perm_sublist {l₁ l₂ l₂' : List α} (s : l₁ <+ l₂) (p : l₂ ~ l₂') :
      ∃ l₁', l₁' ~ l₁ ∧ l₁' <+ l₂' := by
        induction p generalizing l₁ with
        | nil => exact ⟨[], List.Sublist.eq_nil_of_sublist_nil s ▸ Perm.refl _, List.Sublist.nil_sublist _⟩
        | cons x p ih =>
          cases s with
          | cons _ _ _ s => let ⟨l, pl, hl⟩ := ih s; exact ⟨l, pl, hl.cons _ _ x⟩
          | cons' l₁ _ _ s => let ⟨l, pl, hl⟩ := ih s; exact ⟨x::l, pl.cons x, hl.cons' _ _ x⟩
        | swap x y l₂ =>
          cases s with
          | cons _ _ _ s =>
            cases s with
            | cons _ _ _ s => exact ⟨l₁, Perm.refl _, (s.cons _ _ y).cons _ _ x⟩
            | cons' l₁ _ _ s => exact ⟨x::l₁, Perm.refl _, (s.cons _ _ y).cons' _ _ x⟩
          | cons' l₁ _ _ s =>
            cases s with
            | cons _ _ _ s => exact ⟨y::l₁, Perm.refl _, (s.cons' _ _ y).cons _ _ x⟩
            | cons' l₁ _ _ s => exact ⟨x::y::l₁, Perm.swap _ _ _, (s.cons' _ _ y).cons' _ _ x⟩
        | trans p₁ p₂ ih₁ ih₂ => let ⟨l, pl, hl⟩ := ih₁ s; let ⟨m, pm, hm⟩ := ih₂ hl; exact ⟨m, pm.trans pl, hm⟩

    def Subperm (l₁ l₂ : List α) : Prop := ∃ l, l ~ l₁ ∧ l <+ l₂
    infix:50 " <+~ " => Subperm
  end Perm
end M4R

protected theorem List.Sublist.subperm {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁ <+~ l₂ :=
  ⟨l₁, M4R.Perm.refl _, s⟩

namespace M4R
  namespace Perm
    protected theorem subperm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ <+~ l₂ :=
      ⟨l₂, p.symm, List.Sublist.refl _⟩

    theorem subperm_left {l l₁ l₂ : List α} (p : l₁ ~ l₂) : l <+~ l₁ ↔ l <+~ l₂ := by
      have : ∀ {l₁ l₂ : List α}, l₁ ~ l₂ → l <+~ l₁ → l <+~ l₂ := fun p ⟨u, pu, su⟩ =>
        let ⟨v, pv, sv⟩ := exists_perm_sublist su p
        ⟨v, pv.trans pu, sv⟩
      exact ⟨this p, this p.symm⟩

    theorem subperm_right {l₁ l₂ l : List α} (p : l₁ ~ l₂) : l₁ <+~ l ↔ l₂ <+~ l :=
      ⟨fun ⟨u, pu, su⟩ => ⟨u, pu.trans p, su⟩,
        fun ⟨u, pu, su⟩ => ⟨u, pu.trans p.symm, su⟩⟩

    namespace Subperm
      theorem nil_subperm {l : List α} : [] <+~ l :=
        ⟨[], Perm.nil, by simp⟩

      protected theorem refl (l : List α) : l <+~ l := (Perm.refl _).subperm

      protected theorem trans {l₁ l₂ l₃ : List α} : l₁ <+~ l₂ → l₂ <+~ l₃ → l₁ <+~ l₃
      | s, ⟨l₂', p₂, s₂⟩ =>
        let ⟨l₁', p₁, s₁⟩ := p₂.subperm_left.mpr s
        ⟨l₁', p₁, s₁.trans s₂⟩

      theorem length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → l₁.length ≤ l₂.length
      | ⟨l, p, s⟩ => p.length_eq ▸ s.length_le_of_sublist

      theorem perm_of_length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → l₂.length ≤ l₁.length → l₁ ~ l₂
      | ⟨l, p, s⟩, h =>
        have := List.Sublist.eq_of_sublist_of_length_le s (p.symm.length_eq ▸ h)
        this ▸ p.symm

      theorem antisymm {l₁ l₂ : List α} (h₁ : l₁ <+~ l₂) (h₂ : l₂ <+~ l₁) : l₁ ~ l₂ :=
        h₁.perm_of_length_le h₂.length_le

      theorem cons_subperm_of_mem {a : α} {l₁ l₂ : List α} (d₁ : l₁.nodup) (h₁ : a ∉ l₁) (h₂ : a ∈ l₂)
        (s : l₁ <+~ l₂) : a :: l₁ <+~ l₂ := by
          let ⟨l, p, s⟩ := s
          induction s generalizing l₁ with
          | nil => cases h₂
          | cons r₁ r₂  b s' ih =>
            cases h₂ with
            | inl e => rw [e]; exact ⟨b::r₁, p.cons b, s'.cons' _ _ _⟩
            | inr m => let ⟨t, p', s'⟩ := ih d₁ h₁ m ⟨r₁, p, s'⟩ p; exact ⟨t, p', s'.cons _ _ _⟩
          | cons' r₁ r₂ b s' ih =>
            have bm : b ∈ l₁ := p.subset (List.mem_cons_self _ _)
            have am : a ∈ r₂ := h₂.resolve_left (fun e => h₁ (e.symm ▸ bm))
            cases List.mem_split bm with
            | intro t₁ t₂ =>
              let ⟨t₂, h⟩ := t₂; rw [h];
              have st : t₁ ++ t₂ <+ l₁ := by
                rw [h]; exact (List.Sublist.append_sublist_append_left t₁).mpr
                  (List.Sublist.cons t₂ t₂ b (List.Sublist.refl t₂))
              have rt : r₁ ~ t₁ ++ t₂ := cons_inv (p.trans (by rw [h]; exact Perm.middle _ _ _))
              let ⟨t, p', s'⟩ := ih (List.nodup_of_sublist st d₁) (fun h' => absurd (st.subset h') h₁) am
                ⟨r₁, rt, s'⟩ rt
              exact ⟨b::t, (p'.cons b).trans ((swap _ _ _).trans ((Perm.middle _ _ _).symm.cons a)), s'.cons' _ _ _⟩

      theorem subperm_of_subset_nodup {l₁ l₂ : List α} (d : l₁.nodup) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ := by
        induction d with
        | nil => exact ⟨[], Perm.nil, List.Sublist.nil_sublist _⟩
        | cons h d IH =>
          let ⟨H₁, H₂⟩ := List.forall_mem_cons.mp H
          exact cons_subperm_of_mem d (by intro h'; apply h _ h'; rfl) H₁ (IH H₂)

    end Subperm

    protected theorem ext {l₁ l₂ : List α} (d₁ : l₁.nodup) (d₂ : l₂.nodup) : l₁ ~ l₂ ↔ ∀a, a ∈ l₁ ↔ a ∈ l₂ :=
      ⟨fun p a => p.mem_iff _, fun H =>
        Subperm.antisymm
          (Subperm.subperm_of_subset_nodup d₁ (fun a => (H a).mp))
          (Subperm.subperm_of_subset_nodup d₂ (fun a => (H a).mpr))⟩

  end Perm
end M4R
