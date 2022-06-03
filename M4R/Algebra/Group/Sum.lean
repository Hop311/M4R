import M4R.Algebra.Group.Monoid
import M4R.Set

namespace M4R
  open Monoid CommMonoid

  def UnorderedList.fold_add [CommMonoid α] (init : α) (s : UnorderedList α) :=
    s.fold (· + ·) (fun x y z => add_right_comm x z y) init

  namespace UnorderedList.fold_add

    @[simp] theorem empty [CommMonoid α] (init : α) : UnorderedList.fold_add init ∅ = init := rfl

    theorem cons [CommMonoid α] (init a : α) (s : UnorderedList α) : (s.cons a).fold_add init = s.fold_add init + a :=
      UnorderedList.fold.cons' _ _ init a s

    theorem init_change [CommMonoid α] (init a : α) (s : UnorderedList α) : s.fold_add (init + a) = s.fold_add init + a := by
      have : (s.cons a).fold_add init = s.fold_add (init + a) :=
        UnorderedList.fold.cons _ _ init a s
      rw [←this, cons]

    theorem init_swap [CommMonoid α] (a b : α) (s : UnorderedList α) : s.fold_add a + b = s.fold_add b + a := by
      rw [←init_change, ←init_change, add_comm]

    theorem append [CommMonoid α] (init : α) (s t : UnorderedList α) : (s + t).fold_add init + init = s.fold_add init + t.fold_add init := by
      have : (s + t).fold_add init = t.fold_add (s.fold_add init) := by
        simp only [fold_add, fold.append];
      rw [this, init_swap, add_comm]

  end UnorderedList.fold_add

  def UnorderedList.map_fold_add [CommMonoid α] (init : α) (f : β → α) (s : UnorderedList β) : α :=
    s.map_fold (· + ·) add_comm add_assoc init f

  namespace UnorderedList.map_fold_add

    @[simp] theorem empty [CommMonoid α] (init : α) (f : β → α) : map_fold_add init f ∅ = init := rfl

    theorem cons [CommMonoid α] (init : α) (f : β → α) (b : β) (s : UnorderedList β) :
      (s.cons b).map_fold_add init f = s.map_fold_add init f + f b :=
        map_fold.cons (· + ·) add_comm add_assoc init f s b

    theorem distrib [CommMonoid α] (init : α) (f g : β → α) (s : UnorderedList β) :
      init + s.map_fold_add init (fun b => f b + g b) =
        (s.map_fold_add init f) + (s.map_fold_add init g) := by
          simp only [map_fold_add, map_fold.distrib]

    theorem congr_map [CommMonoid α] (init : α) {s : UnorderedList β} {f g : β → α} (h : ∀ x ∈ s, f x = g x) :
      s.map_fold_add init f = s.map_fold_add init g :=
        map_fold.congr_map (· + ·) add_comm add_assoc init h

    theorem append [CommMonoid α] (init : α) (s t : UnorderedList β) (f : β → α) :
      (s + t).map_fold_add init f + init = s.map_fold_add init f + t.map_fold_add init f := by
        have := fold_add.append init (s.map f) (t.map f)
        rw [←map.add] at this; exact this

  end UnorderedList.map_fold_add

  def UnorderedList.sum [CommMonoid α] (s : UnorderedList α) : α :=
    s.fold_add 0

  def UnorderedList.map_sum [CommMonoid β] (s : UnorderedList α) (f : α → β) : β :=
    s.map_fold_add 0 f

  namespace UnorderedList.sum

    @[simp] theorem empty [CommMonoid α] : (∑ (0 : UnorderedList α)) = 0 := rfl

    theorem cons [CommMonoid α] (a : α) (s : UnorderedList α) : (∑ s.cons a) = (∑ s) + a :=
      fold_add.cons 0 a s

    @[simp] theorem cons_zero [CommMonoid α] (s : UnorderedList α) : (∑ s.cons 0) = ∑ s :=
      add_zero (∑ s) ▸ cons 0 s

    @[simp] theorem singleton [CommMonoid α] (a : α) : (∑ UnorderedList.singleton a) = a := by
      conv => rhs rw [←zero_add a]

    @[simp] theorem double  [CommMonoid α] (a b : α) : (∑ ([a, b] : UnorderedList α)) = a + b := by
      have : ([a, b] : UnorderedList α) = (UnorderedList.singleton b).cons a := rfl
      rw [this, cons, singleton]; exact add_comm b a

    theorem eq_zero [CommMonoid α] {s : UnorderedList α} (h : ∀ x ∈ s, x = 0) : (∑ s) = 0 :=
      @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
        (∀ a ∈ l, a = 0) → (∑ l) = 0) s (fun l hl => by
          induction l with
          | nil => rfl
          | cons x l ih =>
            rw [UnorderedList.cons', cons, hl x (by rw [UnorderedList.cons']; exact UnorderedList.mem_cons_self _ _), add_zero]
            exact ih (fun a ha => hl a (UnorderedList.mem_cons_of_mem ha)))
        h

    theorem eq_empty [CommMonoid α] {s : UnorderedList α} (h : s = 0) : (∑ s) = 0 := h ▸ empty

    theorem append [CommMonoid α] (s t : UnorderedList α) : (∑ s + t) = (∑ s) + (∑ t) := by
      have := fold_add.append 0 s t
      rw [add_zero] at this
      exact this

    theorem prop_sum [CommMonoid α] (p : α → Prop) (s : UnorderedList α) (h₀ : p 0)
      (h₁ : ∀ a ∈ s, p a) (h₂ : ∀ a₁ a₂, p a₁ → p a₂ → p (a₁ + a₂)) :
        p (∑ s) :=
          UnorderedList.induction_on (fun l => l ⊆ s → p (∑ l)) s (fun _ => h₀)
            (fun a l hl hla => by
              rw [cons]; exact h₂ _ _ (hl fun x hx => hla (mem_cons.mpr (Or.inr hx)))
                (h₁ _ (hla (mem_cons.mpr (Or.inl rfl))))) (Subset.refl _)

  end UnorderedList.sum
  namespace UnorderedList.map_sum

    @[simp] theorem map_def [CommMonoid β] (f : α → β) (s : UnorderedList α) : (∑ s.map f) = ∑ f in s := rfl

    @[simp] theorem empty [CommMonoid β] (f : α → β) : (∑ f in (0 : UnorderedList α)) = 0 := rfl

    @[simp] theorem map_id [CommMonoid α] (s : UnorderedList α) : (∑ id in s) = ∑ s := by
      simp only [map_sum, map_fold_add, map_fold, UnorderedList.map.map_id s] rfl

    theorem cons [CommMonoid β] (f : α → β) (a : α) (s : UnorderedList α) : (∑ f in s.cons a) = (∑ f in s) + (f a) :=
      map_fold_add.cons 0 f a s

    theorem congr [CommMonoid β] {f g : α → β} {s₁ s₂ : UnorderedList α} (h : s₁ = s₂) :
      (∀ x ∈ s₂, f x = g x) → (∑ f in s₁) = ∑ g in s₂ := by
        rw [h]; exact UnorderedList.map_fold_add.congr_map 0

    @[simp] theorem singleton [CommMonoid β] (f : α → β) (a : α) : (∑ f in UnorderedList.singleton a) = f a := by
      simp only [map_sum, map_fold_add, map_fold, map.singleton f a, fold.singleton, zero_add]

    @[simp] theorem double  [CommMonoid β] (f : α → β) (a b : α) : (∑ f in ([a, b] : UnorderedList α)) = f a + f b :=
      (sum.double (f a) (f b)).symm ▸ rfl

    theorem eq_zero [CommMonoid β] {f : α → β} {s : UnorderedList α} (h : ∀ x ∈ s, f x = 0) :
      (∑ f in s) = 0 :=
        UnorderedList.sum.eq_zero fun x hx =>
          let ⟨a, ha, he⟩ := UnorderedList.map.mem_map.mp hx
          he.symm.trans (h a ha)

    theorem eq_empty [CommMonoid β] (f : α → β) {s : UnorderedList α} (h : s = 0) : (∑ f in s) = 0 := h ▸ empty f

    theorem append [CommMonoid β] (f : α → β) (s t : UnorderedList α) : (∑ f in s + t) = (∑ f in s) + (∑ f in t) := by
      have := map_fold_add.append 0 s t f; rw [add_zero] at this; exact this

    theorem distrib [CommMonoid β] (f g : α → β) (s : UnorderedList α) :
      (∑ x in s, f x + g x) = (∑ f in s) + ∑ g in s := by
        have := map_fold_add.distrib 0 f g s
        rw [zero_add] at this
        simp only [map_sum, this]

    theorem comm [CommMonoid γ] {s : UnorderedList α} {t : UnorderedList β} {f : α → β → γ} :
      (∑ x in s, ∑ y in t, f x y) = (∑ y in t, ∑ x in s, f x y) :=
        UnorderedList.induction_on (fun l => (∑ x in l, ∑ y in t, f x y) = (∑ y in t, ∑ x in l, f x y)) s
          (by simp only [empty]; exact (eq_zero (fun _ _ => rfl)).symm)
          (fun a l ih => by
            simp at ih ⊢
            have : (fun y => map_sum (UnorderedList.cons a l) (f · y)) =
              (fun y => (map_sum l (f · y)) + f a y) := by simp only [cons]
            rw [cons, this, distrib, ih])

    theorem map [CommMonoid γ] (s : UnorderedList α) (e : α → β) (f : β → γ) :
      (∑ f in s.map e) = ∑ f ∘ e in s := by
        simp only [map_sum, map_fold_add, map_fold, UnorderedList.map.map_comp]

    theorem prop_sum [CommMonoid β] (p : β → Prop) (f : α → β) (s : UnorderedList α) (h₀ : p 0)
      (h₁ : ∀ a ∈ s, p (f a)) (h₂ : ∀ b₁ b₂, p b₁ → p b₂ → p (b₁ + b₂)) :
        p (∑ f in s) :=
          UnorderedList.sum.prop_sum _ _ h₀ (fun b hb =>
            let ⟨a, has, hab⟩ := map.mem_map.mp hb
            hab ▸ h₁ a has) h₂

  end UnorderedList.map_sum

  def Finset.sum [CommMonoid α] (s : Finset α) : α := s.elems.sum
  def Finset.map_sum [CommMonoid β] (s : Finset α) (f : α → β) : β := s.elems.map_sum f

  namespace Finset.sum

    @[simp] theorem empty [CommMonoid α] : (∑ (∅ : Finset α)) = 0 := rfl

    theorem cons [CommMonoid α] {a : α} {s : Finset α} (ha : a ∉ s) : (∑ s.cons a ha) = (∑ s) + a :=
      UnorderedList.sum.cons a s.elems

    theorem eq_zero [CommMonoid α] {s : Finset α} (h : ∀ x ∈ s, x = 0) : (∑ s) = 0 :=
      UnorderedList.sum.eq_zero h

    theorem eq_empty [CommMonoid α] {s : Finset α} (h : s = ∅) : (∑ s) = 0 := h ▸ empty

    @[simp] theorem singleton [CommMonoid α] (a : α) : (∑ Finset.singleton a) = a :=
      UnorderedList.sum.singleton a

    @[simp] theorem sum_insert [CommMonoid α] {a : α} {s : Finset α} : a ∉ s → (∑ insert a s) = a + ∑ s := by
      rw [add_comm]; exact fold.fold_insert (· + ·) (fun x y z => add_right_comm x z y) 0

    theorem prop_sum [CommMonoid α] (p : α → Prop) (s : Finset α) (h₀ : p 0)
      (h₁ : ∀ a ∈ s, p a) (h₂ : ∀ a₁ a₂, p a₁ → p a₂ → p (a₁ + a₂)) :
        p (∑ s) := UnorderedList.sum.prop_sum p s h₀ h₁ h₂

  end Finset.sum

  namespace Finset.map_sum

    @[simp] theorem map_def [CommMonoid β] (f : α → β) (s : Finset α) : (∑ s.map f) = ∑ f in s := rfl

    @[simp] theorem empty [CommMonoid β] (f : α → β) : (∑ f in (∅ : Finset α)) = 0 := rfl

    @[simp] theorem map_id [CommMonoid α] (s : Finset α) : (∑ id in s) = ∑ s :=
      UnorderedList.map_sum.map_id s.elems

    theorem cons [CommMonoid β] (f : α → β) {a : α} {s : Finset α} (ha : a ∉ s) : (∑ f in s.cons a ha) = (∑ f in s) + (f a) :=
      UnorderedList.map_sum.cons f a s.elems

    theorem eq_zero [CommMonoid β] {f : α → β} {s : Finset α} (h : ∀ x ∈ s, f x = 0) :
      (∑ f in s) = 0 :=
        UnorderedList.map_sum.eq_zero h

    theorem eq_empty [CommMonoid β] (f : α → β) {s : Finset α} (h : s = ∅) : (∑ f in s) = 0 := h ▸ empty f

    @[simp] theorem singleton [CommMonoid β] (f : α → β) (a : α) : (∑ f in Finset.singleton a) = f a :=
      UnorderedList.map_sum.singleton f a

    theorem distrib [CommMonoid β] (f g : α → β) (s : Finset α) :
      (∑ x in s, f x + g x) = (∑ f in s) + ∑ g in s := by
        exact UnorderedList.map_sum.distrib f g s

    theorem congr [CommMonoid β] {f g : α → β} {s₁ s₂ : Finset α} (h : s₁ = s₂) :
      (∀ x ∈ s₂, f x = g x) → (∑ f in s₁) = ∑ g in s₂ :=
        UnorderedList.map_sum.congr (val_inj.mpr h)

    theorem union_inter [CommMonoid β] {f : α → β} {s₁ s₂ : Finset α} :
      (∑ f in (s₁ ∪ s₂)) + (∑ f in (s₁ ∩ s₂)) = (∑ f in s₁) + (∑ f in s₂) :=
        Finset.map_fold.union_inter (· + ·) add_comm add_assoc f

    theorem union [CommMonoid β] {f : α → β} {s₁ s₂ : Finset α} (h : disjoint s₁ s₂) :
      (∑ f in (s₁ ∪ s₂)) = (∑ f in s₁) + (∑ f in s₂) := by
        rw [←union_inter, h, empty, add_zero]

    theorem sdiff [CommMonoid β] {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) {f : α → β} :
      (∑ f in (s₂ ∖ s₁)) + (∑ f in s₁) = (∑ f in s₂) := by
        rw [←union (((s₂ ∖ s₁).inter_comm s₁).trans (s₁.inter_sdiff_self s₂)), sdiff_union_of_subset h]

    theorem subset_zero_on_sdiff [CommMonoid β] {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) {f g : α → β}
      (hg : ∀ x ∈ (s₂ ∖ s₁), g x = 0) (hfg : ∀ x ∈ s₁, f x = g x) : (∑ f in s₁) = ∑ g in s₂ := by
        rw [←sdiff h, eq_zero hg, zero_add]
        exact congr rfl hfg

    theorem subset [CommMonoid β] {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) {f : α → β} (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 0) :
      (∑ f in s₁) = ∑ f in s₂ :=
        subset_zero_on_sdiff h (by simp only [mem_sdiff, and_imp]; exact hf) (fun _ _ => rfl)

    @[simp] theorem sum_insert [CommMonoid β] (f : α → β) {a : α} {s : Finset α} :
      a ∉ s → (∑ f in insert a s) = f a + ∑ f in s :=
        map_fold.fold_insert (· + ·) add_comm add_assoc 0 f

    theorem comm [CommMonoid γ] {s : Finset α} {t : Finset β} {f : α → β → γ} :
      (∑ x in s, ∑ y in t, f x y) = (∑ y in t, ∑ x in s, f x y) :=
        UnorderedList.map_sum.comm

    theorem map [CommMonoid γ] (s : Finset α) {e : α → β} (he : Function.injective e) (f : β → γ) :
      (∑ f in s.map_inj he) = ∑ f ∘ e in s :=
        UnorderedList.map_sum.map s.elems e f

    theorem antidiagonal_eq_range [CommMonoid α] (f : Nat × Nat → α) (n : Nat) :
      (∑ f in Finset.antidiagonal n) = ∑ k in Finset.range n.succ, f (k, n-k) := by
        have : Finset.antidiagonal n = (Finset.range n.succ).map_inj (fun _ _ h => by
          rw [Prod.mk.injEq] at h; exact h.left) := rfl
        rw [this, map_sum.map]

    theorem range'_start [CommMonoid α] (f : Nat → α) (s n : Nat) :
      (∑ f in Finset.range' s n.succ) = f s + ∑ f in Finset.range' s.succ n := by
        rw [Finset.range'.start, cons, add_comm]

    theorem range'_succ [CommMonoid α] (f : Nat → α) (s n : Nat) :
      (∑ f in Finset.range' s n.succ) = (∑ f in Finset.range' s n) + f (s+n) := by
        rw [Finset.range'.succ, cons]

    theorem range_start [CommMonoid α] (f : Nat → α) (n : Nat) :
      (∑ f in Finset.range n.succ) = f 0 + ∑ f in Finset.range' 1 n := by
        rw [Finset.range.start, cons, add_comm]

    theorem range_succ [CommMonoid α] (f : Nat → α) (n : Nat) :
      (∑ f in Finset.range n.succ) = (∑ f in Finset.range n) + f n := by
        rw [Finset.range.succ, cons]

    theorem range'_shift [CommMonoid α] (f : Nat → α) (s n : Nat) :
      (∑ f in Finset.range' s n) = ∑ f ∘ Nat.pred in Finset.range' s.succ n := by
        induction n with
        | zero => rw [Finset.range'.zero, Finset.range'.zero, empty, empty]
        | succ n ih =>
          rw [range'_succ, ih, range'_succ, Nat.succ_add]
          simp only [Function.comp, Nat.pred_succ]

    theorem range_shift [CommMonoid α] (f : Nat → α) (n : Nat) :
      (∑ f in Finset.range n) = ∑ f ∘ Nat.pred in Finset.range' 1 n := by
        rw [range_eq_range']; exact range'_shift f 0 n

    theorem range'_split [CommMonoid α] {f : Nat → α} {s n : Nat} (m : Nat) (h : m ≤ n) :
      (∑ f in Finset.range' s n) = (∑ f in Finset.range' s m) + (∑ f in Finset.range' (s + m) (n - m)) := by
        have := Finset.range'.append s m (n - m)
        rw [Nat.add_comm m, Nat.sub_add_cancel h] at this
        rw [←this, union ((Finset.range'.disjoint _ _ _ _).mpr (Or.inl (Nat.le_refl _)))]

    theorem prop_sum [CommMonoid β] (p : β → Prop) (f : α → β) (s : Finset α) (h₀ : p 0)
      (h₁ : ∀ a ∈ s, p (f a)) (h₂ : ∀ b₁ b₂, p b₁ → p b₂ → p (b₁ + b₂)) :
        p (∑ f in s) := UnorderedList.map_sum.prop_sum p f s h₀ h₁ h₂

    theorem sum_term [CommMonoid β] (f : α → β) (s : Finset α) {a : α} (ha : a ∈ s) : (∑ f in s) = (∑ f in s.erase a) + f a := by
      conv => lhs rw [s.erase_cons ha, cons]

  end Finset.map_sum
  namespace UnorderedList
    theorem sum_mem {l : UnorderedList (UnorderedList α)} {a : α} : a ∈ (∑ l) ↔ ∃ l' ∈ l, a ∈ l' :=
      ⟨fun ha => Classical.byContradiction fun h => by
        simp only [not_exists, not_and] at h
        exact absurd ha (sum.prop_sum (a ∉ ·) l (by intro; contradiction) h
          (fun s t hs ht hst => absurd (append.mem_add.mp hst) (not_or_iff_and_not.mpr ⟨hs, ht⟩))),
      fun ⟨l', hl', ha⟩ => by rw [←erase.cons_erase hl', sum.cons]; exact append.mem_add.mpr (Or.inr ha)⟩

    theorem sum_cons {s : UnorderedList α} (f₁ : α → UnorderedList β) (f₂ : α → β) : (∑ x in s, (f₁ x).cons (f₂ x)) = (∑ f₁ in s) + s.map f₂ :=
      UnorderedList.induction_on (fun s => (∑ x in s, (f₁ x).cons (f₂ x)) = (∑ f₁ in s) + s.map f₂) s
        (by simp only [UnorderedList.map_sum.empty, UnorderedList.map_nil, add_zero])
        (fun a s ih => by
          simp only [UnorderedList.map_sum.cons, ih, UnorderedList.map.cons, UnorderedList.append.cons_over_right]
          rw [add_right_comm])

    theorem sum_distrib [CommMonoid γ] (s₁ : UnorderedList α) (s₂ : α → UnorderedList β) (f : β → γ) :
      (∑ x in s₁, ∑ y in s₂ x, f y) = ∑ y in ∑ x in s₁, s₂ x, f y :=
        UnorderedList.induction_on (fun s₁ => (∑ x in s₁, ∑ y in s₂ x, f y) = ∑ y in ∑ x in s₁, s₂ x, f y) s₁
          (by simp only [map_sum.empty])
          (fun _ _ ih => by simp only [map_sum.cons, ih, map_sum.append])

    theorem sum_disjoint {l : UnorderedList (UnorderedList α)} {s : UnorderedList α} (h : ∀ l' ∈ l, disjoint l' s) : disjoint (∑ l) s :=
      fun x hxl hxs => let ⟨l', hl', hxl'⟩ := sum_mem.mp hxl; absurd hxs (h l' hl' x hxl')

    theorem sum_nodup {l : UnorderedList (UnorderedList α)} (hl : l.nodup) (hnodup : ∀ s ∈ l, s.nodup) (hdisjoint : ∀ s ∈ l, ∀ t ∈ l, s ≠ t → disjoint s t) :
      (∑ l).nodup :=
        let f : Finset (UnorderedList α) := ⟨l, hl⟩
        @Finset.cons_induction _ (fun f' => f' ⊆ f → (∑ f').nodup)
          (fun _ => by rw [Finset.sum.empty]; exact nodup_zero α)
          (fun s f' hs ih hf' => Finset.sum.cons hs ▸ append.nodup_add.mpr ⟨ih fun x hx => hf' (Finset.mem_cons_self' hs hx),
            hnodup s (hf' (Finset.mem_cons_self f' hs)), sum_disjoint (fun l' hl' => hdisjoint l' (hf' (Finset.mem_cons_self' hs hl')) s
              (hf' (Finset.mem_cons_self f' hs)) (fun hls => hs (hls ▸ hl')))⟩) f (Subset.refl _)

    def product (l₁ : UnorderedList α) (l₂ : UnorderedList β) : UnorderedList (α × β) := ∑ a in l₁, l₂.map (Prod.mk a)

    namespace product
      theorem mem {l₁ : UnorderedList α} {l₂ : UnorderedList β} : ∀ {x : α × β}, x ∈ l₁.product l₂ ↔ x.fst ∈ l₁ ∧ x.snd ∈ l₂ := by
        intro ⟨x₁, x₂⟩; exact ⟨fun h => by
          let ⟨s, hs, hx⟩ := sum_mem.mp h
          let ⟨t, ht, hts⟩ := map.mem_map.mp hs
          rw [←hts] at hx
          let ⟨r, hr, hrx⟩ := map.mem_map.mp hx
          exact hrx ▸ ⟨ht, hr⟩,
        fun ⟨h₁, h₂⟩ => sum_mem.mpr ⟨l₂.map (Prod.mk x₁), map.mem_map.mpr ⟨x₁, h₁, rfl⟩, map.mem_map.mpr ⟨x₂, h₂, rfl⟩⟩⟩

      theorem empty_left (α : Type _) (l : UnorderedList β) : (0 : UnorderedList α).product l = 0 := by
        simp only [product, map_sum.empty]

      theorem empty_right (l : UnorderedList α) (β : Type _) : l.product (0 : UnorderedList β) = 0 := by
        simp only [product, map_nil]; exact map_sum.eq_zero (fun _ _ => rfl)

      theorem cons_left (l₁ : UnorderedList α) (l₂ : UnorderedList β) (a : α) : (l₁.cons a).product l₂ = l₁.product l₂ + l₂.map (Prod.mk a) := by
        simp only [product, map_sum.cons]

      theorem cons_right (l₁ : UnorderedList α) (l₂ : UnorderedList β) (b : β) : l₁.product (l₂.cons b) = l₁.product l₂ + l₁.map (Prod.mk · b) := by
        simp only [product, UnorderedList.map_sum.congr rfl (fun a _ => UnorderedList.map.cons (Prod.mk a) b l₂), sum_cons]

      theorem nodup {l₁ : UnorderedList α} {l₂ : UnorderedList β} (h₁ : l₁.nodup) (h₂ : l₂.nodup) : (l₁.product l₂).nodup := by
        byCases h : l₂ = 0
        { rw [h, empty_right]; exact nodup_zero _ }
        { exact sum_nodup (nodup_map (fun x y h' =>
            let ⟨z, hz⟩ : ∃ x, x ∈ l₂ := Classical.byContradiction fun h' => h (subset_zero fun x hx => absurd hx (not_exists.mp h' x))
            let ⟨w, hw, he⟩ := map.mem_map.mp (h' ▸ map.mem_map.mpr ⟨z, hz, rfl⟩ : (x, z) ∈ l₂.map (Prod.mk y))
            (Prod.mk.inj he.symm).left) h₁) (fun s hs => let ⟨t, ht, he⟩ := map.mem_map.mp hs; he ▸ nodup_map (fun _ _ h => (Prod.mk.inj h).right) h₂)
            (fun s hs t ht hst => fun x hxs hxt => hst (by
              let ⟨_, _, hse⟩ := map.mem_map.mp hs; let ⟨_, _, hte⟩ := map.mem_map.mp ht
              rw [←hse, ←hte]; rw [←hse] at hxs; rw [←hte] at hxt
              let ⟨_, _, hse⟩ := map.mem_map.mp hxs; let ⟨_, _, hte⟩ := map.mem_map.mp hxt
              rw [(Prod.mk.inj (hse.trans hte.symm)).left])) }
    end product
  end UnorderedList

  theorem Finset.sum_distrib [CommMonoid γ] (s₁ : Finset α) (s₂ : α → Finset β) (f : β → γ) :
    (∑ x in s₁, ∑ y in s₂ x, f y) = ∑ y in ∑ x in s₁, (s₂ x).elems, f y :=
      UnorderedList.sum_distrib s₁.elems (fun x => (s₂ x).elems) f

end M4R
