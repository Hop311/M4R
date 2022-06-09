import M4R.Set.MemStructure

namespace List
  open M4R

  protected def mem (a : α) : List α → Prop
  | []   => False
  | b::l => a = b ∨ List.mem a l

  instance ListMem : M4R.Mem α (List α) where mem := List.mem

  protected def sizeOf : List α → Nat := lengthTR
  instance ListSizeOf : SizeOf (List α) where sizeOf := List.sizeOf

  @[simp] theorem sizeOf_cons (a : α) (as : List α) : sizeOf (a::as) = (sizeOf as).succ := by
    simp only [sizeOf, List.sizeOf]; rw [←length_eq_lenghtTR, length_cons]

  theorem eq_nil_of_length_eq_zero {l : List α} : l.length = 0 → l = [] := by
    induction l with
    | nil  => intros; rfl
    | cons => intros; contradiction

  theorem length_eq_one {l : List α} : length l = 1 ↔ ∃ a, l = [a] :=
    ⟨by match l with
    | nil => intro; contradiction
    | cons a l =>
      intro h
      simp at h
      rw [eq_nil_of_length_eq_zero h]
      exact ⟨a, rfl⟩,
    fun ⟨a, e⟩ => e.symm ▸ rfl⟩

  theorem cons_ext {a b : α} {s t : List α} : a :: s = b :: t ↔ a = b ∧ s = t :=
    ⟨List.cons.inj, fun ⟨h₁, h₂⟩ => congr (congrArg List.cons h₁) h₂⟩

  @[simp] theorem mem_nil_iff (a : α) : a ∈ ([] : List α) ↔ False :=
    Iff.rfl
  @[simp] theorem not_mem_nil (a : α) : a ∉ ([] : List α) :=
    Iff.mp (mem_nil_iff a)

  theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l :=
    Or.inl rfl

  @[simp] theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l :=
    Or.inr

  @[simp] theorem eq_or_mem_of_mem_cons {a y : α} {l : List α} : a ∈ y::l → a = y ∨ a ∈ l := by
    simp only [Mem.mem, List.mem]; exact id

  theorem mem_cons_iff {a b : α} {l : List α} : a ∈ b :: l ↔ a = b ∨ a ∈ l :=
    ⟨eq_or_mem_of_mem_cons, fun h =>
      Or.elim h (fun h' => by rw [h']; exact mem_cons_self b l) (mem_cons_of_mem b)⟩

  theorem length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l
  | b::l, _ => Nat.zero_lt_succ _

  theorem exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l
  | b::l, _ => ⟨b, mem_cons_self _ _⟩

  theorem length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l :=
    ⟨exists_mem_of_length_pos, fun ⟨a, h⟩ => length_pos_of_mem h⟩

  theorem forall_mem_nil (p : α → Prop) : ∀ x ∈ [], p x := fun _ _ => by contradiction

  theorem forall_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
      ⟨fun h => ⟨h a (mem_cons_self a l), fun x xl => h x (mem_cons_of_mem a xl)⟩, fun ⟨h₁, h₂⟩ x hx => by
        cases hx with
        | inl h => rw [h]; exact h₁
        | inr h => exact h₂ x h⟩

  theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α}
    (h : ∀ x ∈ a :: l, p x) : ∀ x ∈ l, p x :=
      (forall_mem_cons.mp h).right

  @[simp] theorem forall_mem_ne {a : α} {l : List α} : (∀ (a' : α), a' ∈ l → ¬a = a') ↔ a ∉ l :=
    ⟨fun h m => h _ m rfl, fun h a' m e => h (e.symm ▸ m)⟩

  theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l :=
    fun h₁ h₂ h₃ => Or.elim (eq_or_mem_of_mem_cons h₃) h₁ h₂

  theorem mem_split {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t := by
    induction l with
    | nil         => contradiction
    | cons b l ih => apply Or.elim h (fun ab =>
      by rw [ab]; exact ⟨[], l, rfl⟩) (fun ainl =>
        by let ⟨s, t, p⟩ := ih ainl; rw [p]; exact ⟨b::s, t, rfl⟩)

  theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
    Or.elim (eq_or_mem_of_mem_cons h₂) (fun e => absurd e h₁) id

  theorem eq_nil_of_subset_nil : ∀ {l : List α}, l ⊆ [] → l = []
  | []  , s => rfl
  | a::l, s => False.elim (s (mem_cons_self a l))

  protected theorem in_singleton {a a' : α} : a' ∈ [a] → a' = a := by
    intro ha'
    simp only [Mem.mem, List.mem, or_false] at ha'
    exact ha'

  protected theorem self_singleton (a : α) : a ∈ [a] := by
    simp only [Mem.mem, List.mem]

  @[simp] theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
      induction s with
      | nil => simp
      | cons _ _ ih => exact
        ⟨fun p => Or.elim p (fun x => Or.inl (Or.inl x)) (fun x => Or.assoc.mp (Or.inr (ih.mp x))),
          fun p => Or.elim p (fun q => Or.elim q Or.inl
            (fun x => Or.inr (ih.mpr (Or.inl x)))) (fun x => Or.inr (ih.mpr (Or.inr x)))⟩

  @[simp] theorem appendSingleton {a : α} {l : List α} : [a] ++ l = a::l := rfl

  protected theorem in_double (a b : α) : ∀ x ∈ [a, b], x = a ∨ x = b := fun x hx =>
    Or.elim (eq_or_mem_of_mem_cons hx) Or.inl fun hb => Or.inr (List.in_singleton hb)

  section map

    @[simp] theorem map_nil (f : α → β) : map f [] = [] := rfl

    @[simp] theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = (map f l₁) ++ (map f l₂) := fun l₁ => by
      induction l₁ with
      | nil => intros; rfl
      | cons x l₁ ih => simp only [map, cons_append, cons_ext]; exact fun l₂ => ⟨trivial, ih l₂⟩

    theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] := rfl

    theorem mem_map_of_mem (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ l.map f := by
      induction l with
      | nil => cases h
      | cons _ _ ih =>
        cases h with
        | inl h' => rw [h']; apply Or.inl; rfl
        | inr h' => exact Or.inr (ih h')

    theorem exists_of_mem_map {f : α → β} {b : β} {l : List α} (h : b ∈ l.map f) :
      ∃ a, a ∈ l ∧ f a = b := by
      induction l with
      | nil => cases h
      | cons c _ ih =>
        cases (eq_or_mem_of_mem_cons h) with
        | inl h' => exact ⟨c, mem_cons_self _ _, h'.symm⟩
        | inr h' => let ⟨a, ha₁, ha₂⟩ := ih h'; exact ⟨a, mem_cons_of_mem _ ha₁, ha₂⟩

    @[simp] theorem mem_map {f : α → β} {b : β} {l : List α} : b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b :=
      ⟨exists_of_mem_map, fun ⟨a, la, h⟩ => by rw [←h]; exact mem_map_of_mem f la⟩

    @[simp] theorem map_cons (f : α → β) (a : α) (l : List α) : (a :: l).map f = (f a) :: (l.map f) := rfl

    @[simp] theorem map_comp (f : α → β) (g : β → γ) (l : List α) : (l.map f).map g = l.map (g ∘ f) := by
      induction l with
      | nil => rfl
      | cons a l ih => simp only [map_cons, ih]

    @[simp] theorem map_id (l : List α) : map id l = l := by
      induction l with
      | nil => rfl
      | cons a b ih => simp only [map, id_eq, ih]

    theorem filterMap_Eq_map (f : α → β) : filterMap (some ∘ f) = map f := by
      apply funext; intro l
      induction l with
      | nil => simp only [filterMap, map]
      | cons _ _ ih => simp only [filterMap, map, cons.injEq, true_and]; exact ih

    theorem map_congr {f g : α → β} {s t : List α} (h₁ : s = t) (h₂ : ∀ x ∈ t, f x = g x) :
      s.map f = t.map g := by
        rw [h₁]; clear h₁
        induction t with
        | nil => rfl
        | cons a l ih₂ =>
          simp only [List.map_cons, List.cons_ext]
          exact ⟨h₂ a (List.mem_cons_self a l), ih₂ fun x hx => h₂ x (mem_cons_of_mem a hx)⟩

    @[simp] theorem length_map (f : α → β) (l : List α) : (l.map f).length = l.length := by
      induction l with
      | nil => rfl
      | cons a b ih => rw [map_cons, length_cons, length_cons, ih]
  end map

  inductive Sublist : List α → List α → Prop
  | nil : Sublist [] []
  | cons (l₁ l₂ a) : Sublist l₁ l₂ → Sublist l₁ (a::l₂)
  | cons' (l₁ l₂ a) : Sublist l₁ l₂ → Sublist (a::l₁) (a::l₂)
  infix:50 " <+ " => Sublist

  namespace Sublist

    theorem length_le_of_sublist {l₁ l₂ : List α} : l₁ <+ l₂ → length l₁ ≤ length l₂
    | nil => Nat.le_refl 0
    | cons l₁ l₂ a s => Nat.le_succ_of_le (length_le_of_sublist s)
    | cons' l₁ l₂ a s => Nat.succ_le_succ (length_le_of_sublist s)

    @[simp] theorem nil_sublist : ∀ (l : List α), [] <+ l
    | []     => nil
    | a :: l => cons _ _ a (nil_sublist l)

    @[simp] protected theorem refl : ∀ (l : List α), l <+ l
    | []       => nil
    | (a :: l) => cons' _ _ a (Sublist.refl l)

    protected theorem trans {l₁ l₂ l₃ : List α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ :=
      @Sublist.recOn α (fun l₂ l₃ h => (l₁ : List α) → l₁ <+ l₂ → l₁ <+ l₃) _ _ h₂
        (fun _ => id)
        (fun l₂ l₃ a h₂ IH l₁ h₁ => cons _ _ _ (IH l₁ h₁))
        (fun l₂ l₃ a h₂ IH l₁ h₁ =>
          @Sublist.casesOn α (fun l₁ l₂' _ => l₂' = a :: l₂ → l₁ <+ a :: l₃) _ _ h₁
            (fun _ => nil_sublist _)
            (fun l₁ l₂' a' h₁' e => by rw [(List.cons_ext.mp e).right] at h₁'; exact cons _ _ _ (IH _ h₁'))
            (fun l₁ l₂' a' h₁' e => by
              have ⟨e₁, e₂⟩ := List.cons_ext.mp e; rw [e₁]; rw [e₂] at h₁'
              exact cons' _ _ _ (IH _ h₁')) rfl)
        l₁ h₁

    @[simp] theorem sublist_cons (a : α) (l : List α) : l <+ a::l :=
      cons _ _ _ (Sublist.refl l)

    theorem sublist_of_cons_sublist {a : α} {l₁ l₂ : List α} : a::l₁ <+ l₂ → l₁ <+ l₂ :=
      Sublist.trans (sublist_cons a l₁)

    protected theorem cons_cons {l₁ l₂ : List α} (a : α) (s : l₁ <+ l₂) : a::l₁ <+ a::l₂ :=
      cons' _ _ _ s

    @[simp] theorem sublist_append_left : ∀ (l₁ l₂ : List α), l₁ <+ l₁++l₂
    | []   , l₂ => nil_sublist _
    | a::l₁, l₂ => (sublist_append_left l₁ l₂).cons_cons _

    @[simp] theorem sublist_append_right : ∀ (l₁ l₂ : List α), l₂ <+ l₁++l₂
    | []   , l₂ => Sublist.refl _
    | a::l₁, l₂ => cons _ _ _ (sublist_append_right l₁ l₂)

    theorem sublist_cons_of_sublist (a : α) {l₁ l₂ : List α} : l₁ <+ l₂ → l₁ <+ a::l₂ :=
      cons _ _ _

    theorem sublist_append_of_sublist_left {l l₁ l₂ : List α} (s : l <+ l₁) : l <+ l₁++l₂ :=
      s.trans $ sublist_append_left _ _

    theorem sublist_append_of_sublist_right {l l₁ l₂ : List α} (s : l <+ l₂) : l <+ l₁++l₂ :=
      s.trans (sublist_append_right _ _)

    theorem sublist_of_cons_sublist_cons {l₁ l₂ : List α} {a : α} : a::l₁ <+ a::l₂ → l₁ <+ l₂ := fun h => by
      cases h with
      | cons _ _ _ h => exact sublist_of_cons_sublist h
      | cons' _ _ _ h => exact h

    theorem cons_sublist_cons_iff {l₁ l₂ : List α} {a : α} : a::l₁ <+ a::l₂ ↔ l₁ <+ l₂ :=
    ⟨sublist_of_cons_sublist_cons, Sublist.cons_cons _⟩

    @[simp] theorem append_sublist_append_left {l₁ l₂ : List α} : ∀ l, l++l₁ <+ l++l₂ ↔ l₁ <+ l₂
    | []   => Iff.rfl
    | a::l => cons_sublist_cons_iff.trans (append_sublist_append_left l)

    theorem append_right {l₁ l₂ : List α} (h : l₁ <+ l₂) (l : List α) : l₁++l <+ l₂++l := by
      induction h with
      | nil => simp only [nil_append]; exact Sublist.refl l
      | cons l₁ l₂ a s ih => exact sublist_cons_of_sublist a ih
      | cons' l₁ l₂ a s ih => exact ih.cons_cons a

    protected theorem reverse {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.reverse <+ l₂.reverse := by
      induction h with
      | nil => simp only [List.reverse_nil]; exact Sublist.refl _
      | cons l₁ l₂ a s ih => rw [reverse_cons]; exact sublist_append_of_sublist_left ih
      | cons' l₁ l₂ a s ih => rw [reverse_cons, reverse_cons]; exact ih.append_right [a]

    @[simp] theorem reverse_sublist_iff {l₁ l₂ : List α} : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
      ⟨fun h => l₁.reverse_reverse ▸ l₂.reverse_reverse ▸ h.reverse, Sublist.reverse⟩

    @[simp] theorem append_sublist_append_right {l₁ l₂ : List α} : ∀ l, l₁++l <+ l₂++l ↔ l₁ <+ l₂ := fun l =>
      ⟨fun h => by
        have := h.reverse
        rw [reverse_append, reverse_append, append_sublist_append_left] at this
        exact reverse_sublist_iff.mp this,
      fun h => h.append_right l⟩

    protected theorem subset {l₁ l₂ : List α} : l₁ <+ l₂ → l₁ ⊆ l₂
    | nil, b, h => h
    | cons l₁ l₂ a s, b, h => mem_cons_of_mem _ (Sublist.subset s h)
    | cons' l₁ l₂ a s, b, h => by
      cases eq_or_mem_of_mem_cons h with
      | inl h => exact h ▸ mem_cons_self _ _
      | inr h => exact mem_cons_of_mem _ (Sublist.subset s h)

    @[simp] theorem singleton_sublist {a : α} {l : List α} : [a] <+ l ↔ a ∈ l :=
      ⟨fun h => h.subset (List.self_singleton _),
      fun h => by
        let ⟨s, t, e⟩ := mem_split h; rw [e]
        exact ((Sublist.nil_sublist t).cons_cons a).trans (Sublist.sublist_append_right s (a::t))⟩

    theorem eq_nil_of_sublist_nil {l : List α} (s : l <+ []) : l = [] :=
      eq_nil_of_subset_nil s.subset

    theorem eq_of_sublist_of_length_eq {l₁ l₂ : List α} : l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
    | nil, h => rfl
    | cons l₁ l₂ a s, h => absurd (length_le_of_sublist s) $ Nat.not_le_of_gt (by rw [h]; apply Nat.lt_succ_self)
    | cons' l₁ l₂ a s, h => by simp at h; rw [eq_of_sublist_of_length_eq s h]

    theorem eq_of_sublist_of_length_le {l₁ l₂ : List α} (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) :
      l₁ = l₂ :=
        eq_of_sublist_of_length_eq s (Nat.le_antisymm (length_le_of_sublist s) h)

    theorem sublist_or_mem_of_sublist {l l₁ l₂ : List α} {a : α} (h : l <+ l₁ ++ a::l₂) :
      l <+ l₁ ++ l₂ ∨ a ∈ l := by
        induction l₁ generalizing l with
        | nil =>
          cases h with
          | cons  _ _ _ h => apply Or.inl; simp only [nil_append, h]
          | cons' _ _ _ _ => apply Or.inr; exact mem_cons_self _ _
        | cons b l₁ ih =>
          cases h with
          | cons  _ _ _ h => exact Or.imp_left (sublist_cons_of_sublist _) (ih h)
          | cons' _ _ _ h =>
            exact (ih h).imp (Sublist.cons_cons _) (mem_cons_of_mem _)

    theorem filter_map (f : α → Option β) {l₁ l₂ : List α}
      (s : l₁ <+ l₂) : filterMap f l₁ <+ filterMap f l₂ := by
        induction s with
        | nil => simp
        | cons l₁ l₂ a s ih =>
          simp only [filterMap]
          cases f a with
          | none => exact ih
          | some b => exact Sublist.cons _ _ b ih
        | cons' l₁ l₂ a s ih =>
          simp only [filterMap]
          cases f a with
          | none => exact ih
          | some b => exact Sublist.cons' _ _ b ih

  end Sublist

  section pmap

    @[simp] def pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
    | []  , H => []
    | a::l, H => f a (forall_mem_cons.mp H).left :: pmap f l (forall_mem_cons.mp H).right

    @[simp] theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
      @pmap _ _ p (fun a _ => f a) l H = map f l := by
        induction l with
        | nil => rfl
        | cons _ _ ih => simp only [pmap, map, ih]

    theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
      (h : ∀ a h₁ h₂, f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
        induction l with
        | nil => rfl
        | cons _ _ ih => simp only [pmap, cons.injEq]; exact ⟨h _ _ _, ih⟩

    theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β)
      (l H) : map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
        induction l with
        | nil => rfl
        | cons _ _ ih => simp only [pmap, map, ih]

    section attach
      def attach (l : List α) : List {x // x ∈ l} := pmap Subtype.mk l (fun _ => id)

      theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
        pmap f l H = l.attach.map (fun ⟨x, hx⟩ => f x (H _ hx)) := by
          simp only [attach, map_pmap]; exact pmap_congr l (fun a h₁ h₂ => rfl)

      theorem attach_map_val (l : List α) : l.attach.map Subtype.val = l := by
        simp only [attach, map_pmap]; exact (pmap_eq_map _ _ _ _).trans (map_id l)

      @[simp] theorem mem_attach (l : List α) : ∀ x, x ∈ l.attach
      | ⟨a, h⟩ => by
        have := mem_map.mp (by rw [attach_map_val]; exact h)
        cases this with
        | intro x h' => match x, h' with
          | ⟨x, hx⟩, ⟨h₁, h₂⟩ =>
            have : ({ val := a, property := h } : Subtype (· ∈ l)) = { val := x, property := hx } := by
              simp only [Subtype.mk.injEq, h₂]
            rw [this]
            exact h₁
    end attach

    @[simp] theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
      b ∈ pmap f l H ↔ ∃ (a : α) (h : a ∈ l), f a (H a h) = b := by
        simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, Subtype.exists]
        exact Iff.refl _

    theorem pmap_length {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (hl : ∀ a ∈ l, p a) : (l.pmap f hl).length = l.length := by
      induction l with
      | nil          => rfl
      | cons a l ih => rw [length_cons, ←ih (fun x hx => hl x (mem_cons_of_mem a hx))]; rfl
  end pmap

  open Classical

  section insert
    protected noncomputable def insert (a : α) (l : List α) : List α :=
      if a ∈ l then l else a :: l

    @[simp] theorem insert_nil (a : α) : ([]).insert a = [a] := by simp only [List.insert, mem_nil_iff, ite_false]

    @[simp] theorem insert_of_mem {a : α} {l : List α} (h : a ∈ l) : l.insert a = l := by
      simp only [List.insert, if_pos h]

    @[simp] theorem insert_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.insert a = a :: l :=
      by simp only [List.insert, if_neg h]

    @[simp] theorem mem_insert_iff {l : List α} : a ∈ l.insert b ↔ a = b ∨ a ∈ l := by
      byCases h : b ∈ l
      { rw [insert_of_mem h]; exact ⟨Or.inr, fun h' => Or.elim h' (fun h'' => by rw [h'']; exact h) id⟩ }
      simp only [insert_of_not_mem h, mem_cons_iff]; exact Iff.refl _

    theorem Sublist.insert (a : α) (l : List α) : l <+ l.insert a := by
      byCases h : a ∈ l
      simp only [List.insert, h, ite_true, Sublist.refl]
      simp only [List.insert, h, ite_false, Sublist.sublist_cons]

  end insert

  section fold

    @[simp] theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : List β) :
    foldl f a (b::l) = foldl f (f a b) l := rfl

    @[simp] theorem foldr_cons (f : α → β → β) (init : β) (a : α) (l : List α) :
      foldr f init (a::l) = f a (foldr f init l) := rfl

    @[simp] theorem foldl_append (f : α → β → α) (a : α) (l₁ l₂ : List β) :
      foldl f a (l₁++l₂) = foldl f (foldl f a l₁) l₂ :=
        match l₁ with
        | []      => rfl
        | b::l₁ => by simp only [cons_append, foldl_cons, foldl_append f (f a b) l₁ l₂]

    @[simp] theorem foldl_empty (f : α → β → α) (a : α) :
      foldl f a [] = a := rfl

    @[simp] theorem foldr_empty (f : α → β → β) (a : β) :
      foldr f a [] = a := rfl

    @[simp] theorem foldl_singleton (f : α → β → α) (a : α) (b : β) :
      foldl f a [b] = f a b := rfl

  end fold

  section union

    protected noncomputable def union (l₁ l₂ : List α) : List α :=
      foldr List.insert l₂ l₁

    noncomputable instance ListUnion : Union (List α) where union := List.union

    @[simp] theorem nil_union (l : List α) : [] ∪ l = l := rfl

    @[simp] theorem cons_union (l₁ l₂ : List α) (a : α) : a :: l₁ ∪ l₂ = (l₁ ∪ l₂).insert a := rfl

    @[simp] theorem mem_union {l₁ l₂ : List α} : a ∈ l₁ ∪ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ := by
      induction l₁ with
      | nil => simp
      | cons x l ih =>
        simp only [cons_union, mem_insert_iff, mem_cons_iff, ih, Or.assoc]; exact Iff.refl _

    theorem sublist_suffix_of_union : ∀ l₁ l₂ : List α, ∃ t, t <+ l₁ ∧ t ++ l₂ = l₁ ∪ l₂
    | []   , l₂ => ⟨[], Sublist.refl _, rfl⟩
    | a::l₁, l₂ =>
      let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂
      if h : a ∈ l₁ ∪ l₂ then
        ⟨t, Sublist.sublist_cons_of_sublist _ s, by simp only [e, cons_union, insert_of_mem h]⟩
      else
        ⟨a::t, s.cons_cons _, by simp only [cons_append, cons_union, e, insert_of_not_mem h]⟩

    theorem union_sublist_append (l₁ l₂ : List α) : l₁ ∪ l₂ <+ l₁ ++ l₂ :=
      let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂
      e ▸ (Sublist.append_sublist_append_right _).mpr s

  end union

  section filter'
    noncomputable def filter' (p : α → Prop) : List α → List α
    | []     => []
    | (a::l) => if p a then a :: filter' p l else filter' p l

    @[simp] theorem filter'_nil (p : α → Prop) : filter' p [] = [] := rfl

    @[simp] theorem filter'_cons_of_pos {a : α} (l: List α) (h : p a) : filter' p (a :: l) = a :: filter' p l :=
      if_pos h

    @[simp] theorem filter'_cons_of_neg {a : α} (s) (h : ¬ p a) : filter' p (a :: s) = filter' p s :=
      if_neg h

    @[simp] theorem filter'_append {p : α → Prop} :
      ∀ (l₁ l₂ : List α), filter' p (l₁++l₂) = filter' p l₁ ++ filter' p l₂
    | []   , l₂ => rfl
    | a::l₁, l₂ => by
      byCases pa : p a; repeat { simp [pa, filter'_append] }

    theorem filter_map_eq_filter' (p : α → Prop) : filterMap (Option.guard p) = filter' p := by
      apply funext; intro l
      induction l with
      | nil => rfl
      | cons a l ih =>
        byCases pa : p a
        { simp only [filterMap, Option.guard, if_pos pa, filter'_cons_of_pos _ pa]
          exact cons_ext.mpr ⟨rfl, ih⟩ }
        { simp only [filterMap, Option.guard, if_neg pa, filter'_cons_of_neg _ pa]
          exact ih }

    @[simp] theorem filter'_sublist {p : α → Prop} : ∀ (l : List α), filter' p l <+ l
    | []   => Sublist.nil
    | a::l =>
      if pa : p a then by
        simp only [filter'_cons_of_pos, pa]; apply Sublist.cons'; exact filter'_sublist l
      else by
        simp only [filter'_cons_of_neg, pa]; apply Sublist.cons; exact filter'_sublist l

    @[simp] theorem filter'_subset (p : α → Prop) (l : List α) : filter' p l ⊆ l :=
      (filter'_sublist l).subset

    theorem of_mem_filter' {p : α → Prop} {a : α} : ∀ {l : List α}, a ∈ filter' p l → p a
    | b::l, ain =>
      if pb : p b then
        have : a ∈ b :: filter' p l := by simp only [filter'_cons_of_pos _ pb] at ain; exact ain
        Or.elim (eq_or_mem_of_mem_cons this)
          (fun h => by rw [←h] at pb; exact pb)
          of_mem_filter'
      else by
        simp only [filter'_cons_of_neg _ pb] at ain; exact of_mem_filter' ain

    theorem mem_of_mem_filter' {p : α → Prop} {a : α} {l} (h : a ∈ filter' p l) : a ∈ l :=
      filter'_subset p l h

    theorem mem_filter'_of_mem {p : α → Prop} {a : α} : ∀ {l}, a ∈ l → p a → a ∈ filter' p l
    | _::l, Or.inl rfl, pa => by rw [filter'_cons_of_pos _ pa]; exact mem_cons_self _ _
    | b::l, Or.inr ain, pa =>
      if pb : p b then by
        rw [filter'_cons_of_pos _ pb]; exact mem_cons_of_mem _ (mem_filter'_of_mem ain pa)
      else by
        rw [filter'_cons_of_neg _ pb]; exact mem_filter'_of_mem ain pa

    @[simp] theorem mem_filter' {p : α → Prop} {a : α} {l : List α} : a ∈ filter' p l ↔ a ∈ l ∧ p a :=
      ⟨fun h => ⟨mem_of_mem_filter' h, of_mem_filter' h⟩, fun ⟨h₁, h₂⟩ => mem_filter'_of_mem h₁ h₂⟩

    theorem filter'_eq_self {l : List α} : filter' p l = l ↔ ∀ a ∈ l, p a := by
      induction l with
      | nil => simp only [filter'_nil, true_iff]; exact forall_mem_nil p
      | cons a l ih =>
        rw [forall_mem_cons]; byCases h : p a
        { rw [filter'_cons_of_pos _ h, List.cons.injEq, ih]
          exact ⟨fun h' => ⟨h, h'.right⟩, fun h' => ⟨rfl, h'.right⟩⟩ }
        { rw [filter'_cons_of_neg _ h]
          exact iff_of_false (by
            intro e; have := @filter'_sublist α p l
            rw [e] at this
            have h' := Nat.lt_succ_self (length l)
            have h'' := Sublist.length_le_of_sublist this
            simp only [length] at h''
            exact absurd (Nat.lt_of_lt_of_le h' h'') (Nat.lt_irrefl _)) (mt And.left h) }

  end filter'

  theorem Sublist.filter' (p : α → Prop) {l₁ l₂ : List α} (s : l₁ <+ l₂) : filter' p l₁ <+ filter' p l₂ :=
    filter_map_eq_filter' p ▸ s.filter_map _

  section erasep

    protected def erasep (p : α → Prop) [DecidablePred p] : List α → List α
    | []   => []
    | a::l => if p a then l else a :: List.erasep p l

    variable {p : α → Prop} [DecidablePred p]

    @[simp] theorem erasep_nil : [].erasep p = [] := rfl

    theorem erasep_cons (a : α) (l : List α) :
      (a :: l).erasep p = if p a then l else a :: l.erasep p := rfl

    @[simp] theorem erasep_cons_of_pos {a : α} {l : List α} (h : p a) : (a :: l).erasep p = l := by
      simp only [erasep_cons, h, ite_true]

    @[simp] theorem erasep_cons_of_neg {a : α} {l : List α} (h : ¬ p a) :
      (a::l).erasep p = a :: l.erasep p := by
        simp only [erasep_cons, h, ite_false]

    theorem erasep_of_forall_not {l : List α}
      (h : ∀ a ∈ l, ¬ p a) : l.erasep p = l := by
        induction l with
        | nil => rfl
        | cons _ _ ih =>
          simp only [h _ (Or.inl rfl), ih (forall_mem_of_forall_mem_cons h), erasep_cons_of_neg]

    theorem exists_of_erasep {l : List α} {a} (al : a ∈ l) (pa : p a) :
      ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ := by
        induction l with
        | nil => cases al
        | cons b l ih =>
          byCases pb : p b
          { exact ⟨b, [], l, forall_mem_nil _, pb, by simp only [pb, nil_append, erasep_cons_of_pos]⟩ }
          cases al with
          | inl h => rw [h] at pa; exact absurd pa pb
          | inr h =>
            let ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ := ih h
            exact ⟨c, b::l₁, l₂, forall_mem_cons.mpr ⟨pb, h₁⟩, h₂, by rw [h₃]; rfl, by
              simp only [pb, h₄, erasep_cons_of_neg, cons_append]⟩

    theorem exists_or_eq_self_of_erasep (p : α → Prop) [DecidablePred p] (l : List α) :
      l.erasep p = l ∨ ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ := by
        byCases h : ∃ a ∈ l, p a
        { let ⟨a, ha, pa⟩ := h; exact Or.inr (exists_of_erasep ha pa) }
        { simp only [not_exists, not_and] at h; exact Or.inl (erasep_of_forall_not h) }

    theorem erasep_append_left {a : α} (pa : p a) :
      ∀ {l₁ : List α} (l₂ : List α), a ∈ l₁ → (l₁++l₂).erasep p = l₁.erasep p ++ l₂
    | x::xs, l₂, h => by
      byCases h' : p x
      { simp only [h', erasep_cons_of_pos, cons_append] }
      simp only [h', erasep_cons_of_neg, cons_append, cons.injEq, true_and]
      rw [erasep_append_left pa l₂ (mem_of_ne_of_mem (mt _ h') h)]
      intro h; rw [h] at pa; exact pa

    theorem erasep_append_right :
      ∀ {l₁ : List α} (l₂ : List α), (∀ b ∈ l₁, ¬ p b) → (l₁++l₂).erasep p = l₁ ++ l₂.erasep p
    | []   , l₂, h => rfl
    | x::xs, l₂, h => by
      simp only [(forall_mem_cons.mp h).left, erasep_append_right _ (forall_mem_cons.mp h).right,
        erasep_cons_of_neg, cons_append]

    theorem erasep_sublist (l : List α) : l.erasep p <+ l := by
      cases exists_or_eq_self_of_erasep p l with
      | inl h => rw [h]; exact Sublist.refl _
      | inr h =>
        let ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ := h
        rw [h₄, h₃]; simp

    theorem erasep_subset (l : List α) : l.erasep p ⊆ l :=
      (erasep_sublist l).subset

    theorem mem_of_mem_erasep {a : α} {l : List α} : a ∈ l.erasep p → a ∈ l :=
      @erasep_subset _ _ _ _ _

    @[simp] theorem mem_erasep_of_neg {a : α} {l : List α} (pa : ¬ p a) : a ∈ l.erasep p ↔ a ∈ l :=
      ⟨mem_of_mem_erasep, fun al => by
        cases exists_or_eq_self_of_erasep p l with
        | inl h => rw [h]; exact al
        | inr h =>
          let ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ := h
          rw [h₄]; rw [h₃] at al
          apply List.mem_append.mpr
          cases List.mem_append.mp al with
          | inl h' => exact Or.inl h'
          | inr h' =>
            cases h' with
            | inl h' =>
              have : a ≠ c := fun h' => by rw [h'] at pa; exact absurd h₂ pa
              exact absurd h' this
            | inr h' => exact Or.inr h'⟩

  end erasep

  theorem Sublist.erasep {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁.erasep p <+ l₂.erasep p := by
      induction s with
      | nil => rw [erasep_nil]; exact Sublist.nil
      | cons l₁ l₂ a s ih =>
        byCases h : p a
        { rw [erasep_cons_of_pos h]; exact ih.trans (erasep_sublist _) }
        { rw [erasep_cons_of_neg h]; exact ih.cons _ _ _ }
      | cons' l₁ l₂ a s ih =>
        byCases h : p a
        { rw [erasep_cons_of_pos h, erasep_cons_of_pos h]; exact s }
        { rw [erasep_cons_of_neg h, erasep_cons_of_neg h]; exact ih.cons' _ _ _ }

  section erase
    @[simp] theorem erase_nil (a : α) : [].erase a = [] := rfl

    theorem erase_cons (a b : α) (l : List α) :
      (b :: l).erase a = (if b = a then l else b :: List.erase l a) := by
        byCases h₁ : b = a
        { have h₂ : a == a := decide_eq_true rfl
        simp only [h₁, List.erase, h₂, ite_true] }
        { have h₂ : (b == a) = false := decide_eq_false h₁
        simp only [h₁, List.erase, h₂, ite_false] }

    @[simp] theorem erase_cons_head (a : α) (l : List α) : (a :: l).erase a = l := by
      simp only [erase_cons, ite_true]

    @[simp] theorem erase_cons_tail {a b : α} (l : List α) (h : b ≠ a) :
      (b::l).erase a = b :: l.erase a := by
        simp only [erase_cons, if_neg h]

    theorem erase_eq_erasep (a : α) (l : List α) : l.erase a = l.erasep (Eq a) := by
      induction l with
      | nil => rfl
      | cons b l ih =>
        byCases h : a = b
        { simp only [h, erase_cons_head, erasep_cons_of_pos] }
        { simp only [ne_eq, h, Ne.symm h, ih, erase_cons_tail, erasep_cons_of_neg] }

    @[simp] theorem erase_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.erase a = l := by
      rw [erase_eq_erasep, erasep_of_forall_not]
      intro b h' h''; rw [h''] at h; exact absurd h' h

    theorem exists_erase_eq {a : α} {l : List α} (h : a ∈ l) :
      ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ := by
        let ⟨_, l₁, l₂, h₁, rfl, h₂, h₃⟩ := exists_of_erasep h rfl
        rw [erase_eq_erasep]; exact ⟨l₁, l₂, fun h => h₁ _ h rfl, h₂, h₃⟩

    theorem erase_append_left {a : α} {l₁ : List α} (l₂) (h : a ∈ l₁) :
      (l₁++l₂).erase a = l₁.erase a ++ l₂ := by
        simp only [erase_eq_erasep]; exact erasep_append_left (by rfl) l₂ h

    theorem erase_append_right {a : α} {l₁ : List α} (l₂) (h : a ∉ l₁) :
      (l₁++l₂).erase a = l₁ ++ l₂.erase a := by
        rw [erase_eq_erasep, erase_eq_erasep, erasep_append_right]
        intro b h' h''; rw [h''] at h; exact absurd h' h

    theorem erase_sublist (a : α) (l : List α) : l.erase a <+ l := by
      rw [erase_eq_erasep]; apply erasep_sublist

    theorem erase_subset (a : α) (l : List α) : l.erase a ⊆ l :=
      (erase_sublist a l).subset

    theorem mem_of_mem_erase {a b : α} {l : List α} : a ∈ l.erase b → a ∈ l :=
      have := erase_subset b l
      @this a

    @[simp] theorem mem_erase_of_ne {a b : α} {l : List α} (ab : a ≠ b) : a ∈ l.erase b ↔ a ∈ l := by
      rw [erase_eq_erasep]; exact mem_erasep_of_neg ab.symm

    theorem erase_comm (a b : α) (l : List α) : (l.erase a).erase b = (l.erase b).erase a :=
    if ab : a = b then by rw [ab] else
    if ha : a ∈ l then
    if hb : b ∈ l then match l, l.erase a, exists_erase_eq ha, hb with
    | _, _, ⟨l₁, l₂, ha', rfl, rfl⟩, hb =>
      if h₁ : b ∈ l₁ then
        by rw [erase_append_left _ h₁, erase_append_left _ h₁,
              erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
      else
        by rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
              erase_cons_tail _ ab, erase_cons_head]
    else by simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
    else by simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]

  end erase

  theorem Sublist.erase (a : α) {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a := by
      simp [erase_eq_erasep]; exact Sublist.erasep h

  section diff
    protected noncomputable def diff : List α → List α → List α
    | l , []    => l
    | l₁, a::l₂ => if a ∈ l₁ then List.diff (l₁.erase a) l₂ else List.diff l₁ l₂

    @[simp] theorem diff_nil (l : List α) : l.diff [] = l := rfl

    @[simp] theorem diff_cons (l₁ l₂ : List α) (a : α) : l₁.diff (a::l₂) = (l₁.erase a).diff l₂ :=
      if h : a ∈ l₁ then by simp only [List.diff, if_pos h]
      else by simp only [List.diff, if_neg h, erase_of_not_mem h]

    theorem diff_cons_right (l₁ l₂ : List α) (a : α) : l₁.diff (a::l₂) = (l₁.diff l₂).erase a := by
      induction l₂ generalizing l₁ with
      | nil => simp
      | cons b l₂ ih =>
        rw [diff_cons, diff_cons, erase_comm, ←diff_cons, ih, ←diff_cons]

    theorem diff_erase (l₁ l₂ : List α) (a : α) : (l₁.diff l₂).erase a = (l₁.erase a).diff l₂ := by
      rw [←diff_cons_right, diff_cons]

    @[simp] theorem nil_diff (l : List α) : [].diff l = [] := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [diff_cons, erase_of_not_mem (not_mem_nil _), ih]

  end diff

  @[simp] def repeat (a : α) : Nat → List α
  | 0          => []
  | Nat.succ n => a :: repeat a n

  namespace repeat

    @[simp] theorem length_append (s t : List α) : length (s ++ t) = length s + length t := by
      induction s with
      | nil => simp only [nil_append, length_nil, Nat.zero_add]
      | cons a s ih => simp [Nat.succ_add]

    @[simp] theorem length_repeat (a : α) (n : Nat) : length (repeat a n) = n := by
      induction n with
      | zero => rfl
      | succ n ih => simp [ih]

    @[simp] theorem repeat_sublist_repeat (a : α) {m n} : repeat a m <+ repeat a n ↔ m ≤ n :=
      ⟨fun h => by
        rw [←length_repeat a m, ←length_repeat a n]
        exact Sublist.length_le_of_sublist h,
      fun h => by
        induction h with
        | refl => exact Sublist.refl _
        | step k ih => simp; exact Sublist.cons _ _ a ih⟩

    @[simp] theorem repeat_succ (a : α) (n) : repeat a (n + 1) = a :: repeat a n := rfl

    theorem mem_repeat {a b : α} : ∀ {n : Nat}, b ∈ repeat a n ↔ n ≠ 0 ∧ b = a
    | 0     => by simp
    | n + 1 => by
      simp [mem_repeat, Nat.succ_ne_zero, List.mem_cons_iff]
      exact ⟨fun h => by
        cases h with
        | inl h => exact h
        | inr h => exact h.right,
        Or.inl⟩

    theorem eq_of_mem_repeat {a b : α} {n} (h :  b ∈ repeat a n) : b = a :=
      (mem_repeat.mp h).right

    theorem eq_repeat_of_mem {a : α} : ∀ {l : List α}, (∀ b ∈ l, b = a) → l = repeat a l.length
    | []  , _ => rfl
    | b::l, h => by
      have ⟨h₁, h₂⟩ := forall_mem_cons.mp h
      simp only [length, repeat, cons.injEq]; exact ⟨h₁, eq_repeat_of_mem h₂⟩

    theorem eq_repeat' {a : α} {l : List α} : l = repeat a l.length ↔ ∀ b ∈ l, b = a :=
      ⟨fun h => h.symm ▸ fun b => eq_of_mem_repeat, eq_repeat_of_mem⟩

    theorem eq_repeat {a : α} {n} {l : List α} : l = repeat a n ↔ length l = n ∧ ∀ b ∈ l, b = a :=
      ⟨fun h => h.symm ▸ ⟨length_repeat _ _, fun b => eq_of_mem_repeat⟩,
      fun ⟨e, al⟩ => e ▸ eq_repeat_of_mem al⟩

    theorem repeat_add (a : α) (m n) : repeat a (m + n) = repeat a m ++ repeat a n := by
      induction m with
      | zero   => simp
      | succ m ih => simp [Nat.succ_add, ih]

    theorem repeat_subset_singleton (a : α) (n) : repeat a n ⊆ [a] := fun b h => by
      rw [eq_of_mem_repeat h]; exact List.self_singleton a

  end repeat

  def countp (p : α → Prop) [DecidablePred p] : List α → Nat
  | []    => 0
  | x::xs => if p x then Nat.succ (countp p xs) else countp p xs

  section countp
    variable (p : α → Prop)

    @[simp] theorem countp_nil : countp p [] = 0 := rfl

    @[simp] theorem countp_cons_of_pos {a : α} (l : List α) (pa : p a) : countp p (a::l) = countp p l + 1 :=
      if_pos pa

    @[simp] theorem countp_cons_of_neg {a : α} (l : List α) (pa : ¬ p a) : countp p (a::l) = countp p l :=
      if_neg pa

    theorem countp_eq_length_filter' (l : List α) : countp p l = length (filter' p l) := by
      induction l with
      | nil => rfl
      | cons x l ih =>
        byCases h : p x
        simp only [filter'_cons_of_pos _ h, countp, ih, if_pos h, length]
        simp only [countp_cons_of_neg _ _ h, ih, filter'_cons_of_neg _ h]

    theorem countp_pos {l : List α} : 0 < countp p l ↔ ∃ a ∈ l, p a := by
      rw [countp_eq_length_filter', length_pos_iff_exists_mem]
      simp only [mem_filter']; exact Iff.rfl

  end countp

  theorem Sublist.countp_le {l₁ l₂ : List α} (s : l₁ <+ l₂) : countp p l₁ ≤ countp p l₂ := by
    simp only [countp_eq_length_filter']
    exact length_le_of_sublist (@Sublist.filter' _ p _ _ s)

  def count [DecidableEq α] (a : α) : List α → Nat := countp (Eq a)

  theorem Sublist.count_le {l₁ l₂ : List α} (h : l₁ <+ l₂) (a : α) : count a l₁ ≤ count a l₂ :=
    @Sublist.countp_le α (Eq a) _ _ h

  namespace count

    @[simp] theorem count_nil (a : α) : count a [] = 0 := rfl

    @[simp] theorem count_cons_of_pos (a : α) (l : List α) : count a (a::l) = count a l + 1 :=
      countp_cons_of_pos _ l rfl

    @[simp] theorem count_cons_of_neg {a b : α} (h : a ≠ b) (l : List α) : count a (b::l) = count a l :=
      countp_cons_of_neg _ l h

    @[simp] theorem count_repeat (a : α) (n : Nat) : count a (repeat a n) = n := by
      simp only [count] rw [countp_eq_length_filter', filter'_eq_self.mpr, repeat.length_repeat]
      exact fun b m => (repeat.eq_of_mem_repeat m).symm

    theorem le_count_iff_repeat_sublist {a : α} {l : List α} {n : Nat} :
      n ≤ count a l ↔ repeat a n <+ l :=
        ⟨fun h => by
          exact ((repeat.repeat_sublist_repeat a).mpr h).trans (by
            have : filter' (Eq a) l = repeat a (count a l) := repeat.eq_repeat.mpr
              ⟨by simp only [count, countp_eq_length_filter'],
              fun b m => (of_mem_filter' m).symm⟩
            rw [←this]; exact filter'_sublist _),
        fun h => by
          rw [←count_repeat a n]
          exact h.count_le a⟩

    theorem count_pos {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
      simp only [count, countp_pos]
      exact ⟨fun ⟨_, h₁, h₂⟩ => h₂ ▸ h₁, fun h => ⟨a, h, rfl⟩⟩

  end count

  section bag_inter

    protected noncomputable def bag_inter : List α → List α → List α
    | []   , _  => []
    | _    , [] => []
    | a::l₁, l₂ => if a ∈ l₂ then a :: List.bag_inter l₁ (l₂.erase a) else List.bag_inter l₁ l₂

    @[simp] theorem nil_bag_inter (l : List α) : [].bag_inter l = [] := by
      cases l; repeat rfl

    @[simp] theorem bag_inter_nil (l : List α) : l.bag_inter [] = [] := by
      cases l; repeat rfl

    @[simp] theorem cons_bag_inter_of_pos (l₁ : List α) (h : a ∈ l₂) :
      (a :: l₁).bag_inter l₂ = a :: l₁.bag_inter (l₂.erase a) := by
      cases l₂; contradiction; exact if_pos h

    @[simp] theorem cons_bag_inter_of_neg (l₁ : List α) (h : a ∉ l₂) :
      (a :: l₁).bag_inter l₂ = l₁.bag_inter l₂ := by
        cases l₂; simp only [bag_inter_nil]
        simp only [erase_of_not_mem h, List.bag_inter, if_neg h]

    theorem bag_inter_sublist_left : ∀ l₁ l₂ : List α, l₁.bag_inter l₂ <+ l₁
    | []     , l₂ => by simp only [nil_bag_inter, Sublist.nil_sublist]
    | b :: l₁, l₂ => by
      byCases h : b ∈ l₂
      { rw [List.cons_bag_inter_of_pos _ h]
        exact (bag_inter_sublist_left _ _).cons_cons _ }
      { rw [List.cons_bag_inter_of_neg _ h]
        exact Sublist.sublist_cons_of_sublist b (bag_inter_sublist_left l₁ l₂) }

  end bag_inter
  section pw_filter
    variable (r : α → α → Prop)

    noncomputable def pw_filter : List α → List α
    | []      => []
    | x :: xs =>
      let xs := pw_filter xs
      if ∀ y ∈ xs, r x y then x :: xs else xs

    @[simp] theorem pw_filter_nil : pw_filter r [] = [] := rfl

    @[simp] theorem pw_filter_cons_of_pos {r} {a : α} {l : List α} (h : ∀ b ∈ pw_filter r l, r a b) :
      pw_filter r (a :: l) = a :: pw_filter r l := if_pos h

    @[simp] theorem pw_filter_cons_of_neg {r} {a : α} {l : List α} (h : ¬ ∀ b ∈ pw_filter r l, r a b) :
      pw_filter r (a :: l) = pw_filter r l := if_neg h

    theorem pw_filter_sublist : ∀ (l : List α), pw_filter r l <+ l
    | []     => Sublist.nil_sublist _
    | x :: l => by
      byCases h : ∀ y ∈ pw_filter r l, r x y
      { exact pw_filter_cons_of_pos h ▸ (pw_filter_sublist l).cons_cons _ }
      { exact pw_filter_cons_of_neg h ▸ Sublist.sublist_cons_of_sublist _ (pw_filter_sublist l) }

    theorem pw_filter_subset (l : List α) : pw_filter r l ⊆ l :=
      (pw_filter_sublist r _).subset

    theorem forall_mem_pw_filter {r} (neg_trans : ∀ {x y z}, r x z → r x y ∨ r y z)
      (a : α) (l : List α) : (∀ b ∈ pw_filter r l, r a b) ↔ ∀ b ∈ l, r a b :=
        ⟨by
          induction l with
          | nil => intros; contradiction
          | cons x l ih =>
            byCases h : ∀ y ∈ pw_filter r l, r x y
            { simp only [pw_filter_cons_of_pos h, forall_mem_cons, and_imp]
              exact fun r h => ⟨r, ih h⟩ }
            { simp only [pw_filter_cons_of_neg h, forall_mem_cons]
              exact fun ha => ⟨by
                simp only [not_forall] at h; let ⟨y, hy, hxy⟩ := h
                exact (neg_trans (ha y hy)).resolve_right hxy, ih ha⟩ },
        fun h b hb => h b (pw_filter_subset r l hb)⟩

  end pw_filter
  section dedup

    noncomputable def dedup : List α → List α := pw_filter (· ≠ ·)

    @[simp] theorem mem_dedup {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l :=
      ⟨(pw_filter_subset (· ≠ ·) l ·), fun ha => by
        have := not_iff_not.mpr (@forall_mem_pw_filter α (· ≠ ·) (fun hxz => by
          rw [←not_and_iff_or_not]; exact fun ⟨hxy, hyz⟩ => hxz (hxy.trans hyz)) a l)
        simp only [not_forall, iff_not_not] at this
        let ⟨y, hy, hay⟩ := this.mpr ⟨a, ha, rfl⟩; exact hay ▸ hy⟩

    theorem dedup_sublist : ∀ (l : List α), l.dedup <+ l := pw_filter_sublist _

  end dedup

  def disjoint (s t : List α) : Prop := ∀ x, x ∈ s → x ∉ t

  theorem disjoint.symm {s t : List α} : disjoint s t ↔ disjoint t s :=
    have : ∀ s t : List α, disjoint s t → disjoint t s :=
      fun s t h x ht hs => h x hs ht
    ⟨this s t, this t s⟩

  theorem disjoint_iff_ne {l₁ l₂ : List α} : disjoint l₁ l₂ ↔ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b :=
    ⟨fun h x hx y hy hxy => absurd hy (hxy ▸ h x hx), fun h x h₁ h₂ => absurd rfl (h x h₁ x h₂)⟩

end List
