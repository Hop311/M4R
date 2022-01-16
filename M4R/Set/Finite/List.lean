import M4R.Set.MemStructure
import M4R.Logic
    
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

  theorem cons_ext {a b : α} {s t : List α} : a :: s = b :: t ↔ a = b ∧ s = t :=
    ⟨List.cons.inj, fun ⟨h₁, h₂⟩ => congr (congrArg List.cons h₁) h₂⟩

  @[simp] theorem memNilIff (a : α) : a ∈ ([] : List α) ↔ False :=
    Iff.rfl
  @[simp] theorem notMemNil (a : α) : a ∉ ([] : List α) :=
    Iff.mp (memNilIff a)

  theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l :=
    Or.inl rfl
  
  @[simp] theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l :=
    Or.inr

  @[simp] theorem eq_or_mem_of_mem_cons {a y : α} {l : List α} : a ∈ y::l → a = y ∨ a ∈ l := by
    simp only [Mem.mem, List.mem]; exact id

  theorem mem_cons_iff {a b : α} {l : List α} : a ∈ b :: l ↔ a = b ∨ a ∈ l :=
    ⟨eq_or_mem_of_mem_cons, fun h =>
      Or.elim h (fun h' => by rw [h']; exact mem_cons_self b l) (mem_cons_of_mem b)⟩

  theorem forall_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
      ⟨fun h => ⟨h a (mem_cons_self a l), fun x xl => h x (mem_cons_of_mem a xl)⟩, fun ⟨h₁, h₂⟩ x hx => by
        cases hx with
        | inl h => rw [h]; exact h₁
        | inr h => exact h₂ x h⟩
  
  @[simp] theorem forall_mem_ne {a : α} {l : List α} : (∀ (a' : α), a' ∈ l → ¬a = a') ↔ a ∉ l :=
    ⟨fun h m => h _ m rfl, fun h a' m e => h (e.symm ▸ m)⟩

  theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l :=
    fun h₁ h₂ h₃ => Or.elim (eq_or_mem_of_mem_cons h₃) h₁ h₂

  theorem mem_split {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t := by
    induction l with 
    | nil         => contradiction
    | cons b l ih => apply Or.elim h (fun ab =>
      by rw [ab]; exact ⟨[], l, rfl⟩) (fun ainl =>
        by let ⟨s, t, p⟩ := ih ainl; rw [p]; exact ⟨b::s, t, rfl⟩); 

  theorem eq_nil_of_subset_nil : ∀ {l : List α}, l ⊆ [] → l = []
  | []  , s => rfl
  | a::l, s => False.elim (s (mem_cons_self a l))

  protected theorem in_singleton {a a' : α} : a' ∈ [a] → a' = a := by
    intro ha';
    simp only [Mem.mem, List.mem, or_false] at ha'
    exact ha'

  protected theorem self_singleton (a : α) : a ∈ [a] := by
    simp only [Mem.mem, List.mem]

  @[simp] theorem memAppend {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
      induction s with
      | nil => simp
      | cons _ _ ih => exact
        ⟨fun p => Or.elim p (fun x => Or.inl (Or.inl x)) (fun x => Or.assoc.mp (Or.inr (ih.mp x))),
          fun p => Or.elim p (fun q => Or.elim q Or.inl
            (fun x => Or.inr (ih.mpr (Or.inl x)))) (fun x => Or.inr (ih.mpr (Or.inr x)))⟩

  @[simp] theorem appendSingleton {a : α} {l : List α} : [a] ++ l = a::l := by rfl

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
    | cons a l ih => simp [ih]

  @[simp] theorem map_id (l : List α) : map id l = l := by
    induction l with
    | nil => rfl
    | cons a b ih => simp [map, ih]

  theorem filterMap_Eq_map (f : α → β) : filterMap (some ∘ f) = map f := by
    apply funext; intro l;
    induction l with
    | nil => simp only [filterMap, map];
    | cons _ _ ih => simp [filterMap, map]; exact ih

  @[simp] theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : List β) :
    foldl f a (b::l) = foldl f (f a b) l := rfl

  @[simp] theorem foldl_append (f : α → β → α) (a : α) (l₁ l₂ : List β) :
    foldl f a (l₁++l₂) = foldl f (foldl f a l₁) l₂ :=
      match l₁ with
      | []      => rfl
      | b::l₁ => by simp only [cons_append, foldl_cons, foldl_append f (f a b) l₁ l₂]

  @[simp] theorem foldl_empty (f : α → β → α) (a : α) :
    foldl f a [] = a := rfl

  @[simp] theorem foldl_singleton (f : α → β → α) (a : α) (b : β) :
    foldl f a [b] = f a b := rfl

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

    protected theorem subset {l₁ l₂ : List α} : l₁ <+ l₂ → l₁ ⊆ l₂
    | nil, b, h => h
    | cons l₁ l₂ a s, b, h => mem_cons_of_mem _ (Sublist.subset s h)
    | cons' l₁ l₂ a s, b, h => by
      cases eq_or_mem_of_mem_cons h with
      | inl h => exact h ▸ mem_cons_self _ _
      | inr h => exact mem_cons_of_mem _ (Sublist.subset s h)

    theorem eq_nil_of_sublist_nil {l : List α} (s : l <+ []) : l = [] :=
      eq_nil_of_subset_nil s.subset

    theorem eq_of_sublist_of_length_eq {l₁ l₂ : List α} : l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
    | nil, h => rfl
    | cons l₁ l₂ a s, h => absurd (length_le_of_sublist s) $ Nat.not_le_of_gt (by rw [h]; apply Nat.lt_succ_self)
    | cons' l₁ l₂ a s, h => by simp at h; rw [eq_of_sublist_of_length_eq s h]

    theorem eq_of_sublist_of_length_le {l₁ l₂ : List α} (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) :
      l₁ = l₂ :=
        eq_of_sublist_of_length_eq s (Nat.le_antisymm (length_le_of_sublist s) h)

  end Sublist

  @[simp] def pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
  | []  , H => []
  | a::l, H => f a (forall_mem_cons.mp H).left :: pmap f l (forall_mem_cons.mp H).right
  
  def attach (l : List α) : List {x // x ∈ l} := pmap Subtype.mk l (fun _ => id)
  
  @[simp] theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
      induction l with
      | nil => rfl
      | cons _ _ ih => simp only [pmap, map, ih]

  theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
    (h : ∀ a h₁ h₂, f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
      induction l with
      | nil => rfl
      | cons _ _ ih => simp [pmap]; exact ⟨h _ _ _, ih⟩

  theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β)
    (l H) : map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
      induction l with
      | nil => rfl
      | cons _ _ ih => simp only [pmap, map, ih]

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
          simp [h₂]
        rw [this]
        exact h₁

  @[simp] theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : α) (h : a ∈ l), f a (H a h) = b := by
      simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, Subtype.exists]
      exact Iff.refl _

  open Classical

  protected noncomputable def insert (a : α) (l : List α) : List α :=
    if a ∈ l then l else a :: l

  @[simp] theorem insert_of_mem {a : α} {l : List α} (h : a ∈ l) : l.insert a = l := by
    simp only [List.insert, if_pos h]

  @[simp] theorem insert_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.insert a = a :: l :=
    by simp only [List.insert, if_neg h]

  @[simp] theorem mem_insert_iff {l : List α} : a ∈ l.insert b ↔ a = b ∨ a ∈ l := by
    byCases h : b ∈ l;
    { rw [insert_of_mem h]; exact ⟨Or.inr, fun h' => Or.elim h' (fun h'' => by rw [h'']; exact h) id⟩ }
    simp only [insert_of_not_mem h, mem_cons_iff]; exact Iff.refl _

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

  noncomputable def filter' (p : α → Prop) : List α → List α
  | []     => []
  | (a::l) => if p a then a :: filter' p l else filter' p l

  @[simp] theorem filter'_cons_of_pos {a : α} (l: List α) (h : p a) : filter' p (a :: l) = a :: filter' p l :=
    if_pos h

    
  @[simp] theorem filter'_cons_of_neg {a : α} (s) (h : ¬ p a) : filter' p (a :: s) = filter' p s :=
    if_neg h

  theorem filter_map_eq_filter' (p : α → Prop) : filterMap (Option.guard p) = filter' p := by
    apply funext; intro l;
    induction l with
    | nil => rfl
    | cons a l ih =>
      byCases pa : p a;
      { simp only [filterMap, Option.guard, if_pos pa, filter'_cons_of_pos _ pa];
      exact cons_ext.mpr ⟨rfl, ih⟩ }
      simp only [filterMap, Option.guard, if_neg pa, filter'_cons_of_neg _ pa]; exact ih

  @[simp] theorem filter'_sublist {p : α → Prop} : ∀ (l : List α), filter' p l <+ l
  | []   => Sublist.nil
  | a::l =>
    if pa : p a then by
      simp [pa]; apply Sublist.cons'; exact filter'_sublist l
    else by
      simp [pa]; apply Sublist.cons; exact filter'_sublist l

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

end List
