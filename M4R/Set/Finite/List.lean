import M4R.Notation
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

  theorem eqNilOfLengthEqZero {l : List α} : l.length = 0 → l = [] := by
    induction l with
    | nil  => intros; rfl
    | cons => intros; contradiction

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

  theorem memSplit {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t := by
    induction l with 
    | nil         => contradiction
    | cons b l ih => apply Or.elim h (fun ab =>
      by rw [ab]; exact ⟨[], l, rfl⟩) (fun ainl =>
        by let ⟨s, t, p⟩ := ih ainl; rw [p]; exact ⟨b::s, t, rfl⟩); 

  @[simp] theorem memAppend {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
      induction s with
      | nil => simp
      | cons _ _ ih => exact
        ⟨fun p => Or.elim p (fun x => Or.inl (Or.inl x)) (fun x => Or.assoc.mp (Or.inr (ih.mp x))),
          fun p => Or.elim p (fun q => Or.elim q Or.inl
            (fun x => Or.inr (ih.mpr (Or.inl x)))) (fun x => Or.inr (ih.mpr (Or.inr x)))⟩

  @[simp] theorem appendSingleton {a : α} {l : List α} : [a] ++ l = a::l := by rfl

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

end List
