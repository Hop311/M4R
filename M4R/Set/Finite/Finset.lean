import M4R.Set.Finite.UnorderedList

namespace M4R

  structure Finset (α : Type _) where
    elems : UnorderedList α
    nodup : elems.nodup

  class Fintype (α : Type _) where
    (elems    : Finset α)
    (complete : ∀ x : α, x ∈ elems.elems)

  namespace Finset
    instance FinsetCoe : Coe (Finset α) (UnorderedList α) where coe := Finset.elems

    instance FinsetMem : Mem α (Finset α) where mem := fun x f => x ∈ f.elems

    instance FinsetSizeOf : SizeOf (Finset α) where sizeOf := fun f => f.elems.sizeOf

    def length (f : Finset α) : Nat := f.elems.length

    protected def toSet (f : Finset α) : Set α := Set.toSet f
    protected def ext_Set (f : Finset α) : ∀ x, x ∈ f ↔ x ∈ f.toSet := fun x => ⟨id, id⟩

    @[simp] theorem val_inj {s t : Finset α} : s.elems = t.elems ↔ s = t :=
      ⟨match s, t with | ⟨_, _⟩, ⟨_, _⟩ => by rw [Finset.mk.injEq]; exact id, congrArg _⟩

    theorem ext_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
      val_inj.symm.trans (UnorderedList.nodup_ext s₁.nodup s₂.nodup)

    protected theorem ext {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
      ext_iff.mpr

    theorem antisymm {s₁ s₂ : Finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
      Finset.ext fun a => ⟨@H₁ a, @H₂ a⟩

    protected def Empty : Finset α := ⟨0, Pairwise.nil⟩
    protected def Universal [Fintype α] : Finset α := Fintype.elems

    instance EmptyFinsetEmptyCollection : EmptyCollection (Finset α) where
      emptyCollection := Finset.Empty

    theorem eq_empty_of_forall_not_mem {s : Finset α} (h : ∀ x, x ∉ s) : s = ∅ :=
      Finset.ext fun a => ⟨fun ha => absurd ha (h a), fun _ => by contradiction⟩

    protected def singleton (a : α) : Finset α := ⟨UnorderedList.singleton a, Pairwise.singleton _ a⟩

    protected theorem in_singleton {a a' : α} : a' ∈ Finset.singleton a → a' = a :=
      UnorderedList.in_singleton

    protected theorem self_singleton (a : α) : a ∈ Finset.singleton a :=
      UnorderedList.self_singleton a

    protected def map (f : α → β) (s : Finset α) : UnorderedList β := s.elems.map f
    protected def map_inj {f : α → β} (hf : Function.injective f) (s : Finset α) : Finset β :=
      ⟨s.elems.map f, s.elems.nodup_map hf s.nodup⟩

    @[simp] theorem val_le_iff {s₁ s₂ : Finset α} : s₁.elems ≤ s₂.elems ↔ s₁ ⊆ s₂ :=
      UnorderedList.le.le_iff_subset s₁.nodup

    noncomputable def union (s₁ s₂ : Finset α) : Finset α :=
      ⟨s₁.elems.ndunion s₂.elems, UnorderedList.nodup_ndunion s₁.elems s₂.nodup⟩

    noncomputable instance FinsetUnion : Union (Finset α) where union := union

    @[simp] theorem union_val (s₁ s₂ : Finset α) : (s₁ ∪ s₂).elems = s₁.elems ∪ s₂.elems :=
      UnorderedList.ndunion_eq_union s₁.nodup

    @[simp] theorem mem_union {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
      UnorderedList.mem_ndunion

    theorem mem_union_left {a : α} {s₁ : Finset α} (s₂ : Finset α) (h : a ∈ s₁) : a ∈ s₁ ∪ s₂ :=
      mem_union.mpr (Or.inl h)

    theorem mem_union_right {a : α} {s₂ : Finset α} (s₁ : Finset α) (h : a ∈ s₂) : a ∈ s₁ ∪ s₂ :=
      mem_union.mpr (Or.inr h)

    theorem union_subset {s₁ s₂ s₃ : Finset α} (h₁ : s₁ ⊆ s₃) (h₂ : s₂ ⊆ s₃) : s₁ ∪ s₂ ⊆ s₃ :=
      val_le_iff.mp (UnorderedList.ndunion_le.2 ⟨h₁, val_le_iff.mpr h₂⟩)

    theorem subset_union_left (s₁ s₂ : Finset α) : s₁ ⊆ s₁ ∪ s₂ := fun x => mem_union_left _

    theorem subset_union_right (s₁ s₂ : Finset α) : s₂ ⊆ s₁ ∪ s₂ := fun x => mem_union_right _

    theorem union_subset_union {s₁ t₁ s₂ t₂ : Finset α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) :
        s₁ ∪ s₂ ⊆ t₁ ∪ t₂ := by
          intro x hx; rw [mem_union] at hx ⊢
          exact Or.elim hx (fun h => Or.inl (h₁ h)) (fun h => Or.inr (h₂ h))

    theorem union_comm (s₁ s₂ : Finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ := by
      apply Finset.ext; intro _; simp only [mem_union, Or.comm']; exact Iff.rfl

    theorem union_assoc (s₁ s₂ s₃ : Finset α) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
      apply Finset.ext; intro _; simp only [mem_union, Or.assoc]; exact Iff.rfl

    noncomputable def intersection (s₁ s₂ : Finset α) : Finset α :=
      ⟨s₁.elems.ndinter s₂.elems, UnorderedList.nodup_ndinter s₂.elems s₁.nodup⟩

    noncomputable instance FinsetIntersection : Intersection (Finset α) where intersection := intersection

    @[simp] theorem inter_val (s₁ s₂ : Finset α) : (s₁ ∩ s₂).elems = s₁.elems ∩ s₂.elems :=
      UnorderedList.ndinter_eq_inter s₁.nodup

    @[simp] theorem mem_inter {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
      UnorderedList.mem_ndinter

    theorem inter_comm (s₁ s₂ : Finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ := by
      apply Finset.ext; intro _; simp only [mem_inter, And.comm']; exact Iff.rfl

    theorem inter_assoc (s₁ s₂ s₃ : Finset α) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) := by
      apply Finset.ext; intro _; simp only [mem_inter, And.assoc]; exact Iff.rfl

    def disjoint (s₁ s₂ : Finset α) : Prop := s₁ ∩ s₂ = ∅

    noncomputable def filter (p : α → Prop) (s : Finset α) : Finset α := ⟨UnorderedList.filter p s.elems, 
      UnorderedList.nodup_filter p s.nodup⟩

    @[simp] theorem filter_val (p : α → Prop) (s : Finset α) : (s.filter p).elems = s.elems.filter p := rfl

    @[simp] theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a := UnorderedList.mem_filter

    noncomputable instance sdiff_SetMinus : SetMinus (Finset α) :=
      ⟨fun s₁ s₂ => ⟨s₁.elems - s₂.elems, @UnorderedList.le.nodup_of_le α (s₁.elems - s₂.elems) s₁.elems
        (UnorderedList.le.sub_le_self _ _) s₁.nodup⟩⟩

    @[simp] theorem sdiff_val (s₁ s₂ : Finset α) : (s₁ ∖ s₂).elems = s₁.elems - s₂.elems := rfl

    @[simp] theorem mem_sdiff {s t : Finset α} {a : α}: a ∈ s ∖ t ↔ a ∈ s ∧ a ∉ t :=
      UnorderedList.sub.mem_sub_of_nodup s.nodup

    theorem union_sdiff_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁ ∪ (s₂ ∖ s₁) = s₂ := by
      apply Finset.ext; intro x;
      simp only [Finset.mem_union, Finset.mem_sdiff];
      exact ⟨fun h' => Or.elim h' (h ·) And.left,
        fun h' => Or.elim (Classical.em (x ∈ s₁)) Or.inl (Or.inr ⟨h', ·⟩)⟩

    theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : (s₂ ∖ s₁) ∪ s₁ = s₂ :=
      (union_comm _ _).trans (union_sdiff_of_subset h)

    theorem inter_sdiff (s t u : Finset α) : s ∩ (t ∖ u) = (s ∩ t) ∖ u := by
      apply Finset.ext; intro x; simp only [mem_inter, mem_sdiff, And.assoc]; exact Iff.rfl

    @[simp] theorem inter_sdiff_self (s₁ s₂ : Finset α) : s₁ ∩ (s₂ ∖ s₁) = ∅ :=
      eq_empty_of_forall_not_mem (by simp only [mem_inter, mem_sdiff]; exact fun x ⟨h, _, hn⟩ => absurd h hn)

    section cons
      
      def cons (a : α) (s : Finset α) (h : a ∉ s) : Finset α :=
        ⟨s.elems.cons a, UnorderedList.nodup_cons.mpr ⟨h, s.nodup⟩⟩

      @[simp] theorem mem_cons {a : α} {s : Finset α} {h : a ∉ s} {b : α} : b ∈ @cons α a s h ↔ b = a ∨ b ∈ s :=
        UnorderedList.mem_cons

      @[simp] theorem mem_cons_self (a : α) (s : Finset α) {h : a ∉ s} : a ∈ cons a s h :=
        mem_cons.mpr (Or.inl rfl)

      @[simp] theorem cons_val {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).elems = s.elems.cons a := rfl

      @[simp] theorem mk_cons {a : α} {s : UnorderedList α} (h : (s.cons a).nodup) :
        (⟨s.cons a, h⟩ : Finset α) = cons a ⟨s, (UnorderedList.nodup_cons.mp h).right⟩ (UnorderedList.nodup_cons.mp h).left := rfl

    end cons

    section insert
  
      noncomputable def insert (a : α) (s : Finset α) : Finset α :=
        ⟨s.elems.ndinsert a, UnorderedList.nodup_ndinsert a s.nodup⟩

      theorem insert_def (a : α) (s : Finset α) : insert a s = ⟨s.elems.ndinsert a, UnorderedList.nodup_ndinsert a s.nodup⟩ := rfl

      @[simp] theorem insert_val (a : α) (s : Finset α) : (insert a s).elems = s.elems.ndinsert a := rfl

      theorem insert_val_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).elems = s.elems.cons a := by
        rw [insert_val, UnorderedList.ndinsert_of_not_mem h]

      @[simp] theorem mem_insert {a b : α} {s : Finset α} : a ∈ insert b s ↔ a = b ∨ a ∈ s := UnorderedList.mem_ndinsert

      theorem mem_insert_self (a : α) (s : Finset α) : a ∈ insert a s := UnorderedList.mem_ndinsert_self a s.elems

      theorem mem_insert_of_mem {a b : α} {s : Finset α} (h : a ∈ s) : a ∈ insert b s :=
        UnorderedList.mem_ndinsert_of_mem h

      theorem mem_of_mem_insert_of_ne {a b : α} {s : Finset α} (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
        (mem_insert.mp h).resolve_left

      @[simp] theorem cons_eq_insert (a : α) (s : Finset α) (h : a ∉ s) : @cons α a s h = insert a s := by
        apply Finset.ext; intro x; rw [mem_cons, mem_insert]; exact Iff.rfl

      @[simp] theorem insert_eq_of_mem {a : α} {s : Finset α} (h : a ∈ s) : insert a s = s :=
        val_inj.mp (UnorderedList.ndinsert_of_mem h)

      theorem insert.comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) := by
        apply Finset.ext; intro x; rw [mem_insert, mem_insert, mem_insert, mem_insert,
          Or.left_comm']; exact Iff.rfl

    end insert

    theorem cons_induction {p : Finset α → Prop} (h₁ : p ∅)
      (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
    | ⟨s, nd⟩ =>
      @UnorderedList.induction_on α (fun l => (h : l.nodup) → p ⟨l, h⟩) s
        (fun _ => h₁) (fun a s ih nd => by
          let ⟨m, nd'⟩ := UnorderedList.nodup_cons.mp nd
          rw [(val_inj.mp rfl : ⟨s.cons a, nd⟩ = cons a (Finset.mk s nd') m)]
          exact h₂ m (ih nd')) nd

    theorem cons_induction_on {p : Finset α → Prop} (s : Finset α) (h₁ : p ∅)
      (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : p s :=
        cons_induction h₁ h₂ s

    protected theorem induction (p : Finset α → Prop) (h₁ : p ∅)
      (h₂ : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
        cons_induction h₁ fun a s ha => (s.cons_eq_insert a ha).symm ▸ h₂ ha

    protected theorem induction_on (p : Finset α → Prop) (s : Finset α) (h₁ : p ∅)
      (h₂ : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : p s :=
        Finset.induction p h₁ h₂ s

  end Finset

  namespace Set

    def to_finset (s : Set α) [Fintype s] : Finset α :=
      ⟨(@Finset.Universal s).elems.map Subtype.val, by
        apply UnorderedList.nodup_map; apply Set.elementExt; exact Finset.Universal.nodup;⟩

    @[simp] theorem mem_to_finset {s : Set α} [Fintype s] {a : α} : a ∈ s.to_finset ↔ a ∈ s :=
      ⟨fun h => by let ⟨⟨x, hx⟩, _, h'⟩ := UnorderedList.map.mem_map.mp h; rw [←h']; exact hx,
      fun h => UnorderedList.map.mem_map.mpr ⟨⟨a, h⟩, Fintype.complete _, rfl⟩⟩
      
    @[simp] theorem mem_to_finset_val {s : Set α} [Fintype s] {a : α} : a ∈ s.to_finset.elems ↔ a ∈ s :=
      mem_to_finset

  end Set

  namespace Fintype

    protected instance Empty : Fintype (∅ : Set α) where
      elems := ∅
      complete := fun ⟨x, hx⟩ => by contradiction

    protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) : Fintype {x // p x} :=
      ⟨⟨UnorderedList.pmap Subtype.mk s.elems fun x => (H x).mp,
        UnorderedList.nodup_pmap (fun a _ b _ => congrArg Subtype.val) s.nodup⟩,
      fun ⟨x, px⟩ => UnorderedList.mem_pmap.mpr ⟨x, (H x).mpr px, rfl⟩⟩

    protected def of_finset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p :=
      Fintype.subtype s H
    
    protected noncomputable instance union (s t : Set α) [Fintype s] [Fintype t] : Fintype (s ∪ t : Set α) :=
      Fintype.of_finset (s.to_finset ∪ t.to_finset) (fun x =>
        ⟨fun h => by
          have := UnorderedList.mem_ndunion.mp h
          simp only [Set.mem_to_finset_val] at this
          exact this,
        fun h => 
          Finset.mem_union.mpr (Or.elim h
            (fun h' => Or.inl (Set.mem_to_finset.mpr h'))
            (fun h' => Or.inr (Set.mem_to_finset.mpr h')))⟩)
  
    protected noncomputable instance sep (s : Set α) (p : α → Prop) [Fintype s] :
      Fintype (Subtype ({a ∈ s | p a} : Set α)) :=
        Fintype.of_finset (s.to_finset.filter p) (fun _ => by
          simp only [Finset.mem_filter, Set.mem_to_finset]; exact Iff.refl _)

    protected noncomputable instance intersection (s t : Set α) [Fintype s] : Fintype (s ∩ t : Set α) :=
      Fintype.sep s t

    protected noncomputable instance subset {s t : Set α} [Fintype t] (h : s ⊆ t) : Fintype s := by
      rw [←Set.intersection.inter_eq_self_of_subset_right h]
      exact Fintype.intersection t s
  
  end Fintype

  inductive finite (s : Set α) : Prop
  | intro : Fintype s → finite s

  def infinite (s : Set α) : Prop := ¬ finite s

  def Finset.to_finite (f : Finset α) : finite (f.toSet) :=
    finite.intro (Fintype.of_finset f f.ext_Set)

  namespace finite

    theorem iff_exists_fintype {s : Set α} : finite s ↔ Nonempty (Fintype s) :=
      ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩      

    noncomputable def to_fintype {s : Set α} (h : finite s) : Fintype s :=
      Classical.choice (iff_exists_fintype.mp h)

    noncomputable def to_finset {s : Set α} (h : finite s) : Finset α :=
      @Set.to_finset _ s h.to_fintype

    @[simp] theorem mem_to_finset {s : Set α} (hs : finite s) {a : α} : a ∈ hs.to_finset ↔ a ∈ s :=
      ⟨fun h => by let ⟨⟨x, hx⟩, _, h'⟩ := UnorderedList.map.mem_map.mp h; rw [←h']; exact hx,
      fun h => UnorderedList.map.mem_map.mpr ⟨⟨a, h⟩, hs.to_fintype.complete _, rfl⟩⟩
      
    @[simp] theorem mem_to_finset_val {s : Set α} (hs : finite s) {a : α} : a ∈ hs.to_finset.elems ↔ a ∈ s :=
      mem_to_finset hs

    theorem subset {s t : Set α} (ht : finite t) (h : s ⊆ t) : finite s := 
      finite.intro (@Fintype.subset _ s t ht.to_fintype h)

    theorem union {s t : Set α} (hs : finite s) (ht : finite t) : finite (s ∪ t) :=
      finite.intro (@Fintype.union _ s t hs.to_fintype ht.to_fintype)
    
    theorem intersection {s : Set α} (hs : finite s) (t : Set α) : finite (s ∩ t) :=
      finite.intro (@Fintype.intersection _ s t hs.to_fintype)

    theorem intersection' (s : Set α) {t : Set α} (ht : finite t) : finite (s ∩ t) := by
      rw [Set.intersection.comm]; exact intersection ht s

  end finite
end M4R