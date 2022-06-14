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

    instance FinsetToSubtype {α : Type u} : CoeSort (Finset α) (Type u) where coe := fun f => {x // x ∈ f}

    instance FinsetSizeOf : SizeOf (Finset α) where sizeOf := fun f => f.elems.sizeOf

    def length (f : Finset α) : Nat := f.elems.length

    theorem val_nodup (f : Finset α) : f.elems.nodup := f.nodup

    protected def toSet (f : Finset α) : Set α := Set.toSet f
    protected def ext_toSet {f : Finset α} {x : α} : x ∈ f ↔ x ∈ f.toSet := ⟨id, id⟩

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

    def length_empty (α : Type _) : (∅ : Finset α).length = 0 := rfl

    theorem empty_subset (f : Finset α) : (∅ : Finset α) ⊆ f :=
      fun _ _ => by contradiction

    theorem eq_empty_of_forall_not_mem {s : Finset α} (h : ∀ x, x ∉ s) : s = ∅ :=
      Finset.ext fun a => ⟨fun ha => absurd ha (h a), fun _ => by contradiction⟩

    theorem eq_empty_of_subset_empty {s : Finset α} (h : s ⊆ ∅) : s = ∅ :=
      eq_empty_of_forall_not_mem fun x hx => h hx

    theorem mem_empty {a : α} : a ∈ (∅ : Finset α) ↔ False := Iff.rfl
    theorem empty_val (α : Type _) : (∅ : Finset α).elems = 0 := rfl
    theorem empty_toSet (α : Type _) : (∅ : Finset α).toSet = ∅ := rfl

    theorem eq_empty_of_length_eq_zero {s : Finset α} (hs : s.length = 0) : s = ∅ :=
      val_inj.mp (UnorderedList.eq_nil_of_length_eq_zero hs)

    protected def singleton (a : α) : Finset α := ⟨UnorderedList.singleton a, Pairwise.singleton _ a⟩

    protected theorem in_singleton {a a' : α} : a' ∈ Finset.singleton a → a' = a :=
      UnorderedList.in_singleton

    protected theorem self_singleton (a : α) : a ∈ Finset.singleton a :=
      UnorderedList.self_singleton a

    protected theorem mem_singleton {a a' : α} : a' ∈ Finset.singleton a ↔ a' = a :=
      ⟨Finset.in_singleton, fun h => h.symm ▸ Finset.self_singleton a⟩

    theorem singleton_toSet (a : α) : (Finset.singleton a).toSet = Set.singleton a :=
      Set.ext.mp fun _ => Iff.trans Finset.mem_singleton Iff.rfl

    theorem length.eq_one {s : Finset α} : s.length = 1 ↔ ∃ a, s = Finset.singleton a :=
      Iff.trans UnorderedList.length.eq_one
        ⟨fun ⟨a, ha⟩ => ⟨a, val_inj.mp ha⟩, fun ⟨a, ha⟩ => ⟨a, val_inj.mpr ha⟩⟩

    section map
      protected def map (f : α → β) (s : Finset α) : UnorderedList β := s.elems.map f
      protected def map_inj {f : α → β} (hf : Function.injective f) (s : Finset α) : Finset β :=
        ⟨s.elems.map f, s.elems.nodup_map hf s.nodup⟩

      protected theorem map_mem {f : α → β} {b : β} {s : Finset α} : b ∈ s.map f ↔ ∃ a, a ∈ s ∧ f a = b :=
        UnorderedList.map.mem_map
      protected theorem map_inj_mem {f : α → β} {hf : Function.injective f} {b : β} {s : Finset α} :
        b ∈ s.map_inj hf ↔ ∃ a, a ∈ s ∧ f a = b  :=
          UnorderedList.map.mem_map
      protected theorem map_inj_mem' {f : α → β} {hf : Function.injective f} {b : β} {s : Finset α} :
        b ∈ s.map_inj hf ↔ ∃ a, a ∈ s ∧ f a = b ∧ ∀ a', f a' = b → a' = a :=
          ⟨fun h => by cases Finset.map_inj_mem.mp h with | intro a ha =>
            exact ⟨a, ha.left, ha.right, fun a' ha' => by rw [←ha.right] at ha'; exact hf ha'⟩,
          fun ⟨a, b, c, _⟩ => Finset.map_inj_mem.mpr ⟨a, b, c⟩⟩

      protected theorem mem_map_inj {f : α → β} {hf : Function.injective f} {a : α} {s : Finset α} : a ∈ s ↔ f a ∈ s.map_inj hf :=
        ⟨fun h => Finset.map_inj_mem.mpr ⟨a, h, rfl⟩,
        fun h => let ⟨b, hb, _, hu⟩ := Finset.map_inj_mem'.mp h; hu a rfl ▸ hb⟩
      protected theorem not_mem_map_inj {f : α → β} {hf : Function.injective f} {a : α} {s : Finset α} :
        a ∉ s ↔ f a ∉ s.map_inj hf := not_iff_not.mpr Finset.mem_map_inj

      protected theorem map_empty (f : α → β) : Finset.map f ∅ = 0 := rfl
      protected theorem map_inj_empty {f : α → β} (hf : Function.injective f) : Finset.map_inj hf ∅ = ∅ := rfl
    end map

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

    theorem union_self (s : Finset α) : s ∪ s = s :=
      Finset.ext fun a => by rw [Finset.mem_union, or_self]; exact Iff.rfl

    theorem union_toSet (s t : Finset α) : (s ∪ t).toSet = s.toSet ∪ t.toSet :=
      Set.ext.mp fun _ => by rw [←Finset.ext_toSet, mem_union]; exact Iff.rfl

    theorem union_empty_right (s : Finset α) : s ∪ ∅ = s :=
      Finset.ext fun x => by rw [mem_union, mem_empty, or_false]; exact Iff.rfl

    theorem union_empty_left (s : Finset α) : ∅ ∪ s = s :=
      union_comm ∅ s ▸ union_empty_right s

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

    theorem singleton_disjoint {a b : α} : disjoint (Finset.singleton a) (Finset.singleton b) ↔ a ≠ b := by
      simp only [disjoint, Finset.ext_iff, Finset.mem_empty, iff_false, Finset.mem_inter, not_and_iff_or_not,
        Finset.mem_singleton]
      exact ⟨fun h => (h a).resolve_left (iff_not_not.mpr rfl), fun h x => by
        byCases hx : x = a
        { exact hx.symm ▸ Or.inr h }
        { exact Or.inl hx }⟩

    noncomputable def filter (p : α → Prop) (s : Finset α) : Finset α := ⟨UnorderedList.filter p s.elems,
      UnorderedList.nodup_filter p s.nodup⟩

    @[simp] theorem filter_val (p : α → Prop) (s : Finset α) : (s.filter p).elems = s.elems.filter p := rfl

    @[simp] theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a := UnorderedList.mem_filter

    theorem filter_empty (p : α → Prop) : (∅ : Finset α).filter p = ∅ := rfl

    noncomputable instance sdiff_SetMinus : SetMinus (Finset α) :=
      ⟨fun s₁ s₂ => ⟨s₁.elems - s₂.elems, @UnorderedList.le.nodup_of_le α (s₁.elems - s₂.elems) s₁.elems
        (UnorderedList.le.sub_le_self _ _) s₁.nodup⟩⟩

    @[simp] theorem sdiff_val (s₁ s₂ : Finset α) : (s₁ ∖ s₂).elems = s₁.elems - s₂.elems := rfl

    @[simp] theorem mem_sdiff {s t : Finset α} {a : α}: a ∈ s ∖ t ↔ a ∈ s ∧ a ∉ t :=
      UnorderedList.sub.mem_sub_of_nodup s.nodup

    theorem union_sdiff_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁ ∪ (s₂ ∖ s₁) = s₂ := by
      apply Finset.ext; intro x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      exact ⟨fun h' => Or.elim h' (h ·) And.left,
        fun h' => Or.elim (Classical.em (x ∈ s₁)) Or.inl (Or.inr ⟨h', ·⟩)⟩

    theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : (s₂ ∖ s₁) ∪ s₁ = s₂ :=
      (union_comm _ _).trans (union_sdiff_of_subset h)

    theorem inter_sdiff (s t u : Finset α) : s ∩ (t ∖ u) = (s ∩ t) ∖ u := by
      apply Finset.ext; intro x; simp only [mem_inter, mem_sdiff, And.assoc]; exact Iff.rfl

    @[simp] theorem inter_sdiff_self (s₁ s₂ : Finset α) : s₁ ∩ (s₂ ∖ s₁) = ∅ :=
      eq_empty_of_forall_not_mem (by simp only [mem_inter, mem_sdiff]; exact fun x ⟨h, _, hn⟩ => absurd h hn)

    theorem union_sdiff (s₁ s₂ : Finset α) : s₁ ∪ s₂ ∖ s₁ = s₁ ∪ s₂ :=
      Finset.ext fun _ => by
        simp only [Finset.mem_union, Finset.mem_sdiff]
        exact ⟨Or.imp_right And.left, (Or.elim · Or.inl (fun h => or_iff_not_imp_left.mpr (And.intro h)))⟩

    theorem disjoint_sdiff (s₁ s₂ : Finset α) : disjoint s₁ (s₂ ∖ s₁) :=
      inter_sdiff_self s₁ s₂

    theorem sdiff_empty_left (s : Finset α) : ∅ ∖ s = ∅ :=
      Finset.ext fun _ => by simp only [Finset.mem_sdiff, Finset.mem_empty, false_and]

    theorem sdiff_empty_right (s : Finset α) : s ∖ ∅ = s :=
      Finset.ext fun _ => by simp only [Finset.mem_sdiff, Finset.mem_empty, and_true]; exact Iff.rfl

    section cons

      def cons (a : α) (s : Finset α) (h : a ∉ s) : Finset α :=
        ⟨s.elems.cons a, UnorderedList.nodup_cons.mpr ⟨h, s.nodup⟩⟩

      @[simp] theorem mem_cons {a : α} {s : Finset α} {h : a ∉ s} {b : α} : b ∈ @cons α a s h ↔ b = a ∨ b ∈ s :=
        UnorderedList.mem_cons

      @[simp] theorem mem_cons_self {a : α} (s : Finset α) (h : a ∉ s) : a ∈ cons a s h :=
        mem_cons.mpr (Or.inl rfl)

      @[simp] theorem mem_cons_self' {a : α} {s : Finset α} (h : a ∉ s) {b : α} (hb : b ∈ s) : b ∈ cons a s h :=
        mem_cons.mpr (Or.inr hb)

      @[simp] theorem cons_val {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).elems = s.elems.cons a := rfl

      @[simp] theorem mk_cons {a : α} {s : UnorderedList α} (h : (s.cons a).nodup) :
        (⟨s.cons a, h⟩ : Finset α) = cons a ⟨s, (UnorderedList.nodup_cons.mp h).right⟩ (UnorderedList.nodup_cons.mp h).left := rfl

      theorem cons_subset {a : α} (s : Finset α) (h : a ∉ s) : s ⊆ s.cons a h :=
        fun _ => UnorderedList.mem_cons_of_mem

      theorem cons_subsetneq {a : α} (s : Finset α) (h : a ∉ s) : s ⊊ s.cons a h :=
        ⟨cons_subset s h, a, h, mem_cons_self s h⟩

      theorem length_cons {a : α} (s : Finset α) (h : a ∉ s) : (s.cons a h).length = s.length + 1 :=
        UnorderedList.length.cons a s

      theorem cons_toSet {a : α} {s : Finset α} (h : a ∉ s) : (s.cons a h).toSet = s.toSet.insert a :=
        Set.ext.mp fun _ => Finset.mem_cons

    end cons

    protected theorem map_cons (f : α → β) (s : Finset α) {a : α} (ha : a ∉ s) : (s.cons a ha).map f = (s.map f).cons (f a) :=
      UnorderedList.map.cons f a s
    protected theorem map_inj_cons {f : α → β} (hf : Function.injective f) (s : Finset α) {a : α} (ha : a ∉ s) :
      (s.cons a ha).map_inj hf = (s.map_inj hf).cons (f a) (Finset.not_mem_map_inj.mp ha) := by
        apply Finset.ext; intro x; rw [mem_cons]
        exact ⟨fun h =>
          let ⟨b, hb, he⟩ := Finset.map_inj_mem.mp h
          Or.imp (· ▸ he.symm : _) (he ▸ Finset.mem_map_inj.mp ·) (mem_cons.mp hb),
        fun h =>
          Or.elim h (· ▸ Finset.mem_map_inj.mp (mem_cons_self s ha)) (fun h =>
            let ⟨b, hb, he⟩ := Finset.map_inj_mem.mp h
            Finset.map_inj_mem.mpr ⟨b, mem_cons.mpr (Or.inr hb), he⟩)⟩

    @[simp] theorem length_map (f : α → β) (s : Finset α) : (s.map f).length = s.length :=
      UnorderedList.map.length_map f s.elems

    @[simp] theorem filter_cons_of_pos (p : α → Prop) {a : α} {s : Finset α} (ha : a ∉ s) (hpa : p a) : filter p (s.cons a ha) = (filter p s).cons a (fun h =>
      absurd (mem_filter.mp h).left ha) :=
        Finset.ext fun x => by
          simp only [Finset.mem_cons, Finset.mem_filter]
          exact ⟨fun ⟨h₁, h₂⟩ => h₁.imp_right (fun h => ⟨h, h₂⟩), fun h => h.elim (fun h => ⟨Or.inl h, h ▸ hpa⟩) (And.imp_left Or.inr)⟩

    @[simp] theorem filter_cons_of_neg (p : α → Prop) {a : α} {s : Finset α} (ha : a ∉ s) (hpa : ¬p a) : filter p (s.cons a ha) = filter p s :=
      Finset.ext fun x => by
        simp only [Finset.mem_filter, Finset.mem_cons]
        exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.resolve_left (fun h => absurd (h ▸ h₂) hpa), h₂⟩, And.imp_left Or.inr⟩

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

    theorem strong_induction (p : Finset α → Prop) (ih : ∀ f : Finset α, (∀ f' : Finset α, f'.length < f.length → p f') → p f)
      (f : Finset α) : p f :=
        ih f (@cons_induction _ (fun f : Finset α => ∀ f' : Finset α, f'.length < f.length → p f')
          (fun f h => absurd h f.length.not_lt_zero)
          (fun x f hx ih' f' hf' => by
            rw [Finset.length_cons] at hf'
            exact (Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ hf')).elim
              (ih' f') (fun h => ih f' (h ▸ ih'))) f)

    section erase

      noncomputable def erase (s : Finset α) (a : α) : Finset α := ⟨_, UnorderedList.erase.nodup_erase_of_nodup a s.nodup⟩

      @[simp] theorem erase_val (s : Finset α) (a : α) : (erase s a).elems = s.elems.erase a := rfl

      @[simp] theorem mem_erase {a b : α} {s : Finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
        UnorderedList.erase.mem_erase_iff_of_nodup s.nodup

      theorem not_mem_erase (a : α) (s : Finset α) : a ∉ erase s a := UnorderedList.erase.mem_erase_of_nodup s.nodup

      @[simp] theorem erase_empty (a : α) : erase ∅ a = ∅ := rfl

      theorem erase_insert {a : α} {s : Finset α} (h : a ∉ s) : erase (insert a s) a = s := by
        apply Finset.ext; intro x
        simp only [mem_erase, mem_insert, and_or_distrib_left, false_and, not_and_self, false_or]
        exact ⟨And.right, fun h' => ⟨fun h'' => by rw [h''] at h'; exact absurd h' h, h'⟩⟩

      theorem erase_cons {a : α} (s : Finset α) (hs : a ∈ s) : s = (s.erase a).cons a (not_mem_erase a s) :=
        Finset.ext fun x => by
          byCases hx : x = a
          { simp only [hx, hs, true_iff]; exact mem_cons_self _ _ }
          { simp only [mem_cons, hx, false_or, mem_erase, ne_eq, true_and]; exact Iff.rfl }

    end erase
  end Finset

  namespace Set

    def to_finset (s : Set α) [Fintype s] : Finset α :=
      ⟨(@Finset.Universal s).elems.map Subtype.val, by
        apply UnorderedList.nodup_map; apply Set.elementExt; exact Finset.Universal.nodup⟩

    @[simp] theorem mem_to_finset {s : Set α} [Fintype s] {a : α} : a ∈ s.to_finset ↔ a ∈ s :=
      ⟨fun h => by let ⟨⟨x, hx⟩, _, h'⟩ := UnorderedList.map.mem_map.mp h; rw [←h']; exact hx,
      fun h => UnorderedList.map.mem_map.mpr ⟨⟨a, h⟩, Fintype.complete _, rfl⟩⟩

    @[simp] theorem mem_to_finset_val {s : Set α} [Fintype s] {a : α} : a ∈ s.to_finset.elems ↔ a ∈ s :=
      mem_to_finset

  end Set

  namespace UnorderedList

    noncomputable def to_finset (l : UnorderedList α) : Finset α := ⟨l.dedup, UnorderedList.nodup_dedup l⟩

    @[simp] theorem to_finset_val (l : UnorderedList α) : l.to_finset.elems = l.dedup := rfl

    @[simp] theorem mem_to_finset {a : α} {s : UnorderedList α} : a ∈ s.to_finset ↔ a ∈ s := UnorderedList.mem_dedup

    @[simp] theorem to_finset_zero : to_finset (0 : UnorderedList α) = ∅ := rfl

    theorem to_finset_toSet (l : UnorderedList α) : l.toSet = l.to_finset.toSet :=
      Set.ext.mp fun _ => mem_to_finset.symm

    theorem to_finset_ext {s t : UnorderedList α} : s.to_finset = t.to_finset ↔ ∀ a, a ∈ s ↔ a ∈ t := by
      rw [Finset.ext_iff]; apply forall_congr'; intro
      rw [mem_to_finset, mem_to_finset]; exact Iff.rfl

    theorem to_finset_cons_of_pos {l : UnorderedList α} {a : α} (ha : a ∈ l) : (l.cons a).to_finset = l.to_finset := by
      apply to_finset_ext.mpr; intro; rw [UnorderedList.mem_cons]
      exact ⟨fun h => Or.elim h (· ▸ ha) id, Or.inr⟩
    theorem to_finset_cons_of_neg {l : UnorderedList α} {a : α} (ha : a ∉ l) :
      (l.cons a).to_finset = l.to_finset.cons a (mt mem_to_finset.mp ha) := by
        apply Finset.ext; intro
        rw [mem_to_finset, UnorderedList.mem_cons, Finset.mem_cons, mem_to_finset]
        exact Iff.rfl

    theorem to_finset_length_le (l : UnorderedList α) : l.to_finset.length ≤ l.length :=
      length.le_of_le l.dedup_le

  end UnorderedList

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
          simp only [Finset.mem_filter, Set.mem_to_finset]; exact Iff.rfl)

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
    finite.intro (Fintype.of_finset f (fun _ => Finset.ext_toSet))

  namespace finite

    theorem empty (α : Type _) : finite (∅ : Set α) := ⟨Fintype.Empty⟩

    theorem iff_exists_fintype {s : Set α} : finite s ↔ Nonempty (Fintype s) :=
      ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

    noncomputable def to_fintype {s : Set α} (h : finite s) : Fintype s :=
      Classical.choice (iff_exists_fintype.mp h)

    noncomputable def to_finset {s : Set α} (h : finite s) : Finset α :=
      @Set.to_finset _ s h.to_fintype

    @[simp] theorem mem_to_finset {s : Set α} (hs : finite s) {a : α} : a ∈ hs.to_finset ↔ a ∈ s :=
      ⟨fun h => by let ⟨⟨x, hx⟩, _, h'⟩ := UnorderedList.map.mem_map.mp h; rw [←h']; exact hx,
      fun h => UnorderedList.map.mem_map.mpr ⟨⟨a, h⟩, hs.to_fintype.complete _, rfl⟩⟩

    @[simp] theorem to_finset_toSet {s : Set α} (hs : finite s) : hs.to_finset.toSet = s :=
      Set.ext.mp fun _ => by rw [←hs.mem_to_finset]; exact Iff.rfl

    @[simp] theorem mem_to_finset_val {s : Set α} (hs : finite s) {a : α} : a ∈ hs.to_finset.elems ↔ a ∈ s :=
      mem_to_finset hs

    theorem to_finset_ext {s t : Set α} {hs : finite s} {ht : finite t} : hs.to_finset = ht.to_finset ↔ ∀ a, a ∈ s ↔ a ∈ t := by
      rw [Finset.ext_iff]; apply forall_congr'; intro
      rw [mem_to_finset, mem_to_finset]; exact Iff.rfl

    theorem subset {s t : Set α} (ht : finite t) (h : s ⊆ t) : finite s :=
      finite.intro (@Fintype.subset _ s t ht.to_fintype h)

    theorem union {s t : Set α} (hs : finite s) (ht : finite t) : finite (s ∪ t) :=
      finite.intro (@Fintype.union _ s t hs.to_fintype ht.to_fintype)

    theorem intersection {s : Set α} (hs : finite s) (t : Set α) : finite (s ∩ t) :=
      finite.intro (@Fintype.intersection _ s t hs.to_fintype)

    theorem intersection' (s : Set α) {t : Set α} (ht : finite t) : finite (s ∩ t) := by
      rw [Set.intersection.comm]; exact intersection ht s

  end finite
  namespace infinite
    variable {s : Set α} (hs : infinite s)
    open Classical

    theorem nonempty : ∃ x, x ∈ s :=
      byContradiction fun h => hs (by
        simp only [not_exists] at h
        exact Set.empty.mpr h ▸ finite.empty α)

    theorem not_in_finset (f : Finset α) : ∃ x ∈ s, x ∉ f :=
      byContradiction fun h => hs (by
        simp only [not_exists, not_and, iff_not_not] at h
        exact f.to_finite.subset h)

    noncomputable def choose_finset : Nat → Finset α
    | 0   => Finset.singleton (choose (hs.not_in_finset ∅))
    | n+1 => have := hs.not_in_finset (choose_finset n)
      (choose_finset n).cons (choose this) (choose_spec this).right

    theorem choose_finset_subset_succ (n : Nat) : hs.choose_finset n ⊊ hs.choose_finset n.succ :=
      Finset.cons_subsetneq _ (choose_spec (hs.not_in_finset (hs.choose_finset n))).right

    theorem choose_finset_subset_add (m n : Nat) : hs.choose_finset m ⊆ hs.choose_finset (m + n) := by
      induction n with
      | zero      => exact Subset.refl _
      | succ n ih => exact Subset.trans ih (hs.choose_finset_subset_succ (m + n)).left

    theorem choose_finset_subset_le {m n : Nat} (h : m ≤ n) : hs.choose_finset m ⊆ hs.choose_finset n :=
      let ⟨k, hk⟩ := Nat.le.dest h
      hk ▸ hs.choose_finset_subset_add m k

    noncomputable def nat_inclusion : Nat → s
    | 0   =>
      have := hs.not_in_finset ∅
      ⟨choose this, (choose_spec this).left⟩
    | n+1 =>
      have := hs.not_in_finset (hs.choose_finset n)
      ⟨choose this, (choose_spec this).left⟩

    theorem nat_inclusion_notin (n : Nat) : (hs.nat_inclusion (n+1)).val ∉ hs.choose_finset n :=
      (choose_spec (hs.not_in_finset (hs.choose_finset n))).right

    theorem nat_inclusion_notin_lt {m n: Nat} (h : m < n) : (hs.nat_inclusion n).val ∉ hs.choose_finset m :=
      match n with
      | 0   => absurd h (Nat.not_lt_zero m)
      | n+1 => fun h' => absurd (hs.choose_finset_subset_le (Nat.le_of_succ_le_succ h) h')
        (hs.nat_inclusion_notin n)

    theorem nat_inclusion_cons (n : Nat) : hs.choose_finset (n+1) = (hs.choose_finset n).cons
      (hs.nat_inclusion (n+1)).val (hs.nat_inclusion_notin n) := rfl

    theorem nat_inclusion_in : (n : Nat) → (hs.nat_inclusion n).val ∈ hs.choose_finset n
    | 0   => Finset.mem_singleton.mpr rfl
    | n+1 => hs.nat_inclusion_cons n ▸ Finset.mem_cons_self _ _

    theorem nat_inclusion_le_injective {m n : Nat} (h₁ : m ≤ n) (h₂ : hs.nat_inclusion m = hs.nat_inclusion n) : m = n :=
      (Nat.lt_or_eq_of_le h₁).resolve_left (fun h₁ => absurd (h₂ ▸ hs.nat_inclusion_in m)
        (hs.nat_inclusion_notin_lt h₁))

    theorem nat_inclusion_injective : Function.injective hs.nat_inclusion :=
      fun m n h => Or.elim (Nat.le_total m n) (hs.nat_inclusion_le_injective · h)
        (fun h' => (hs.nat_inclusion_le_injective h' h.symm).symm)

  end infinite
end M4R
