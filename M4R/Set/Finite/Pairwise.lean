import M4R.Notation
import M4R.Logic

namespace M4R

  protected def List.mem (a : α) : List α → Prop
  | []   => False
  | b::l => a = b ∨ l.mem a
  instance List.ListMem : Mem α (List α) where mem := List.mem
  
  inductive Pairwise (r : α → α → Prop) : List α → Prop
  | nil  : Pairwise r []
  | cons : ∀ {x : α} {l : List α}, (∀ a ∈ l, r x a) → Pairwise r l → Pairwise r (x::l)
    
  namespace List

    protected def sizeOf : List α → Nat := List.lengthTR
    instance ListSizeOf : SizeOf (List α) where sizeOf := List.sizeOf

    @[simp] theorem sizeOf_cons (a : α) (as : List α) : sizeOf (a::as) = (sizeOf as).succ := by
      simp only [sizeOf, List.sizeOf]; rw [←List.length_eq_lenghtTR, List.length_cons]

    protected def nodup : List α → Prop := Pairwise (fun x y => x ≠ y)

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

  end List
  namespace Pairwise

    @[simp] theorem consIff {r : α → α → Prop} {a : α} {l : List α} :
      Pairwise r (a::l) ↔ (∀ a' ∈ l, r a a') ∧ Pairwise r l :=
        ⟨(fun x => by cases x with | cons p rl => exact ⟨p, rl⟩), (fun ⟨p, rl⟩ => rl.cons p)⟩

    theorem appendIff {r : α → α → Prop} {l₁ l₂ : List α} : Pairwise r (l₁++l₂) ↔
      Pairwise r l₁ ∧ Pairwise r l₂ ∧ ∀ x ∈ l₁, ∀ y ∈ l₂, r x y := by
      induction l₁ with
      | nil =>
        apply Iff.intro; intro prl; apply And.intro Pairwise.nil; simp only [nil] at prl;
        apply And.intro prl; exact (fun x _ _ _ => by have := List.notMemNil x; contradiction)
        exact (fun x => x.right.left)
      | cons x l₁ IH =>
        simp; apply Iff.intro;
        intro h; apply And.intro;
        exact And.intro (fun y yl => h.left y (Or.inl yl)) (IH.mp h.right).left;
        apply And.intro; exact (IH.mp h.right).right.left;
        intro a axl b; apply Or.elim axl; intro ax bl; rw [ax]; exact h.left b (Or.inr bl);
        intro al bl; exact (IH.mp h.right).right.right a al b bl;
        intro h; apply And.intro; intro a all; apply Or.elim all (h.left.left a);
        apply h.right.right x (List.mem_cons_self x l₁) a;
        apply IH.mpr; apply And.intro h.left.right; apply And.intro h.right.left;
        intro _ al _ bl; apply h.right.right; exact Or.inr al; exact bl

    theorem appendComm {r : α → α → Prop} (h : ∀ a b, r a b → r b a) {l₁ l₂ : List α} :
      Pairwise r (l₁++l₂) ↔ Pairwise r (l₂++l₁) := by
      have : ∀ s t : List α, Pairwise r (s++t) → Pairwise r (t++s) := by
        intro s t p; rw [appendIff] at *; apply And.intro p.right.left; apply And.intro p.left;
        intro x xt y ys; exact h y x (p.right.right y ys x xt);
      exact ⟨this l₁ l₂, this l₂ l₁⟩;

    theorem middle {r : α → α → Prop} (h : ∀ a b, r a b → r b a) {a : α} {l₁ l₂ : List α} :
      Pairwise r (l₁ ++ a::l₂) ↔ Pairwise r (a::(l₁++l₂)) := by
        have : Pairwise r (l₁ ++ ([a] ++ l₂)) ↔ Pairwise r ([a] ++ l₁ ++ l₂) := by
          {rw [←List.append_assoc, appendIff, @appendIff _ _ ([a] ++ l₁), appendComm h];
          simp only [List.memAppend, Or.comm']; apply Iff.refl}
        simp only [List.appendSingleton] at this; exact this

    theorem imp_of_mem {r s : α → α → Prop} {l : List α}
      (h : ∀ {a b}, a ∈ l → b ∈ l → r a b → s a b) (p : Pairwise r l) : Pairwise s l := by
      induction p with
      | nil => exact nil
      | @cons a l lr p ih =>
        constructor; exact fun b bl => h (List.mem_cons_self a l) (Or.inr bl) (lr b bl);
        exact ih (fun xl yl => h (Or.inr xl) (Or.inr yl))

    theorem imp {r s : α → α → Prop} (h : ∀ a b, r a b → s a b) {l : List α} :
      Pairwise r l → Pairwise s l := imp_of_mem (fun _ _ => h _ _)

    theorem iff_of_mem {r s : α → α → Prop} {l : List α} (H : ∀ {a b}, a ∈ l → b ∈ l → (r a b ↔ s a b)) :
      Pairwise r l ↔ Pairwise s l :=
        ⟨imp_of_mem (fun al bl => (H al bl).mp),
        imp_of_mem (fun al bl => (H al bl).mpr)⟩

    theorem and_mem {r : α → α → Prop} {l : List α} : Pairwise r l ↔ Pairwise (fun x y => x ∈ l ∧ y ∈ l ∧ r x y) l := by
      apply iff_of_mem (fun al bl => ⟨fun rab => ⟨al, bl, rab⟩, fun ⟨_, _, rab⟩ => rab⟩);

    theorem map {r : α → α → Prop} (f : β → α) : ∀ {l : List β},
      Pairwise r (l.map f) ↔ Pairwise (fun a b : β => r (f a) (f b)) l
    | []     => by simp only [List.map, Pairwise.nil]
    | b::l => by
      have : (∀ a b', b' ∈ l → f b' = a → r (f b) a) ↔ ∀ (b' : β), b' ∈ l → r (f b) (f b') := by
        apply Iff.intro (fun h x xl => h (f x) x xl rfl);
        intro h _ y yl eq; rw [←eq]; exact h y yl;
      simp [List.map, consIff, List.mem_map, exists_imp_distrib, and_imp, this, map];

    theorem map_of_pairwise {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
      (H : ∀ a b : α, r a b → s (f a) (f b)) {l : List α}
      (p : Pairwise r l) : Pairwise s (l.map f) := (map f).2 (p.imp H)

  end Pairwise

  namespace List
    
    theorem nodup_map_on {f : α → β} {l : List α} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
      (d : List.nodup l) : List.nodup (l.map f) :=
        Pairwise.map_of_pairwise f (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.mp d)

  end List
end M4R