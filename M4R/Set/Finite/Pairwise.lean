import M4R.Set.Finite.List
import M4R.Numbers


inductive M4R.Pairwise (r : α → α → Prop) : List α → Prop
| nil  : Pairwise r []
| cons : ∀ {x : α} {l : List α}, (∀ a ∈ l, r x a) → Pairwise r l → Pairwise r (x::l)
    
def List.nodup : List α → Prop := M4R.Pairwise (fun x y => x ≠ y)

namespace M4R
  namespace Pairwise

    @[simp] theorem consIff {r : α → α → Prop} {a : α} {l : List α} :
      Pairwise r (a::l) ↔ (∀ a' ∈ l, r a a') ∧ Pairwise r l :=
        ⟨(fun x => by cases x with | cons p rl => exact ⟨p, rl⟩), (fun ⟨p, rl⟩ => rl.cons p)⟩

    theorem singleton (r : α → α → Prop) (a : α) : Pairwise r [a] := by
      simp only [consIff]; exact ⟨by intros; contradiction, nil⟩
      
    theorem appendIff {r : α → α → Prop} {l₁ l₂ : List α} : Pairwise r (l₁++l₂) ↔
      Pairwise r l₁ ∧ Pairwise r l₂ ∧ ∀ x ∈ l₁, ∀ y ∈ l₂, r x y := by
      induction l₁ with
      | nil =>
        apply Iff.intro; intro prl; apply And.intro Pairwise.nil; simp only [nil] at prl;
        apply And.intro prl; exact (fun x _ _ _ => by have := List.not_mem_nil x; contradiction)
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
          simp only [List.mem_append, Or.comm']; apply Iff.refl}
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

    theorem of_pairwise_map {r : α → α → Prop} {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → r a b)
      {l : List α} (p : Pairwise S (l.map f)) : Pairwise r l :=
        ((map f).mp p).imp H

    theorem map_of_pairwise {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
      (H : ∀ a b : α, r a b → s (f a) (f b)) {l : List α}
      (p : Pairwise r l) : Pairwise s (l.map f) := (map f).mpr (p.imp H)

    theorem pairwise_of_sublist {r : α → α → Prop} {l₁ l₂ : List α} : l₁ <+ l₂ → Pairwise r l₂ → Pairwise r l₁
    | List.Sublist.nil, h => h
    | List.Sublist.cons l₁ l₂ a s, Pairwise.cons i n => pairwise_of_sublist s n
    | List.Sublist.cons' l₁ l₂ a s, Pairwise.cons i n  =>
      (pairwise_of_sublist s n).cons fun a ha => i a (s.subset ha)

    theorem filter'_of_pairwise {r : α → α → Prop} (p : α → Prop) {l : List α}
      : Pairwise r l → Pairwise r (l.filter' p) := pairwise_of_sublist (List.filter'_sublist _)

  end Pairwise
end M4R

open M4R

namespace List

  @[simp] theorem nodup_nil : @nodup α [] := Pairwise.nil

  @[simp] theorem nodup_cons {a : α} {l : List α} : nodup (a::l) ↔ a ∉ l ∧ nodup l := by
    simp only [nodup, Pairwise.consIff, forall_mem_ne]; exact Iff.refl _

  theorem nodup_of_nodup_map (f : α → β) {l : List α} : nodup (map f l) → nodup l :=
    Pairwise.of_pairwise_map f fun a b => mt (congrArg f)

  theorem nodup_map_on {f : α → β} {l : List α} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (d : List.nodup l) : List.nodup (l.map f) :=
      Pairwise.map_of_pairwise f (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.mp d)

  theorem nodup_of_sublist {l₁ l₂ : List α} : l₁ <+ l₂ → l₂.nodup → l₁.nodup :=
    Pairwise.pairwise_of_sublist

  @[simp] theorem nodup_attach {l : List α} : nodup (attach l) ↔ nodup l :=
    ⟨fun h => attach_map_val l ▸ nodup_map_on (fun ⟨_, _⟩ _ ⟨_, _⟩ _ h => by rw [Subtype.mk.injEq]; exact h) h,
      fun h => nodup_of_nodup_map Subtype.val ((attach_map_val l).symm ▸ h)⟩

  theorem nodup_pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H : ∀ a ∈ l, p a}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : l.nodup) : nodup (l.pmap f H) := by
      rw [pmap_eq_map_attach]; exact nodup_map_on
        (fun ⟨a, ha⟩ ha' ⟨b, hb⟩ hb' h => by rw [Subtype.mk.injEq]; exact hf a (H _ ha) b (H _ hb) h)
        (nodup_attach.mpr h)

  open Classical

  theorem nodup_insert {a : α} {l : List α} (h : nodup l) : nodup (l.insert a) :=
    if h' : a ∈ l then by
      rw [insert_of_mem h']; exact h
    else by
      rw [insert_of_not_mem h', nodup_cons]; exact ⟨h', h⟩

  theorem nodup_union (l₁ : List α) {l₂ : List α} (h : l₂.nodup) : nodup (l₁ ∪ l₂) := by
    induction l₁ generalizing l₂ with
    | nil => exact h
    | cons a l ih =>
      apply nodup_insert; exact ih h

  theorem nodup_filter' (p : α → Prop) {l : List α} : nodup l → nodup (filter' p l) :=
    Pairwise.filter'_of_pairwise p

  theorem nodup_cons_of_nodup {a : α} {l : List α} (m : a ∉ l) (n : nodup l) : nodup (a::l) :=
    nodup_cons.mpr ⟨m, n⟩

  theorem not_mem_of_nodup_cons {a : α} {l : List α} (h : nodup (a::l)) : a ∉ l :=
    (nodup_cons.mp h).left

  theorem not_nodup_cons_of_mem {a : α} {l : List α} : a ∈ l → ¬ nodup (a :: l) :=
    imp_not_comm.mp not_mem_of_nodup_cons

  theorem not_nodup_pair (a : α) : ¬ nodup [a, a] :=
    not_nodup_cons_of_mem (List.self_singleton _)

  theorem nodup_iff_sublist {l : List α} : nodup l ↔ ∀ a, ¬ [a, a] <+ l :=
    ⟨fun d a h => not_nodup_pair a (nodup_of_sublist h d), by
      induction l with
      | nil => intros; exact nodup_nil
      | cons a l ih =>
        intro h;
        exact nodup_cons_of_nodup (fun al => h a ((Sublist.singleton_sublist.mpr al).cons_cons a))
          (ih fun a s => h a (Sublist.sublist_cons_of_sublist _ s))⟩

  theorem nodup_iff_count_le_one {l : List α} : l.nodup ↔ ∀ a : α, List.count a l ≤ 1 := by
    apply nodup_iff_sublist.trans
    have : (∀ (a : α), ¬[a, a] <+ l) = ∀ (a : α), count a l ≤ 1 := forall_congr fun a =>
      have : [a, a] <+ l ↔ 1 < count a l := (@count.le_count_iff_repeat_sublist _ a l (Nat.succ 1)).symm
      propext ((not_iff_not.mpr this).trans Nat.not_lt)
    rw [this]; exact Iff.rfl

end List
