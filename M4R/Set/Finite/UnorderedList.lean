import M4R.Set.Finite.Perm

def M4R.UnorderedList (α : Type u) : Type u := Quotient (Perm.PermSetoid α)

def List.to_UnorderedList (l : List α) : M4R.UnorderedList α := Quotient.mk l

namespace M4R
  namespace UnorderedList
    instance UnorderedListCoe : Coe (List α) (UnorderedList α) where coe := List.to_UnorderedList
    @[simp] theorem list_coe_eq (l : List α) : Quotient.mk l = (↑l : UnorderedList α) := rfl

    protected def mem (a : α) (s : UnorderedList α) : Prop :=
      Quot.liftOn s (fun l => a ∈ l) (fun l₁ l₂ (p : l₁ ~ l₂) => propext (p.mem_iff _))
    instance UnorderedListMem : Mem α (UnorderedList α) where mem := UnorderedList.mem

    def nodup (s : UnorderedList α) : Prop :=
      Quot.liftOn s List.nodup (fun l₁ l₂ p => propext p.nodupIff)

    protected def sizeOf [SizeOf α] (s : UnorderedList α) : Nat :=
      Quot.liftOn s sizeOf (fun _ _ => Perm.sizeOf_Eq_sizeOf)
    instance UnorderedListSizeOf : SizeOf (UnorderedList α) where sizeOf := UnorderedList.sizeOf

    protected def length (s : UnorderedList α) : Nat :=
      Quot.liftOn s List.length (fun _ _ => Perm.length_eq)

    protected def cons (a : α) (s : UnorderedList α) : UnorderedList α :=
      Quot.liftOn s (fun l => List.to_UnorderedList (a::l)) (fun _ _ p => Quot.sound (p.cons a))
    @[simp] theorem cons_eq (a : α) (l : List α) : ↑(a::l) = (↑l : UnorderedList α).cons a := rfl

    protected def Empty {α : Type _} : UnorderedList α := List.to_UnorderedList []
    instance EmptyUnorderedListEmptyCollection : EmptyCollection (UnorderedList α) where
      emptyCollection := UnorderedList.Empty
    instance UnorderedListZero : Zero (UnorderedList α) where zero := ∅
    @[simp] theorem empty_eq : (↑([] : List α) : UnorderedList α) = (∅ : UnorderedList α) := rfl

    protected def singleton (a : α) : UnorderedList α := ↑[a]
    @[simp] theorem singleton_eq (a : α) : List.to_UnorderedList [a] = UnorderedList.singleton a := rfl

    @[simp] theorem mem_cons {a b : α} {s : UnorderedList α} : a ∈ s.cons b ↔ a = b ∨ a ∈ s :=
      @Quotient.ind (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) => a ∈ l.cons b ↔ a = b ∨ a ∈ l)
        (fun l => Iff.refl _) s

    theorem mem_cons_of_mem {a b : α} {s : UnorderedList α} (h : a ∈ s) : a ∈ s.cons b :=
      mem_cons.mpr (Or.inr h)

    @[simp] theorem mem_cons_self (a : α) (s : UnorderedList α) : a ∈ s.cons a :=
      mem_cons.mpr (Or.inl rfl)

    protected def append (s t : UnorderedList α) : UnorderedList α :=
      Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁ ++ l₂ : List α).to_UnorderedList)
        fun v₁ v₂ w₁ w₂ p₁ p₂ => Quot.sound (p₁.append p₂)

    namespace append
      instance UnorderedListAdd : Add (UnorderedList α) where add := UnorderedList.append

      theorem comm (s t : UnorderedList α) : s + t = t + s := 
        @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (l₁ l₂ : UnorderedList α) => l₁ + l₂ = l₂ + l₁) s t (fun _ _ => Quot.sound (Perm.append_comm _ _))

      theorem add_zero (s : UnorderedList α) : s + 0 = s :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (a : UnorderedList α) => a + 0 = a) s
          (fun l => Quot.sound (by simp; exact Perm.refl _))

      theorem zero_add (s : UnorderedList α) : 0 + s = s := by
        rw [comm, add_zero]

      theorem cons (a : α) (s : UnorderedList α) : s.cons a = [a] + s := rfl
      theorem cons' (a : α) (s : UnorderedList α) : s.cons a = s + [a] := by rw [comm, cons]

      theorem assoc (s t u : UnorderedList α) : s + t + u = s + (t + u) :=
        @Quotient.inductionOn₃ (List α) (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (a b c : UnorderedList α) => a + b + c = a + (b + c)) s t u
          (fun a b c => Quot.sound (by rw [List.append_assoc]; exact Perm.refl _))

    end append

    protected theorem in_singleton {a a' : α} : a' ∈ UnorderedList.singleton a → a' = a :=
      List.in_singleton

    protected theorem self_singleton (a : α) : a ∈ UnorderedList.singleton a :=
      List.self_singleton a

    protected theorem cons' (a : α) (l : List α) : Quotient.mk (a :: l) = (↑l : UnorderedList α).cons a := rfl

    protected def map (f : α → β) (s : UnorderedList α) : UnorderedList β :=
      Quot.liftOn s (fun l : List α => ↑(l.map f))
        (fun l₁ l₂ p => Quot.sound (p.map f))
    
    @[simp] theorem map_nil (f : α → β) : UnorderedList.map f 0 = 0 := rfl
    
    namespace map

      @[simp] theorem cons (f : α → β) (a : α) (s : UnorderedList α) : (s.cons a).map f = (s.map f).cons (f a) :=
        @Quotient.ind (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) => (l.cons a).map f = (l.map f).cons (f a))
          (fun _ => rfl) s

      @[simp] theorem singleton (f : α → β) (a : α) : (UnorderedList.singleton a).map f = UnorderedList.singleton (f a) := rfl

      @[simp] theorem add (f : α → β) (l₁ l₂ : UnorderedList α) : (l₁ + l₂).map f = (l₁.map f) + (l₂.map f) :=
        @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (s t : UnorderedList α) => (s + t).map f = (s.map f) + (t.map f)) l₁ l₂
          (fun s t => congrArg List.to_UnorderedList (List.map_append f s t))

      @[simp] theorem mem_map {f : α → β} {b : β} {s : UnorderedList α} : b ∈ s.map f ↔ ∃ a, a ∈ s ∧ f a = b :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b) s (fun _ => List.mem_map)

    end map

    theorem nodup_map_on {f : α → β} {s : UnorderedList α} (H : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
      nodup s → nodup (s.map f) :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          (∀ (x : α), x ∈ l → ∀ (y : α), y ∈ l → f x = f y → x = y) → nodup l → nodup (l.map f))
            s (fun _ => List.nodup_map_on) H

    theorem nodup_map {f : α → β} {s : UnorderedList α} (hf : Function.injective f) :
      nodup s → nodup (s.map f) :=
        nodup_map_on (fun x _ y _ h => hf h)

    theorem nodup_ext {s t : UnorderedList α} : nodup s → nodup t → (s = t ↔ ∀ a, a ∈ s ↔ a ∈ t) :=
      @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
        (fun (s' t' : UnorderedList α) => nodup s' → nodup t' → (s' = t' ↔ ∀ a, a ∈ s' ↔ a ∈ t')) s t
        (fun l₁ l₂ h₁ h₂ => Quotient.eq.trans (Perm.ext h₁ h₂))

    inductive rel {α : Type _} {β : Type _} (r : α → β → Prop) : UnorderedList α → UnorderedList β → Prop
    | zero : rel r 0 0
    | cons {a b as bs} : r a b → rel r as bs → rel r (as.cons a) (bs.cons b)

    def pmap {p : α → Prop} (f : ∀ a, p a → β) (s : UnorderedList α) : (∀ a ∈ s, p a) → UnorderedList β :=
      @Quotient.recOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) => (∀ a ∈ l, p a) → UnorderedList β) s
        (fun l H => ↑(l.pmap f H)) (fun l₁ l₂ pp => by
          apply funext; intro h₂; have h₁ : ∀ a, a ∈ ↑l₁ → p a := fun a h => h₂ a (pp.subset h)
          have : ∀ (s₂ e H), @Eq.rec (UnorderedList α) l₁
            (fun l _ => (∀ a ∈ l, p a) → UnorderedList β) (fun _ => ↑(l₁.pmap f h₁))
            s₂ e H = ↑(l₁.pmap f h₁) := by
              intro _ e _; subst e; rfl
          have t₁ := this ↑l₂ (Quot.sound pp) h₂
          have t₂ := Quot.sound (@Perm.pmap _ _ _ f _ _ pp h₁ h₂)
          exact t₁.trans t₂)

    theorem nodup_pmap {p : α → Prop} {f : ∀ a, p a → β} {s : UnorderedList α} {H : ∀ a ∈ s, p a}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) : nodup s → nodup (pmap f s H) :=
      @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
        (h : ∀ a ∈ l, p a) → nodup l → nodup (pmap f l h)) s (fun l hl => List.nodup_pmap hf) H

    @[simp] theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β}
      {s : UnorderedList α} {H : ∀ a ∈ s, p a} {b : β} : b ∈ pmap f s H ↔ ∃ (a : α) (h : a ∈ s), f a (H a h) = b :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          (H' : ∀ a ∈ l, p a) → b ∈ pmap f l H' ↔ ∃ (a : α) (h : a ∈ l), f a (H' a h) = b) s
          (fun l h => List.mem_pmap) H

    noncomputable def ndunion (s t : UnorderedList α) : UnorderedList α :=
      @Quotient.liftOn₂ (List α) (List α) (UnorderedList α) (Perm.PermSetoid α) (Perm.PermSetoid α) s t
        (fun l₁ l₂ => ↑(l₁ ∪ l₂)) (fun _ _ _ _ p₁ p₂ => Quot.sound (p₁.union p₂))

    @[simp] theorem mem_ndunion {s t : UnorderedList α} {a : α} : a ∈ ndunion s t ↔ a ∈ s ∨ a ∈ t :=
      @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α) 
        (fun (l₁ l₂ : UnorderedList α) => a ∈ ndunion l₁ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂) s t
        (fun l₁ l₂ => List.mem_union)

    theorem nodup_ndunion (s : UnorderedList α) {t : UnorderedList α} : nodup t → nodup (ndunion s t) :=
      @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
        (fun (l₁ l₂ : UnorderedList α) => nodup l₂ → nodup (ndunion l₁ l₂)) s t
        (fun l₁ l₂ => List.nodup_union l₁)

    noncomputable def filter (p : α → Prop) (s : UnorderedList α) : UnorderedList α :=
      Quot.liftOn s (fun l => (l.filter' p : UnorderedList α))
        (fun l₁ l₂ h => Quot.sound (h.filter' p))

    theorem nodup_filter (p : α → Prop) {l : UnorderedList α} : nodup l → nodup (filter p l) :=
      @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (s : UnorderedList α) =>
        nodup s → nodup (filter p s)) l fun l => List.nodup_filter' p

    @[simp] theorem mem_filter {a : α} {s : UnorderedList α} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
      @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
        a ∈ filter p l ↔ a ∈ l ∧ p a) s fun l => List.mem_filter'

  end UnorderedList
end M4R
