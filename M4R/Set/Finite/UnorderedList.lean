import M4R.Set.Finite.Perm

def M4R.UnorderedList (α : Type u) : Type u := Quotient (Perm.PermSetoid α)

def List.to_UnorderedList (l : List α) : M4R.UnorderedList α := Quotient.mk l

namespace M4R
  namespace UnorderedList
    instance UnorderedListCoe : Coe (List α) (UnorderedList α) where coe := List.to_UnorderedList

    @[simp] theorem list_to_eq (l : List α) : l.to_UnorderedList = (↑l : UnorderedList α) := rfl
    @[simp] theorem list_coe_eq (l : List α) : Quotient.mk l = (↑l : UnorderedList α) := rfl
    @[simp] theorem list_coe_eq' (l : List α) : Quot.mk Perm l = (↑l : UnorderedList α) := rfl

    @[simp] theorem list_perm_eq {l₁ l₂ : List α} (h : l₁ ~ l₂) : (↑l₁ : UnorderedList α) = ↑l₂ :=
      Quot.sound h

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
    instance UnorderedListZero : Zero (UnorderedList α) where zero := UnorderedList.Empty
    @[simp] theorem empty_eq : (↑([] : List α) : UnorderedList α) = 0 := rfl

    protected def singleton (a : α) : UnorderedList α := ↑[a]
    @[simp] theorem singleton_eq (a : α) : List.to_UnorderedList [a] = UnorderedList.singleton a := rfl
    theorem singleton_eq_cons (a : α) : UnorderedList.singleton a = UnorderedList.cons a 0 := rfl

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

      @[simp] theorem add_zero (s : UnorderedList α) : s + 0 = s :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (a : UnorderedList α) => a + 0 = a) s
          (fun l => Quot.sound (by simp; exact Perm.refl _))

      @[simp] theorem zero_add (s : UnorderedList α) : 0 + s = s := by
        rw [comm, add_zero]

      theorem cons (a : α) (s : UnorderedList α) : s.cons a = [a] + s := rfl
      theorem cons' (a : α) (s : UnorderedList α) : s.cons a = s + [a] := by rw [comm, cons]

      theorem assoc (s t u : UnorderedList α) : s + t + u = s + (t + u) :=
        @Quotient.inductionOn₃ (List α) (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (a b c : UnorderedList α) => a + b + c = a + (b + c)) s t u
          (fun a b c => Quot.sound (by rw [List.append_assoc]; exact Perm.refl _))

      @[simp] theorem cons_over (a : α) (s t : UnorderedList α) : (s + t).cons a = s + (t.cons a) := by
        simp only [cons]; rw [←assoc, comm _ s, assoc]

      @[simp] theorem mem_add {a : α} {s t : UnorderedList α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
        @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (l₁ l₂ : UnorderedList α) => a ∈ l₁ + l₂ ↔ a ∈ l₁ ∨ a ∈ l₂) s t fun l₁ l₂ => List.mem_append

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

    section filter
    
      noncomputable def filter (p : α → Prop) (s : UnorderedList α) : UnorderedList α :=
        Quot.liftOn s (fun l => (l.filter' p : UnorderedList α))
          (fun l₁ l₂ h => Quot.sound (h.filter' p))

      @[simp] theorem filter_add (s t : UnorderedList α) : filter p (s + t) = filter p s + filter p t :=
        @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (l₁ l₂ : UnorderedList α) => filter p (l₁ + l₂) = filter p l₁ + filter p l₂) s t
          (fun l₁ l₂ => congrArg List.to_UnorderedList (List.filter'_append _ _))

      theorem nodup_filter (p : α → Prop) {l : UnorderedList α} : nodup l → nodup (filter p l) :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (s : UnorderedList α) =>
          nodup s → nodup (filter p s)) l fun l => List.nodup_filter' p

      @[simp] theorem filter_cons_of_pos {a : α} (s : UnorderedList α) :
        p a → filter p (s.cons a) = (filter p s).cons a :=
          @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
            p a → filter p (l.cons a) = (filter p l).cons a) s
            fun l h => congrArg List.to_UnorderedList (List.filter'_cons_of_pos l h)

      @[simp] theorem filter_cons_of_neg {a : α} (s : UnorderedList α) :
        ¬ p a → filter p (s.cons a) = filter p s :=
          @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
            ¬ p a → filter p (l.cons a) = filter p l) s
            fun l h => congrArg List.to_UnorderedList (List.filter'_cons_of_neg l h)

      @[simp] theorem mem_filter {a : α} {s : UnorderedList α} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          a ∈ filter p l ↔ a ∈ l ∧ p a) s fun l => List.mem_filter'
          
    end filter

    section ndunion

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

    end ndunion

    section ndinter

      noncomputable def ndinter (s t : UnorderedList α) : UnorderedList α := s.filter (· ∈ t)

      @[simp] theorem zero_ndinter (s : UnorderedList α) : ndinter 0 s = 0 := rfl

      @[simp] theorem cons_ndinter_of_mem {a : α} (s : UnorderedList α) {t : UnorderedList α} (h : a ∈ t) :
        ndinter (s.cons a) t = (ndinter s t).cons a := by simp [ndinter, h]

      @[simp] theorem ndinter_cons_of_not_mem {a : α} (s : UnorderedList α) {t : UnorderedList α} (h : a ∉ t) :
        ndinter (s.cons a) t = ndinter s t := by simp [ndinter, h]

      @[simp] theorem mem_ndinter {s t : UnorderedList α} {a : α} : a ∈ ndinter s t ↔ a ∈ s ∧ a ∈ t :=
        mem_filter

      @[simp] theorem nodup_ndinter {s : UnorderedList α} (t : UnorderedList α) : nodup s → nodup (ndinter s t) :=
        nodup_filter _

    end ndinter

    protected def le (s t : UnorderedList α) : Prop :=
        Quotient.liftOn₂ s t (· <+~ ·) (fun _ _ _ _ p₁ p₂ =>
          propext (p₂.subperm_left.trans p₁.subperm_right))

    namespace le
      instance UnorderedListle : LE (UnorderedList α) where le := UnorderedList.le

      protected theorem refl (a : UnorderedList α) : a ≤ a :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) => l ≤ l) a
          Perm.Subperm.refl
      
      protected theorem trans {a b c : UnorderedList α} : a ≤ b → b ≤ c → a ≤ c :=
        @Quotient.inductionOn₃ (List α) (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (l₁ l₂ l₃ : UnorderedList α) => l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃) a b c
          (fun l₁ l₂ l₃ => Perm.Subperm.trans)

      protected theorem antisymm {a b : UnorderedList α} : a ≤ b → b ≤ a → a = b :=
        @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (l₁ l₂ : UnorderedList α) => l₁ ≤ l₂ → l₂ ≤ l₁ → l₁ = l₂) a b
          (fun l₁ l₂ h₁ h₂ => Quot.sound (Perm.Subperm.antisymm h₁ h₂))

      protected theorem of_eq {a b : UnorderedList α} (h : a = b) : a ≤ b := by rw [h]; exact le.refl _

      @[simp] theorem subperm {l₁ l₂ : List α} : (l₁ : UnorderedList α) ≤ l₂ ↔ l₁ <+~ l₂ := Iff.rfl

      variable {s t : UnorderedList α} {a : α}

      theorem subset_of_le : s ≤ t → s ⊆ t :=
        @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (l₁ l₂ : UnorderedList α) => l₁ ≤ l₂ → l₁ ⊆ l₂) s t
          (fun l₁ l₂ h => Perm.Subperm.subset (le.subperm.mp h))

      theorem mem_of_le (h : s ≤ t) : a ∈ s → a ∈ t :=
        have := subset_of_le h
        @this a

      theorem not_mem_mono (h : s ⊆ t) : a ∉ t → a ∉ s := mt (@h _)

      theorem zero_le (s : UnorderedList α) : 0 ≤ s :=
        Quot.inductionOn s fun l => (List.Sublist.nil_sublist l).subperm

      theorem le_zero : s ≤ 0 ↔ s = 0 := ⟨fun h => le.antisymm h (zero_le _), le.of_eq⟩

      theorem le_induction_on {C : UnorderedList α → UnorderedList α → Prop}
        (h : s ≤ t) (H : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → C l₁ l₂) : C s t :=
          @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
            (fun (l₁ l₂ : UnorderedList α) => l₁ ≤ l₂ → C l₁ l₂) s t
            (fun l₁ l₂ ⟨l, p, s'⟩ => by simp; rw [←list_perm_eq p]; exact H s') h

      theorem nodup_of_le (h : s ≤ t) : nodup t → nodup s :=
        @le_induction_on α s t (fun a b => nodup b → nodup a)
          h List.nodup_of_sublist

      theorem cons_self (s : UnorderedList α) (a : α) : s ≤ s.cons a :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) => l ≤ l.cons a)
          s fun l => (List.Sublist.sublist_cons a l).subperm

      theorem cons_of_le {s t : UnorderedList α} (a : α) (h : s ≤ t) : s ≤ t.cons a :=
        le.trans h (cons_self t a)

      theorem cons_le_cons_iff (a : α) {s t : UnorderedList α} : s.cons a ≤ t.cons a ↔ s ≤ t :=
        @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (l₁ l₂ : UnorderedList α) => l₁.cons a ≤ l₂.cons a ↔ l₁ ≤ l₂) s t
          fun l₁ l₂ => Perm.Subperm.subperm_cons a

      theorem cons_le_cons (a : α) : s ≤ t → s.cons a ≤ t.cons a := (cons_le_cons_iff a).mpr

      theorem le_cons_of_not_mem (m : a ∉ s) : s ≤ t.cons a ↔ s ≤ t :=
        ⟨have : ∀ {t' : UnorderedList α} (h₁ : s ≤ t') (h₂ : a ∈ t'), s.cons a ≤ t' := by
          intro t' h; revert m;
          exact @le_induction_on α s t' (fun l₁ l₂ => a ∉ l₁ → a ∈ l₂ → l₁.cons a ≤ l₂) h (by
            intro l₁ l₂ s m₁ m₂; let ⟨r₁, r₂, h'⟩ := List.mem_split m₂; rw [h'] at s ⊢
            exact (Perm.middle a r₁ r₂).subperm_left.mpr ((Perm.Subperm.subperm_cons a).mpr ((List.Sublist.sublist_or_mem_of_sublist s).resolve_right m₁).subperm))
        fun h => (cons_le_cons_iff a).mp (this h (mem_cons_self _ _)),
        cons_of_le a⟩

      theorem add_self (s t : UnorderedList α) : s ≤ s + t :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          s ≤ s + l) t (fun l => by
            induction l with
            | nil => exact (by simp; exact le.refl _ : s ≤ s + 0)
            | cons a l ih => simp; rw [←append.cons_over]; exact cons_of_le a ih)

      theorem add_self' (s t : UnorderedList α) : s ≤ t + s := by
        rw [append.comm]; exact add_self s t

    end le

    open Classical

    protected noncomputable def erase (s : UnorderedList α) (a : α) : UnorderedList α :=
        Quotient.liftOn s (fun l => (l.erase a : UnorderedList α))
          fun l₁ l₂ p => list_perm_eq (p.erase a)

    namespace erase
      @[simp] theorem coe_erase (l : List α) (a : α) :
        (l : UnorderedList α).erase a = l.erase a := rfl

      @[simp] theorem erase_zero (a : α) : (0 : UnorderedList α).erase a = 0 := rfl

      @[simp] theorem erase_cons_head (a : α) (s : UnorderedList α) : (s.cons a).erase a = s :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) => (l.cons a).erase a = l)
          s fun l => congrArg List.to_UnorderedList (List.erase_cons_head a l)

      @[simp] theorem erase_cons_tail {a b : α} (s : UnorderedList α) (h : b ≠ a) :
        (s.cons b).erase a = (s.erase a).cons b :=
          @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) => (l.cons b).erase a = (l.erase a).cons b)
            s fun l => congrArg List.to_UnorderedList (List.erase_cons_tail l h)

      @[simp] theorem erase_of_not_mem {a : α} {s : UnorderedList α} : a ∉ s → s.erase a = s :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          a ∉ l → l.erase a = l) s fun l h => congrArg List.to_UnorderedList (List.erase_of_not_mem h)

      @[simp] theorem cons_erase {s : UnorderedList α} {a : α} : a ∈ s → (s.erase a).cons a = s :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          a ∈ l → (l.erase a).cons a = l) s fun l h => Quot.sound (Perm.cons_erase h).symm

      theorem le_cons_erase (s : UnorderedList α) (a : α) : s ≤ (s.erase a).cons a :=
        if h : a ∈ s then le.of_eq (cons_erase h).symm
        else by rw [erase_of_not_mem h]; apply le.cons_self

      theorem erase_le (a : α) (s : UnorderedList α) : s.erase a ≤ s :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          l.erase a ≤ l) s fun l => (List.erase_sublist a l).subperm

      theorem erase_le_iff_le_cons {s t : UnorderedList α} {a : α} : s.erase a ≤ t ↔ s ≤ t.cons a :=
        ⟨fun h => le.trans (erase.le_cons_erase _ _) (le.cons_le_cons _ h),
        fun h => if m : a ∈ s then by
          rw [←cons_erase m] at h; exact (le.cons_le_cons_iff _).mp h
        else le.trans (erase_le _ _) ((le.le_cons_of_not_mem m).1 h)⟩

    end erase

    protected noncomputable def sub (s t : UnorderedList α) : UnorderedList α :=
      Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.diff l₂ : UnorderedList α))
        (fun _ _ _ _ p₁ p₂ => Quot.sound (p₁.diff p₂))

    namespace sub
    
      noncomputable instance : Sub (UnorderedList α) where sub := UnorderedList.sub

      @[simp] protected theorem sub_zero (s : UnorderedList α) : s - 0 = s :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α)
          (fun (l : UnorderedList α) => l - 0 = l) s fun l => rfl

      @[simp] theorem sub_cons (a : α) (s t : UnorderedList α) : s - t.cons a = s.erase a - t :=
        @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (l₁ l₂ : UnorderedList α) => l₁ - l₂.cons a = l₁.erase a - l₂) s t
          fun l₁ l₂ => congrArg List.to_UnorderedList (List.diff_cons _ _ _)

      theorem sub_le_iff_le_add {s t : UnorderedList α} : s - t ≤ u ↔ s ≤ u + t := by
        revert s
        exact @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          ∀ s, s - l ≤ u ↔ s ≤ u + l) t (fun l => by
            induction l with
            | nil => exact fun s => (by simp : s - 0 ≤ u ↔ s ≤ u + 0)
            | cons a t ih =>
              intro s
              simp at ih
              simp [ih, erase.erase_le_iff_le_cons])

      theorem sub_le_iff_le_add' {s t : UnorderedList α} : s - t ≤ u ↔ s ≤ t + u := by
        rw [sub_le_iff_le_add, append.comm]; exact Iff.rfl
    
      theorem le_sub_add (s t : UnorderedList α) : s ≤ (s - t) + t :=
        sub.sub_le_iff_le_add.mp (le.refl _)

    end sub

    @[simp] theorem le.sub_le_self (s t : UnorderedList α) : s - t ≤ s :=
      sub.sub_le_iff_le_add'.mpr (le.add_self' s t)

    def card : UnorderedList α → Nat :=
      fun s => Quotient.liftOn s List.length fun l₁ l₂ => Perm.length_eq

    namespace card
      @[simp] theorem coe_card (l : List α) : card (l : UnorderedList α) = l.length := rfl

      @[simp] theorem zero : @card α 0 = 0 := rfl

      @[simp] theorem add (s t : UnorderedList α) : card (s + t) = card s + card t :=
        @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
          (fun (l₁ l₂ : UnorderedList α) => card (l₁ + l₂) = card l₁ + card l₂) s t
            List.length_append

      @[simp] theorem cons (a : α) (s : UnorderedList α) : card (s.cons a) = card s + 1 :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α)
          (fun (l : UnorderedList α) => card (l.cons a) = card l + 1) s fun l => rfl

      @[simp] theorem singleton (a : α) : card (UnorderedList.singleton a) = 1 := by
        simp only [singleton_eq_cons, zero, cons]

      theorem eq_one {s : UnorderedList α} : card s = 1 ↔ ∃ a, s = UnorderedList.singleton a :=
        ⟨@Quotient.inductionOn (List α) (Perm.PermSetoid α)
          (fun (l : UnorderedList α) => card l = 1 → ∃ a, l = UnorderedList.singleton a) s
          (fun l h => (List.length_eq_one.mp h).imp fun _ => congrArg List.to_UnorderedList),
        fun ⟨a, e⟩ => e.symm ▸ rfl⟩

      theorem le_of_le {s t : UnorderedList α} (h : s ≤ t) : card s ≤ card t :=
        @le.le_induction_on α s t (fun l₁ l₂ => card l₁ ≤ card l₂) h
          List.Sublist.length_le_of_sublist

      theorem pos_iff_exists_mem {s : UnorderedList α} : 0 < card s ↔ ∃ a, a ∈ s :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α)
          (fun (l : UnorderedList α) => 0 < card l ↔ ∃ a, a ∈ l) s
          (fun l => List.length_pos_iff_exists_mem)

    end card

    def countp (p : α → Prop) [DecidablePred p] (s : UnorderedList α) : Nat :=
      Quot.liftOn s (List.countp p) (fun l₁ l₂ => Perm.countp_eq p)

    namespace countp
      open Classical
      variable (p : α → Prop)

      @[simp] theorem coe_countp (l : List α) : countp p l = l.countp p := rfl

      @[simp] theorem zero : countp p 0 = 0 := rfl

      @[simp] theorem cons_of_pos {p} {a : α} (s : UnorderedList α) :
        p a → countp p (s.cons a) = countp p s + 1 :=
          @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
            p a → countp p (l.cons a) = countp p l + 1) s (List.countp_cons_of_pos p)

      @[simp] theorem cons_of_neg {p} {a : α} (s : UnorderedList α) :
        ¬ p a → countp p (s.cons a) = countp p s :=
          @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
            ¬ p a → countp p (l.cons a) = countp p l) s (List.countp_cons_of_neg p)

      theorem cons (b : α) (s) : countp p (s.cons b) = countp p s + (if p b then 1 else 0) := by
        byCases h : p b; simp [h]; simp [h]

      theorem countp_eq_card_filter (s : UnorderedList α) : countp p s = card (filter p s) :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α)
          (fun (l : UnorderedList α) => countp p l = card (filter p l)) s
            fun l => List.countp_eq_length_filter' _ _

      @[simp] theorem add (s t : UnorderedList α) : countp p (s + t) = countp p s + countp p t := by
        simp [countp_eq_card_filter]

      theorem pos {s : UnorderedList α} : 0 < countp p s ↔ ∃ a ∈ s, p a := by
        simp [countp_eq_card_filter, card.pos_iff_exists_mem]

    end countp

    noncomputable def count (a : α) : UnorderedList α → Nat := countp (Eq a)

    namespace count

      @[simp] theorem zero (a : α) : count a 0 = 0 := rfl

      @[simp] theorem cons_self (a : α) (s : UnorderedList α) : count a (s.cons a) = (count a s).succ :=
        countp.cons_of_pos _ rfl

      @[simp] theorem cons_of_ne {a b : α} (h : a ≠ b) (s : UnorderedList α) :
        count a (s.cons b) = count a s :=
          countp.cons_of_neg _ h

      theorem cons (a b : α) (s : UnorderedList α) :
        count a (s.cons b) = count a s + (if a = b then 1 else 0) := by
          byCases h : a = b; repeat simp [h]

      theorem singleton_self (a : α) : count a (UnorderedList.singleton a) = 1 := by
        simp only [cons_self, singleton_eq_cons, zero]

      theorem singleton (a b : α) : count a (UnorderedList.singleton b) = if a = b then 1 else 0 := by
        simp only [cons, singleton_eq_cons, zero, Nat.zero_add]

      @[simp] theorem add (a : α) : ∀ s t, count a (s + t) = count a s + count a t :=
          countp.add _

      theorem pos {a : α} {s : UnorderedList α} : 0 < count a s ↔ a ∈ s := by
        simp [count, countp.pos]
        exact ⟨fun ⟨x, xs, ax⟩ => by rw [ax]; exact xs, fun as => ⟨a, as, rfl⟩⟩

      @[simp] theorem eq_zero {a : α} {s : UnorderedList α} : count a s = 0 ↔ a ∉ s :=
        iff_not_comm.mp (pos.symm.trans Nat.pos_iff_ne_zero)

      @[simp] theorem erase_self (a : α) (s : UnorderedList α) :
        count a (s.erase a) = Nat.pred (count a s) := by
          byCases h : a ∈ s
          { rw [(by rw [erase.cons_erase h] : count a s = count a ((s.erase a).cons a)), cons_self]; simp }
          rw [erase.erase_of_not_mem h, eq_zero.mpr h]; rfl

      @[simp] theorem erase_of_ne {a b : α} (ab : a ≠ b) (s : UnorderedList α) :
        count a (s.erase b) = count a s := by
          byCases h : b ∈ s
          rw [←count.cons_of_ne ab, erase.cons_erase h]
          rw [erase.erase_of_not_mem h]

      @[simp] theorem sub (a : α) (s t : UnorderedList α) : count a (s - t) = count a s - count a t := by
        revert s;
        exact @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          ∀ (s : UnorderedList α), count a (s - l) = count a s - count a l) t
          (fun l => by
            induction l with
            | nil => intro; simp
            | cons b t ih =>
              intro s; have := ih (s.erase b)
              simp at this ⊢; rw [this]
              byCases ab : a = b
              { subst b; rw [count.erase_self, count.cons_self, Nat.sub_succ, Nat.pred_sub] }
              rw [erase_of_ne ab, cons_of_ne ab])

    end count

    theorem nodup_iff_count_le_one {s : UnorderedList α} : nodup s ↔ ∀ a, count a s ≤ 1 :=
      @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
        nodup l ↔ ∀ a, count a l ≤ 1) s fun l => List.nodup_iff_count_le_one

    theorem sub.mem_sub_of_nodup {a : α} {s t : UnorderedList α} (d : nodup s) :
      a ∈ s - t ↔ a ∈ s ∧ a ∉ t :=
        ⟨fun h => ⟨le.mem_of_le (le.sub_le_self _ _) h, fun h' =>
          count.eq_zero.mp (by
            rw [count.sub a s t, Nat.sub_eq_zero_iff_le]
            exact Nat.le_trans (nodup_iff_count_le_one.mp d a) (count.pos.mpr h')) h⟩,
        fun ⟨h₁, h₂⟩ => Or.resolve_right (append.mem_add.mp (le.mem_of_le (sub.le_sub_add  s t) h₁)) h₂⟩

  end UnorderedList
end M4R
