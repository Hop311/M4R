import M4R.Set.Finite.Perm

def M4R.UnorderedList (α : Type u) : Type u := Quotient (Perm.PermSetoid α)

def List.to_UnorderedList (l : List α) : M4R.UnorderedList α := Quotient.mk l

namespace M4R
  namespace UnorderedList
    instance UnorderedListCoe : Coe (List α) (UnorderedList α) where coe := List.to_UnorderedList

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

    protected def Empty {α : Type _} : UnorderedList α := List.to_UnorderedList []
    instance EmptyUnorderedListEmptyCollection : EmptyCollection (UnorderedList α) where
      emptyCollection := UnorderedList.Empty
    instance UnorderedListZero : Zero (UnorderedList α) where zero := ∅

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

    end map

    theorem nodup_map_on {f : α → β} {s : UnorderedList α} (H : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
      nodup s → nodup (s.map f) :=
        @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          (∀ (x : α), x ∈ l → ∀ (y : α), y ∈ l → f x = f y → x = y) → nodup l → nodup (l.map f))
            s (fun _ => List.nodup_map_on) H

    theorem nodup_map {f : α → β} {s : UnorderedList α} (hf : Function.injective f) :
      nodup s → nodup (s.map f) :=
        nodup_map_on (fun x _ y _ h => hf h)

    def fold (f : α → β → α) (hcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂) :
      (init : α) → UnorderedList β → α := fun init s =>
        Quot.liftOn s (List.foldl f init) fun _ _ p => by
          induction p generalizing init with
          | nil => rfl
          | cons x _ h => exact h (f init x)
          | swap x y _ => simp only [List.foldl]; rw [hcomm init x y]
          | trans _ _ h₁₂ h₂₃ => exact Eq.trans (h₁₂ init) (h₂₃ init)

    namespace fold
      variable (f : α → β → α) (hcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂)
      
      @[simp] theorem empty (init : α) : fold f hcomm init ∅ = init := rfl

      @[simp] theorem singleton (init : α) (b : β) : fold f hcomm init (UnorderedList.singleton b) = f init b := rfl

      theorem append (init : α) (s t : UnorderedList β) :
        fold f hcomm init (s + t) = fold f hcomm (fold f hcomm init s) t :=
          @Quotient.inductionOn₂ (List β) (List β) (Perm.PermSetoid β) (Perm.PermSetoid β)
            (fun (a b : UnorderedList β) => fold f hcomm init (a + b) = fold f hcomm (fold f hcomm init a) b) s t
            (fun a b => List.foldl_append f _ a b)

      theorem cons (init : α) (x : β) (s : UnorderedList β) :
        fold f hcomm init (s.cons x) = fold f hcomm (f init x) s :=
          @Quotient.inductionOn (List β) (Perm.PermSetoid β) (fun (ms : UnorderedList β) =>
            fold f hcomm init (ms.cons x) = fold f hcomm (f init x) ms) s (fun l => rfl)

      theorem cons' (init : α) (x : β) (s : UnorderedList β) :
        fold f hcomm init (s.cons x) = f (fold f hcomm init s) x := by
          rw [cons, ←singleton f hcomm _ x, ←singleton f hcomm _ x, ←append, ←append, append.comm]

    end fold

    theorem nodup_ext {s t : UnorderedList α} : nodup s → nodup t → (s = t ↔ ∀ a, a ∈ s ↔ a ∈ t) :=
      @Quotient.inductionOn₂ (List α) (List α) (Perm.PermSetoid α) (Perm.PermSetoid α)
        (fun (s' t' : UnorderedList α) => nodup s' → nodup t' → (s' = t' ↔ ∀ a, a ∈ s' ↔ a ∈ t')) s t
        (fun l₁ l₂ h₁ h₂ => Quotient.eq.trans (Perm.ext h₁ h₂))

  end UnorderedList
end M4R
