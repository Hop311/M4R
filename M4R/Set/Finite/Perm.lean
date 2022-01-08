import M4R.Set.Basic
import M4R.Set.Finite.Pairwise

import M4R.Function

namespace M4R

  inductive Perm : List α → List α → Prop
  | nil                           : Perm [] []
  | cons (x : α) {l₁ l₂ : List α} : Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
  | swap (x y : α) (l : List α)   : Perm (y::x::l) (x::y::l)
  | trans {l₁ l₂ l₃ : List α}     : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

  infix:50 " ~ " => Perm
  
  namespace Perm

    protected theorem refl : ∀ (x : List α), x ~ x
    | []      => Perm.nil
    | (x::xl) => (Perm.refl xl).cons x
    
    protected theorem symm {x y : List α} (h : x ~ y) : y ~ x := 
      @Perm.recOn α (fun (a b : List α) _ => b ~ a) x y h
        Perm.nil
        (fun x _ _ _ r₁ => r₁.cons x)
        (fun x y l => swap y x l)
        (fun _ _ p₂₁ p₃₂ => p₃₂.trans p₂₁)
    
    instance PermEquivalence : Equivalence (@Perm α) where
    refl  := Perm.refl
    symm  := Perm.symm
    trans := Perm.trans

    instance PermSetoid (α : Type _) : Setoid (List α) where
      r := Perm
      iseqv := PermEquivalence

    theorem subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ :=
      fun x => @Perm.recOn α (fun (a b : List α) _ => x ∈ a → x ∈ b) l₁ l₂ p id
          (fun y a b _ xab xya => Or.elim xya
            (fun exy => Or.inl exy)
            (fun xa => Or.inr (xab xa)))
          (fun y z a xzya => Or.elim xzya
              (fun exz => Or.inr (Or.inl exz))
              (fun xya => Or.elim xya
                  (fun exy => Or.inl exy)
                  (fun xa => Or.inr (Or.inr xa))))
          (fun _ _ x₁₂ x₂₃ x₁ => x₂₃ (x₁₂ x₁))

    theorem memIff {a : α} {l₁ l₂ : List α} (p : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
      Iff.intro (fun x => p.subset x) (fun x => p.symm.subset x)
    
    theorem append_right {l₁ l₂ : List α} (t : List α) (p : l₁ ~ l₂) : l₁++t ~ l₂++t :=
      @Perm.recOn α (fun a b pab => a++t ~ b++t) _ _ p
        (Perm.refl ([] ++ t))
        (fun x _ _ _ r₁ => r₁.cons x)
        (fun x y _ => swap x y _)
        (fun _ _ r₁ r₂ => r₁.trans r₂)

    theorem append_left {t₁ t₂ : List α} (l : List α) (p : t₁ ~ t₂) : l++t₁ ~ l++t₂ :=
      match l with
      | [] => p
      | x::xs => (append_left xs p).cons x

    theorem append {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁++t₁ ~ l₂++t₂ :=
      (p₁.append_right t₁).trans (p₂.append_left l₂)

    theorem middle (a : α) : ∀ (l₁ l₂ : List α), l₁++a::l₂ ~ a::(l₁++l₂)
    | []     , l₂ => Perm.refl _
    | (b::l₁), l₂ => ((@middle α a l₁ l₂).cons b).trans (swap a b _)
    
    theorem append_singleton (a : α) (l : List α) : l ++ [a] ~ a::l := by
      have := middle a l []
      rw [List.append_nil] at this
      exact this

    theorem append_comm  (l₁ l₂ : List α) : (l₁++l₂) ~ (l₂++l₁) :=
      match l₁ with
      | []     => by simp; exact Perm.refl l₂
      | (a::t) => ((append_comm t l₂).cons a).trans (middle a l₂ t).symm

    theorem lengthEq {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.length = l₂.length :=
      @Perm.recOn α (fun (a b : List α) _ => a.length = b.length) l₁ l₂ p rfl
        (fun _ _ _ _ h => by simp[h])
        (fun _ _ _ => by simp)
        (fun _ _ r₁₂ r₂₃ => Eq.trans r₁₂ r₂₃)

    theorem eqNil {l : List α} (p : l ~ []) : l = [] :=
      List.eqNilOfLengthEqZero p.lengthEq
    theorem nilEq {l : List α} (p : [] ~ l) : l = [] :=
      eqNil p.symm

    theorem inductionOn (motive : List α → List α → Prop) {l₁ l₂ : List α} (p : l₁ ~ l₂)
      (h₁ : motive [] [])
      (h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → motive l₁ l₂ → motive (x::l₁) (x::l₂))
      (h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → motive l₁ l₂ → motive (y::x::l₁) (x::y::l₂))
      (h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → motive l₁ l₂ → motive l₂ l₃ → motive l₁ l₃) : motive l₁ l₂ := by
        have P_refl : ∀ l, motive l l :=
          fun l => @List.recOn α (fun x => motive x x) l h₁ (fun x xs ih => h₂ x xs xs (Perm.refl xs) ih)
        exact Perm.recOn p h₁ h₂ (fun x y l => h₃ x y l l (Perm.refl l) (P_refl l)) (h₄ _ _ _)

    theorem invCore {a : α} {l₁ l₂ r₁ r₂ : List α} : l₁++a::r₁ ~ l₂++a::r₂ → l₁++r₁ ~ l₂++r₂ := by
      generalize e₁ : l₁++a::r₁ = s₁; generalize e₂ : l₂++a::r₂ = s₂;
      intro p; revert l₁ l₂ r₁ r₂ e₁ e₂;
      apply inductionOn (fun (t₁ t₂ : List α) => ∀ {l₁' l₂' r₁' r₂' : List α},
        l₁'++a::r₁' = t₁ → l₂'++a::r₂' = t₂ → l₁'++r₁' ~ l₂'++r₂') p
      { intro l₁ _ r₁ _ e₁ _
        have h₀ := List.notMemNil a; rw [←e₁] at h₀
        have : a ∈ l₁ ++ a :: r₁ := by apply (memIff (middle a l₁ r₁)).mpr; apply Or.inl; rfl
        contradiction }
      { intro _ _ _ p₁₂ ih l₁ l₂ _ _ e₁ e₂;
        match l₁, l₂ with
        | [], [] =>
          simp at *; rw [e₁.right, e₂.right]; exact p₁₂
        | [], List.cons _ _ =>
          simp at *; rw [e₂.left, e₁.right, ←e₁.left]; apply trans p₁₂; rw [←e₂.right]; exact middle _ _ _
        | List.cons _ _, [] =>
          simp at *; rw [e₁.left, ←e₂.left, e₂.right]; apply Perm.symm; apply trans p₁₂.symm;
            rw [←e₁.right]; exact middle _ _ _
        | List.cons _ _, List.cons z l₂ =>
          simp at *; rw [e₁.left, e₂.left]; exact cons _ (ih e₁.right e₂.right) }
      { intro _ _ _ _ p₁₂ ih l₁ l₂ _ _ e₁ e₂
        match l₁, l₂ with
        | [], [] =>
          simp at *; rw [e₁.right, e₂.right, ←e₁.left, e₂.left]; exact Perm.cons _ p₁₂
        | [], List.cons _ l₂ =>
          match l₂ with
          | [] =>
            simp at *; rw [e₁.right, e₂.left, e₂.right.right]; exact Perm.cons _ p₁₂
          | List.cons _ _ =>
            simp at *; rw [e₁.right, e₂.left, e₂.right.left, ←e₁.left]; apply cons;
              apply trans p₁₂; rw [←e₂.right.right]; exact middle _ _ _
        | List.cons _ l₁, [] =>
          match l₁ with
          | [] =>
            simp at *; rw [e₁.right.right, e₂.right, e₁.left]; exact Perm.cons _ p₁₂
          | List.cons _ l₂ =>
            simp at *; rw [e₂.right, e₁.left, e₁.right.left, ←e₂.left]; apply cons;
              apply Perm.symm; apply trans p₁₂.symm; rw [←e₁.right.right]; exact middle _ _ _
        | List.cons _ l₁, List.cons _ l₂ =>
          match l₁, l₂ with
          | [], [] =>
            simp at *; rw [e₁.left, e₂.left, ←e₁.right.left, ←e₂.right.left, e₁.right.right, e₂.right.right]
              exact cons _ p₁₂
          | [], List.cons _ _ =>
            simp at *; rw [e₁.left, e₂.left, ←e₁.right.left, e₂.right.left, e₁.right.right];
              apply trans (cons _ p₁₂); rw [←e₂.right.right]; apply Perm.symm; apply trans (swap _ _ _);
                apply cons; apply Perm.symm; exact middle _ _ _
          | List.cons _ _, [] =>
            simp at *; rw [e₁.left, e₂.left, e₁.right.left, ←e₂.right.left]; apply trans (swap _ _ _); apply cons;
              rw [e₂.right.right]; apply Perm.symm; apply trans p₁₂.symm; rw [←e₁.right.right]; exact middle _ _ _
          | List.cons _ _, List.cons _ _ =>
            simp at *; rw [e₁.left, e₂.left, e₁.right.left, e₂.right.left]; apply trans (swap _ _ _); apply cons;
              apply cons; exact ih e₁.right.right e₂.right.right }
      { intro _ t₂ _ p₁₂ p₂₃ ih₁ ih₂ l₁ _ r₁ _ e₁ e₃;
          rw [←e₁] at p₁₂; rw [←e₃] at p₂₃;
          have : a ∈ t₂ := p₁₂.subset (by apply (memIff (middle a l₁ r₁)).mpr; apply Or.inl; rfl)
          let ⟨l₂, r₂, e₂⟩ := List.memSplit this;
          exact trans (ih₁ e₁ e₂.symm) (ih₂ e₂.symm e₃) }

    theorem consInv {a : α} {l₁ l₂ : List α} : a::l₁ ~ a::l₂ → l₁ ~ l₂ :=
      @invCore _ _ [] [] _ _

    theorem pairwiseIff {r : α → α → Prop} (h : ∀ a b, r a b → r b a) :
      ∀ {l₁ l₂ : List α} (p : l₁ ~ l₂), Pairwise r l₁ ↔ Pairwise r l₂ := by
      have : ∀ {l₁ l₂}, l₁ ~ l₂ → Pairwise r l₁ → Pairwise r l₂ := by
        intro l₁ l₂ p₁₂ pwl₁;
        induction pwl₁ generalizing l₂ with
        | nil => rw [p₁₂.nilEq]; constructor
        | @cons a l₃ hl₃ pwl₃ ih =>
          let ⟨s, t, e⟩ := List.memSplit (p₁₂.subset (List.mem_cons_self a l₃));
          rw [e, Pairwise.middle, Pairwise.consIff]; rw [e] at p₁₂;
          have p' : l₃ ~ s ++ t := (p₁₂.trans (middle _ _ _)).consInv;
          exact And.intro (fun x xst => hl₃ x ((memIff p').mpr xst)) (ih p')
          exact h
      exact fun _ _ p => ⟨this p, this p.symm⟩

    theorem nodupIff {l₁ l₂ : List α} : l₁ ~ l₂ → (List.nodup l₁ ↔ List.nodup l₂) :=
      pairwiseIff (@Ne.symm α)

    theorem sizeOf_Eq_sizeOf {l₁ l₂ : List α} (h : l₁ ~ l₂) :
      sizeOf l₁ = sizeOf l₂ := by
      induction h with
      | nil => rfl
      | cons _ _ h => rw [List.sizeOf_cons, List.sizeOf_cons, h]
      | swap _ _ _ => rw [List.sizeOf_cons, List.sizeOf_cons, List.sizeOf_cons, List.sizeOf_cons]
      | trans _ _ h₁ h₂ => exact Eq.trans h₁ h₂

    theorem filterMap (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
      List.filterMap f l₁ ~ List.filterMap f l₂ := by
        induction p with
        | nil => simp only [List.filterMap]; exact Perm.nil
        | cons x p ih =>
          simp only [List.filterMap]
          cases f x with
          | none => exact ih
          | some a => exact cons a ih;
        | swap x y l =>
          simp only [List.filterMap]
          cases f x with
          | none =>
            cases f y with
            | none => exact Perm.refl _
            | some b => exact Perm.cons b (Perm.refl _)
          | some a =>
            cases f y with
            | none => exact Perm.refl _
            | some b => exact Perm.swap a b _
        | trans p₁₂ p₂₃ ih₁₂ ih₂₃ => exact ih₁₂.trans ih₂₃

    theorem map (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.map f ~ l₂.map f := by
      rw [←List.filterMap_Eq_map f]; exact filterMap (some ∘ f) p

  end Perm

  def UnorderedList (α : Type u) : Type u := Quotient (Perm.PermSetoid α)
end M4R

def List.to_UnorderedList (l : List α) : M4R.UnorderedList α := Quotient.mk l

namespace M4R
  namespace UnorderedList
    instance UnorderedListCoe : Coe (List α) (UnorderedList α) where coe := List.to_UnorderedList

    protected def mem (a : α) (s : UnorderedList α) : Prop :=
      Quot.liftOn s (fun l => a ∈ l) (fun l₁ l₂ (p : l₁ ~ l₂) => propext (p.memIff))
    instance UnorderedListMem : Mem α (UnorderedList α) where mem := UnorderedList.mem
  
    def nodup (s : UnorderedList α) : Prop :=
      Quot.liftOn s List.nodup (fun l₁ l₂ p => propext p.nodupIff)

    protected def sizeOf [SizeOf α] (s : UnorderedList α) : Nat :=
      Quot.liftOn s sizeOf (fun _ _ => Perm.sizeOf_Eq_sizeOf)
    instance UnorderedListSizeOf : SizeOf (UnorderedList α) where sizeOf := UnorderedList.sizeOf

    protected def length (s : UnorderedList α) : Nat :=
      Quot.liftOn s List.length (fun _ _ => Perm.lengthEq)

    protected def map (f : α → β) (s : UnorderedList α) : UnorderedList β := by
      apply Quot.liftOn s (fun l : List α => List.to_UnorderedList (l.map f))
        (fun l₁ l₂ p => Quot.sound (p.map f))

    protected def cons (a : α) (s : UnorderedList α) : UnorderedList α :=
      Quot.liftOn s (fun l => List.to_UnorderedList (a::l)) (fun _ _ p => Quot.sound (p.cons a))

    protected def Empty {α : Type _} : UnorderedList α := List.to_UnorderedList []
    instance UnorderedListZero : Zero (UnorderedList α) where zero := UnorderedList.Empty

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

    end append

    theorem nodup_map_on {f : α → β} {s : UnorderedList α} (H : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
      nodup s → nodup (s.map f) := by
        apply @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
          (∀ (x : α), x ∈ l → ∀ (y : α), y ∈ l → f x = f y → x = y) → nodup l → nodup (l.map f))
            s (fun _ => List.nodup_map_on) H;

    theorem nodup_map {f : α → β} {s : UnorderedList α} (hf : Function.injective f) :
      nodup s → nodup (s.map f) :=
        nodup_map_on (fun x _ y _ h => hf h)

    def fold (f : α → β → α) (hcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂) :
      (init : α) → UnorderedList β → α := fun init s =>
        Quot.liftOn s (fun l => l.foldl f init) fun _ _ p => by
          induction p generalizing init with
          | nil => rfl
          | cons x _ h => exact h (f init x)
          | swap x y _ => simp only [List.foldl]; rw [hcomm init x y]
          | trans _ _ h₁₂ h₂₃ => exact Eq.trans (h₁₂ init) (h₂₃ init)

    namespace fold
      variable (f : α → β → α) (hcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂)
      
      theorem empty (init : α) : fold f hcomm init UnorderedList.Empty = init := rfl

      theorem cons (init : α) (x : β) (s : UnorderedList β) :
        fold f hcomm init (s.cons x) = fold f hcomm (f init x) s :=
          @Quotient.inductionOn (List β) (Perm.PermSetoid β) (fun (ms : UnorderedList β) =>
            fold f hcomm init (ms.cons x) = fold f hcomm (f init x) ms) s (fun l => rfl)
        
      theorem append (init : α) (s t : UnorderedList β) :
        fold f hcomm init (s + t) = fold f hcomm (fold f hcomm init s) t :=
          @Quotient.inductionOn₂ (List β) (List β) (Perm.PermSetoid β) (Perm.PermSetoid β)
            (fun (a b : UnorderedList β) => fold f hcomm init (a + b) = fold f hcomm (fold f hcomm init a) b) s t
            (fun a b => List.foldl_append f _ a b)

    end fold
  end UnorderedList
end M4R