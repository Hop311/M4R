import M4R.Set.Finite.Finset

namespace List

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

namespace M4R

  namespace UnorderedList
    def fold (f : α → β → α) (hrcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂)
      (init : α) (s : UnorderedList β) : α :=
        Quot.liftOn s (List.foldl f init) fun _ _ p => by
          induction p generalizing init with
          | nil => rfl
          | cons x _ h => exact h (f init x)
          | swap x y _ => simp only [List.foldl]; rw [hrcomm init x y]
          | trans _ _ h₁₂ h₂₃ => exact Eq.trans (h₁₂ init) (h₂₃ init)

    namespace fold

      variable (f : α → β → α) (hrcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂)
      
      @[simp] theorem empty (init : α) : fold f hrcomm init ∅ = init := rfl

      @[simp] theorem singleton (init : α) (b : β) : fold f hrcomm init (UnorderedList.singleton b) = f init b := rfl

      theorem append (init : α) (s t : UnorderedList β) :
        fold f hrcomm init (s + t) = fold f hrcomm (fold f hrcomm init s) t :=
          @Quotient.inductionOn₂ (List β) (List β) (Perm.PermSetoid β) (Perm.PermSetoid β)
            (fun (a b : UnorderedList β) => fold f hrcomm init (a + b) = fold f hrcomm (fold f hrcomm init a) b) s t
            (fun a b => List.foldl_append f _ a b)

      theorem cons (init : α) (x : β) (s : UnorderedList β) :
        fold f hrcomm init (s.cons x) = fold f hrcomm (f init x) s :=
          @Quotient.inductionOn (List β) (Perm.PermSetoid β) (fun (ms : UnorderedList β) =>
            fold f hrcomm init (ms.cons x) = fold f hrcomm (f init x) ms) s (fun l => rfl)

      theorem cons' (init : α) (x : β) (s : UnorderedList β) :
        fold f hrcomm init (s.cons x) = f (fold f hrcomm init s) x := by
          rw [cons, ←singleton f hrcomm _ x, ←singleton f hrcomm _ x, ←append, ←append, append.comm]

    end fold

    theorem hrcomm_of_comm_assoc {op : α → α → α} (hcomm : ∀ a₁ a₂, op a₁ a₂ = op a₂ a₁) (hassoc : ∀ a₁ a₂ a₃, op (op a₁ a₂) a₃ = op a₁ (op a₂ a₃)) :
      ∀ (a b c : α), op (op a c) b = op (op a b) c := fun a b c => by rw [hassoc, hcomm c, ←hassoc]

    def map_fold (op : α → α → α) (hcomm : ∀ a₁ a₂, op a₁ a₂ = op a₂ a₁) (hassoc : ∀ a₁ a₂ a₃, op (op a₁ a₂) a₃ = op a₁ (op a₂ a₃))
      (init : α) (f : β → α) (s : UnorderedList β) : α :=
        (s.map f).fold op (hrcomm_of_comm_assoc hcomm hassoc) init

    namespace map_fold
      variable (op : α → α → α) (hcomm : ∀ a₁ a₂, op a₁ a₂ = op a₂ a₁) (hassoc : ∀ a₁ a₂ a₃, op (op a₁ a₂) a₃ = op a₁ (op a₂ a₃))
      local infix:55 " ⋆ " => op

      @[simp] theorem empty (init : α) (f : β → α) : map_fold op hcomm hassoc init f ∅ = init := rfl

      theorem cons (init : α) (f : β → α) (s : UnorderedList β) (b : β):
        (s.cons b).map_fold op hcomm hassoc init f = (s.map_fold op hcomm hassoc init f) ⋆ (f b) := by
          simp [map_fold, fold.cons'];

      theorem distrib (init : α) (f g : β → α) (s : UnorderedList β) :
        init ⋆ s.map_fold op hcomm hassoc init (fun b => f b ⋆ g b) =
          (s.map_fold op hcomm hassoc init f) ⋆ (s.map_fold op hcomm hassoc init g) :=
            @Quotient.inductionOn (List β) (Perm.PermSetoid β) (fun (l : UnorderedList β) =>
              init ⋆ l.map_fold op hcomm hassoc init (fun b => f b ⋆ g b) =
                (l.map_fold op hcomm hassoc init f) ⋆ (l.map_fold op hcomm hassoc init g)) s
              (fun l => by
                induction l with
                | nil => simp
                | cons x l ih =>
                  simp [cons]; simp only [list_coe_eq] at ih
                  (conv => rhs; rw [hassoc, ←hassoc (f x), hcomm (f x), hassoc _ (f x), ←hassoc])
                  rw [←ih, hassoc])

    end map_fold
  end UnorderedList
  namespace Finset

    def fold (f : α → β → α) (hcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂)
      (init : α) (s : Finset β) : α := UnorderedList.fold f hcomm init s.elems

    namespace fold
      variable (f : α → β → α) (hcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂)
      
      @[simp] theorem empty (init : α) : Finset.fold f hcomm init ∅ = init := rfl

      @[simp] theorem singleton (init : α) (b : β) : fold f hcomm init (Finset.singleton b) = f init b := rfl

    end fold
  end Finset
end M4R