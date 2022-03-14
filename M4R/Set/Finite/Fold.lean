import M4R.Set.Finite.Finset

namespace M4R

  variable (f : α → β → α) (hrcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂)

  variable (op : α → α → α) (hcomm : ∀ a₁ a₂, op a₁ a₂ = op a₂ a₁) (hassoc : ∀ a₁ a₂ a₃, op (op a₁ a₂) a₃ = op a₁ (op a₂ a₃))
  local infix:55 " ⋆ " => op

  theorem hrcomm_of_comm_assoc {op : α → α → α} (hcomm : ∀ a₁ a₂, op a₁ a₂ = op a₂ a₁)
    (hassoc : ∀ a₁ a₂ a₃, op (op a₁ a₂) a₃ = op a₁ (op a₂ a₃)) :
      ∀ (a b c : α), op (op a c) b = op (op a b) c := fun a b c => by rw [hassoc, hcomm c, ←hassoc]

  namespace UnorderedList

    def fold (init : α) (s : UnorderedList β) : α :=
      Quot.liftOn s (List.foldl f init) fun _ _ p => by
        induction p generalizing init with
        | nil => rfl
        | cons x _ h => exact h (f init x)
        | swap x y _ => simp only [List.foldl]; rw [hrcomm init x y]
        | trans _ _ h₁₂ h₂₃ => exact Eq.trans (h₁₂ init) (h₂₃ init)

    namespace fold

      @[simp] theorem empty (init : α) : fold f hrcomm init 0 = init := rfl

      @[simp] theorem singleton (init : α) (b : β) : fold f hrcomm init (UnorderedList.singleton b) = f init b := rfl

      @[simp] theorem double (init : α) (b c : β) : fold f hrcomm init [b, c] = f (f init b) c := rfl

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

      theorem fold_add (a₁ a₂ : α) (s₁ s₂ : UnorderedList α) :
          (s₁ + s₂).fold op (hrcomm_of_comm_assoc hcomm hassoc) (op a₁ a₂) =
            (s₁.fold op (hrcomm_of_comm_assoc hcomm hassoc) a₁) ⋆
              (s₂.fold op (hrcomm_of_comm_assoc hcomm hassoc) a₂) :=
                @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
                  (s₁ + l).fold op (hrcomm_of_comm_assoc hcomm hassoc) (a₁ ⋆ a₂) =
                    (s₁.fold op (hrcomm_of_comm_assoc hcomm hassoc) a₁) ⋆
                    (l.fold op (hrcomm_of_comm_assoc hcomm hassoc) a₂))
                  s₂ (fun l => by
                    induction l with
                    | nil => simp; rw [←cons, cons']
                    | cons x l ih => simp at ih ⊢; rw [append.cons_over_right, cons', ih, cons', hassoc])

    end fold

    def map_fold (op : α → α → α) (hcomm : ∀ a₁ a₂, op a₁ a₂ = op a₂ a₁) (hassoc : ∀ a₁ a₂ a₃, op (op a₁ a₂) a₃ = op a₁ (op a₂ a₃))
      (init : α) (f : β → α) (s : UnorderedList β) : α :=
        (s.map f).fold op (hrcomm_of_comm_assoc hcomm hassoc) init

    namespace map_fold

      @[simp] theorem empty (init : α) (f : β → α) : map_fold op hcomm hassoc init f 0 = init := rfl

      theorem congr_map (init : α) {s : UnorderedList β} {f g : β → α} (H : ∀ x ∈ s, f x = g x) :
        s.map_fold op hcomm hassoc init f = s.map_fold op hcomm hassoc init g := by
          simp only [map_fold]
          rw [map.congr rfl H]

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

    def fold (init : α) (s : Finset β) : α := UnorderedList.fold f hrcomm init s.elems

    namespace fold

      @[simp] theorem empty (init : α) : fold f hrcomm init ∅ = init := rfl

      @[simp] theorem singleton (init : α) (b : β) : (Finset.singleton b).fold f hrcomm init = f init b := rfl

      @[simp] theorem fold_insert (init : α) {a : β} {s : Finset β} (h : a ∉ s) :
        (insert a s).fold f hrcomm init = f (s.fold f hrcomm init) a := by
          simp only [fold]; rw [insert_val, UnorderedList.ndinsert_of_not_mem h, UnorderedList.fold.cons']

    end fold

    def map_fold (op : α → α → α) (hcomm : ∀ a₁ a₂, op a₁ a₂ = op a₂ a₁) (hassoc : ∀ a₁ a₂ a₃, op (op a₁ a₂) a₃ = op a₁ (op a₂ a₃))
      (init : α) (f : β → α) (s : Finset β) : α :=
        UnorderedList.map_fold op hcomm hassoc init f s.elems

    namespace map_fold

      @[simp] theorem empty (init : α) (f : β → α) : map_fold op hcomm hassoc init f ∅ = init := rfl

      theorem congr_map (init : α) {s : Finset β} {f g : β → α} (h : ∀ x ∈ s, f x = g x) :
        s.map_fold op hcomm hassoc init f = s.map_fold op hcomm hassoc init g :=
          UnorderedList.map_fold.congr_map op hcomm hassoc init h

      theorem union_inter (f : β → α) {s₁ s₂ : Finset β} {a₁ a₂ : α} :
        (s₁ ∪ s₂).map_fold op hcomm hassoc a₁ f ⋆ (s₁ ∩ s₂).map_fold op hcomm hassoc a₂ f =
          s₁.map_fold op hcomm hassoc a₂ f ⋆ s₂.map_fold op hcomm hassoc a₁ f := by
            simp only [map_fold, UnorderedList.map_fold]
            rw [←UnorderedList.fold.fold_add op hcomm hassoc, ←UnorderedList.map.add,
              Finset.union_val, Finset.inter_val, UnorderedList.union_add_inter,
              UnorderedList.map.add, hcomm, UnorderedList.fold.fold_add op hcomm hassoc]

      @[simp] theorem fold_insert (init : α) (f : β → α) {a : β} {s : Finset β} (h : a ∉ s) :
        (insert a s).map_fold op hcomm hassoc init f = f a ⋆ s.map_fold op hcomm hassoc init f := by
          simp only [map_fold, UnorderedList.map_fold]
          rw [insert_val, UnorderedList.ndinsert_of_not_mem h, UnorderedList.map.cons, UnorderedList.fold.cons', hcomm]

    end map_fold
  end Finset
end M4R