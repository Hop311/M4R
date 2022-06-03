import M4R.Algebra.Ring.RMorphism

namespace M4R
  open NCSemiring Semiring

  namespace UnorderedList.map_sum

    theorem mul_sum [NCSemiring β] (b : β) (f : α → β) (s : UnorderedList α) :
      b * (∑ f in s) = ∑ (b * f ·) in s := by
        let h := NCSemiring.MulHomLeft b
        have : b * (∑ f in s) = h (∑ f in s) := rfl
        rw [this, h.map_sum']; rfl

    theorem sum_mul [NCSemiring β] (b : β) (f : α → β) (s : UnorderedList α) :
      (∑ f in s) * b = ∑ (f · * b) in s := by
        let h := NCSemiring.MulHomRight b
        have : (∑ f in s) * b = h (∑ f in s) := rfl
        rw [this, h.map_sum']; rfl

    theorem div_sum [Semiring β] (b : β) (f : α → β) (s : UnorderedList α) (h : ∀ a ∈ s, b ÷ f a) :
      b ÷ (∑ f in s) :=
        prop_sum (b ÷ ·) f s (divides_zero b) h (fun _ _ => divides_add)

    theorem mul_distrib [NCSemiring γ] (s₁ : UnorderedList α) (s₂ : UnorderedList β) (f₁ : α → γ) (f₂ : β → γ) :
      (∑ f₁ in s₁) * (∑ f₂ in s₂) = ∑ x in s₁.product s₂, f₁ x.fst * f₂ x.snd :=
        UnorderedList.induction_on (fun s₁ : UnorderedList α => (∑ f₁ in s₁) * (∑ f₂ in s₂) = ∑ x in s₁.product s₂, f₁ x.fst * f₂ x.snd) s₁
          (by simp only [product.empty_left, empty, zero_mul])
          (fun a s ih => by
            simp only [cons, mul_distrib_right, ih, product.cons_left, append]
            exact congrArg (_ + ·) (UnorderedList.induction_on (fun s₂ => f₁ a * (∑ f₂ in s₂) = ∑ x in s₂.map (Prod.mk a), f₁ x.fst * f₂ x.snd) s₂
              (by simp only [map_nil, empty, mul_zero])
              (fun _ _ ih => by simp only [map.cons, cons, mul_distrib_left, ih])))

  end UnorderedList.map_sum

  namespace Finset.map_sum

    theorem mul_sum [NCSemiring β] (b : β) (f : α → β) (s : Finset α) :
      b * (∑ f in s) = ∑ (b * f ·) in s := UnorderedList.map_sum.mul_sum b f s

    theorem sum_mul [NCSemiring β] (b : β) (f : α → β) (s : Finset α) :
      (∑ f in s) * b = ∑ (f · * b) in s := UnorderedList.map_sum.sum_mul b f s

    theorem div_sum [Semiring β] (b : β) (f : α → β) (s : Finset α) (h : ∀ a ∈ s, b ÷ f a) :
      b ÷ (∑ f in s) := UnorderedList.map_sum.div_sum b f s h

    theorem mul_distrib [NCSemiring γ] (s₁ : Finset α) (s₂ : Finset β) (f₁ : α → γ) (f₂ : β → γ) :
      (∑ f₁ in s₁) * (∑ f₂ in s₂) = ∑ x in s₁.elems.product s₂.elems, f₁ x.fst * f₂ x.snd :=
        UnorderedList.map_sum.mul_distrib s₁.elems s₂.elems f₁ f₂

  end Finset.map_sum

  theorem Semiring.binomial [Semiring α] (a b : α) (n : Nat) : (a + b)^n =
    ∑ (fun x => n.choose x.fst * a ^ x.fst * b ^ x.snd) in (Finset.antidiagonal n) := by
      induction n with
      | zero => simp only [Nat.zero_eq, pow_nat_0, Finset.antidiagonal.zero,
        Finset.map_sum.singleton, mul_one]; rfl
      | succ n ih =>
        rw [pow_nat_succ, ih, Finset.map_sum.sum_mul]
        have : (fun (x : Nat × Nat) => n.choose x.fst * a ^ x.fst * b ^ x.snd * (a + b)) =
          (fun (x : Nat × Nat) => n.choose x.fst * a ^ x.fst.succ * b ^ x.snd +
            n.choose x.fst * a ^ x.fst * b ^ x.snd.succ) := funext fun x => by
              rw [mul_distrib_left, mul_right_comm, mul_assoc _ _ a,
                mul_assoc _ _ b, pow_nat_succ, pow_nat_succ]
        rw [this]; simp only [Finset.map_sum.antidiagonal_eq_range]
        rw [Finset.map_sum.distrib, CommMonoid.add_comm, Finset.map_sum.range_start,
          Finset.map_sum.range_succ, ←Monoid.add_assoc, Monoid.add_assoc (_ * _)]
        have : (∑ k in Finset.range' 1 n, n.choose k * a ^ k * b ^ (n - k).succ) +
          (∑ k in Finset.range n, n.choose k * a ^ k.succ * b ^ (n - k)) =
            ∑ k in Finset.range' 1 n, n.succ.choose k * a ^ k * b ^ (n.succ - k) := by
              rw [Finset.map_sum.range_shift, ←Finset.map_sum.distrib]
              exact Finset.map_sum.congr rfl (fun x hx => by
                simp only [Function.comp]
                have ⟨h₁, h₂⟩ := Finset.range'.mem_range'.mp hx
                have h₂ : x ≤ n := Nat.le_of_lt_succ (Nat.one_add n ▸ h₂)
                rw [Nat.succ_pred_eq_of_pos h₁, Nat.succ_sub h₂, Nat.sub_pred h₁ h₂,
                  ←mul_distrib_right, ←mul_distrib_right, ←ofNat.preserve_add, Nat.choose_pred h₁])
        rw [this, Finset.map_sum.range_succ, Finset.map_sum.range_start, Nat.choose_zero_right_succ,
          Nat.sub_zero, Nat.sub_zero, Nat.choose_self_succ, Nat.sub_self, Nat.sub_self]

  def UnorderedList.fold_mul [Semiring α] (init : α) (s : UnorderedList α) :=
    s.fold (· * ·) (fun x y z => mul_right_comm x z y) init

  namespace UnorderedList.fold_mul

    @[simp] theorem empty [Semiring α] (init : α) : UnorderedList.fold_mul init ∅ = init := rfl

    theorem cons [Semiring α] (init a : α) (s : UnorderedList α) : (s.cons a).fold_mul init = s.fold_mul init * a :=
      UnorderedList.fold.cons' _ _ init a s

    theorem init_change [Semiring α] (init a : α) (s : UnorderedList α) : s.fold_mul (init * a) = s.fold_mul init * a := by
      have : (s.cons a).fold_mul init = s.fold_mul (init * a) :=
        UnorderedList.fold.cons _ _ init a s
      rw [←this, cons]

    theorem init_swap [Semiring α] (a b : α) (s : UnorderedList α) : s.fold_mul a * b = s.fold_mul b * a := by
      rw [←init_change, ←init_change, mul_comm]

    theorem append [Semiring α] (init : α) (s t : UnorderedList α) : (s + t).fold_mul init * init = s.fold_mul init * t.fold_mul init := by
      have : (s + t).fold_mul init = t.fold_mul (s.fold_mul init) := by
        simp only [fold_mul, fold.append];
      rw [this, init_swap, mul_comm]

  end UnorderedList.fold_mul

  def UnorderedList.map_fold_mul [Semiring α] (init : α) (f : β → α) (s : UnorderedList β) : α :=
    s.map_fold (· * ·) mul_comm mul_assoc init f

  namespace UnorderedList.map_fold_mul

    @[simp] theorem empty [Semiring α] (init : α) (f : β → α) : map_fold_mul init f ∅ = init := rfl

    theorem cons [Semiring α] (init : α) (f : β → α) (b : β) (s : UnorderedList β) :
      (s.cons b).map_fold_mul init f = s.map_fold_mul init f * f b :=
        map_fold.cons (· * ·) mul_comm mul_assoc init f s b

    theorem distrib [Semiring α] (init : α) (f g : β → α) (s : UnorderedList β) :
      init * s.map_fold_mul init (fun b => f b * g b) =
        (s.map_fold_mul init f) * (s.map_fold_mul init g) := by
          simp only [map_fold_mul, map_fold.distrib]

    theorem congr_map [Semiring α] (init : α) {s : UnorderedList β} {f g : β → α} (h : ∀ x ∈ s, f x = g x) :
      s.map_fold_mul init f = s.map_fold_mul init g :=
        map_fold.congr_map (· * ·) mul_comm mul_assoc init h

  end UnorderedList.map_fold_mul

  def UnorderedList.prod [Semiring α] (s : UnorderedList α) : α :=
    s.fold_mul 1
  def UnorderedList.map_prod [Semiring β] (s : UnorderedList α) (f : α → β) : β :=
    s.map_fold_mul 1 f

  namespace UnorderedList.prod

    @[simp] theorem empty [Semiring α] : (∏ (0 : UnorderedList α)) = 1 := rfl

    theorem cons [Semiring α] (a : α) (s : UnorderedList α) : (∏ s.cons a) = (∏ s) * a :=
      fold_mul.cons 1 a s

    @[simp] theorem cons_one [Semiring α] (s : UnorderedList α) : (∏ s.cons 1) = ∏ s :=
      mul_one (∏ s) ▸ cons 1 s

    @[simp] theorem singleton [Semiring α] (a : α) : (∏ UnorderedList.singleton a) = a := by
      conv => rhs rw [←one_mul a]

    @[simp] theorem double  [Semiring α] (a b : α) : (∏ ([a, b] : UnorderedList α)) = a * b := by
      have : ([a, b] : UnorderedList α) = (UnorderedList.singleton b).cons a := rfl
      rw [this, cons, singleton]; exact mul_comm b a

    theorem eq_one [Semiring α] {s : UnorderedList α} (h : ∀ x ∈ s, x = 1) : (∏ s) = 1 :=
      @Quotient.inductionOn (List α) (Perm.PermSetoid α) (fun (l : UnorderedList α) =>
        (∀ a ∈ l, a = 1) → (∏ l) = 1) s (fun l hl => by
          induction l with
          | nil => rfl
          | cons x l ih =>
            rw [UnorderedList.cons', cons, hl x (by rw [UnorderedList.cons']; exact UnorderedList.mem_cons_self _ _), mul_one]
            exact ih (fun a ha => hl a (UnorderedList.mem_cons_of_mem ha)))
        h

    theorem append [Semiring α] (s t : UnorderedList α) : (∏ s + t) = (∏ s) * (∏ t) := by
      have := fold_mul.append 1 s t
      rw [mul_one] at this
      exact this

    theorem prop_prod [Semiring α] (p : α → Prop) (s : UnorderedList α) (h₀ : p 1)
      (h₁ : ∀ a ∈ s, p a) (h₂ : ∀ a₁ a₂, p a₁ → p a₂ → p (a₁ * a₂)) :
        p (∏ s) :=
          UnorderedList.induction_on (fun l => l ⊆ s → p (∏ l)) s (fun _ => h₀)
            (fun a l hl hla => by
              rw [cons]; exact h₂ _ _ (hl fun x hx => hla (mem_cons.mpr (Or.inr hx)))
                (h₁ _ (hla (mem_cons.mpr (Or.inl rfl))))) (Subset.refl _)

  end UnorderedList.prod
  namespace UnorderedList.map_prod

    @[simp] theorem map_def [Semiring β] (f : α → β) (s : UnorderedList α) : (∏ s.map f) = ∏ f in s := rfl

    @[simp] theorem empty [Semiring β] (f : α → β) : (∏ f in (0 : UnorderedList α)) = 1 := rfl

    @[simp] theorem map_id [Semiring α] (s : UnorderedList α) : (∏ id in s) = ∏ s := by
      simp only [map_prod, map_fold_mul, map_fold, UnorderedList.map.map_id s] rfl

    theorem cons [Semiring β] (f : α → β) (a : α) (s : UnorderedList α) : (∏ f in s.cons a) = (∏ f in s) * (f a) :=
      map_fold_mul.cons 1 f a s

    theorem congr [Semiring β] {f g : α → β} {s₁ s₂ : UnorderedList α} (h : s₁ = s₂) :
      (∀ x ∈ s₂, f x = g x) → (∏ f in s₁) = ∏ g in s₂ := by
        rw [h]; exact UnorderedList.map_fold_mul.congr_map 1

    @[simp] theorem singleton [Semiring β] (f : α → β) (a : α) : (∏ f in UnorderedList.singleton a) = f a := by
      simp only [map_prod, map_fold_mul, map_fold, map.singleton f a, fold.singleton, one_mul]

    @[simp] theorem double  [Semiring β] (f : α → β) (a b : α) : (∏ f in ([a, b] : UnorderedList α)) = f a * f b :=
      (prod.double (f a) (f b)).symm ▸ rfl

    theorem eq_one [Semiring β] {f : α → β} {s : UnorderedList α} (h : ∀ x ∈ s, f x = 1) :
      (∏ f in s) = 1 :=
        UnorderedList.prod.eq_one fun x hx =>
          let ⟨a, ha, he⟩ := UnorderedList.map.mem_map.mp hx
          he.symm.trans (h a ha)

    theorem distrib [Semiring β] (f g : α → β) (s : UnorderedList α) :
      (∏ x in s, f x * g x) = (∏ f in s) * ∏ g in s := by
        have := map_fold_mul.distrib 1 f g s
        rw [one_mul] at this
        simp only [map_prod, this]

    theorem comm [Semiring γ] {s : UnorderedList α} {t : UnorderedList β} {f : α → β → γ} :
      (∏ x in s, ∏ y in t, f x y) = (∏ y in t, ∏ x in s, f x y) :=
        UnorderedList.induction_on (fun l => (∏ x in l, ∏ y in t, f x y) = (∏ y in t, ∏ x in l, f x y)) s
          (by simp only [empty]; exact (eq_one (fun _ _ => rfl)).symm)
          (fun a l ih => by
            simp at ih ⊢
            have : (fun y => map_prod (UnorderedList.cons a l) (f · y)) =
              (fun y => (map_prod l (f · y)) * f a y) := by simp only [cons]
            rw [cons, this, distrib, ih])

    theorem map [Semiring γ] (s : UnorderedList α) (e : α → β) (f : β → γ) :
      (∏ f in s.map e) = ∏ f ∘ e in s := by
        simp only [map_prod, map_fold_mul, map_fold, UnorderedList.map.map_comp]

    theorem prop_prod [Semiring β] (p : β → Prop) (f : α → β) (s : UnorderedList α) (h₀ : p 1)
      (h₁ : ∀ a ∈ s, p (f a)) (h₂ : ∀ b₁ b₂, p b₁ → p b₂ → p (b₁ * b₂)) :
        p (∏ f in s) :=
          UnorderedList.prod.prop_prod _ _ h₀ (fun b hb =>
            let ⟨a, has, hab⟩ := map.mem_map.mp hb
            hab ▸ h₁ a has) h₂

  end UnorderedList.map_prod

  def Finset.prod [Semiring α] (s : Finset α) : α := s.elems.prod
  def Finset.map_prod [Semiring β] (s : Finset α) (f : α → β) : β := s.elems.map_prod f

  namespace Finset.prod

    @[simp] theorem empty [Semiring α] : (∏ (∅ : Finset α)) = 1 := rfl

    theorem cons [Semiring α] {a : α} {s : Finset α} (ha : a ∉ s) : (∏ s.cons a ha) = (∏ s) * a :=
      UnorderedList.prod.cons a s.elems

    theorem eq_one [Semiring α] {s : Finset α} (h : ∀ x ∈ s, x = 1) : (∏ s) = 1 :=
      UnorderedList.prod.eq_one h

    @[simp] theorem singleton [Semiring α] (a : α) : (∏ Finset.singleton a) = a :=
      UnorderedList.prod.singleton a

    @[simp] theorem prod_insert [Semiring α] {a : α} {s : Finset α} : a ∉ s → (∏ insert a s) = a * ∏ s := by
      rw [mul_comm]; exact fold.fold_insert (· * ·) (fun x y z => mul_right_comm x z y) 1

    theorem prop_prod [Semiring α] (p : α → Prop) (s : Finset α) (h₀ : p 1)
      (h₁ : ∀ a ∈ s, p a) (h₂ : ∀ a₁ a₂, p a₁ → p a₂ → p (a₁ * a₂)) :
        p (∏ s) := UnorderedList.prod.prop_prod p s h₀ h₁ h₂

  end Finset.prod

  namespace Finset.map_prod

    @[simp] theorem map_def [Semiring β] (f : α → β) (s : Finset α) : (∏ s.map f) = ∏ f in s := rfl

    @[simp] theorem empty [Semiring β] (f : α → β) : (∏ f in (∅ : Finset α)) = 1 := rfl

    @[simp] theorem map_id [Semiring α] (s : Finset α) : (∏ id in s) = ∏ s :=
      UnorderedList.map_prod.map_id s.elems

    theorem cons [Semiring β] (f : α → β) {a : α} {s : Finset α} (ha : a ∉ s) : (∏ f in s.cons a ha) = (∏ f in s) * (f a) :=
      UnorderedList.map_prod.cons f a s.elems

    theorem eq_one [Semiring β] {f : α → β} {s : Finset α} (h : ∀ x ∈ s, f x = 1) :
      (∏ f in s) = 1 :=
        UnorderedList.map_prod.eq_one h

    @[simp] theorem singleton [Semiring β] (f : α → β) (a : α) : (∏ f in Finset.singleton a) = f a :=
      UnorderedList.map_prod.singleton f a

    theorem distrib [Semiring β] (f g : α → β) (s : Finset α) :
      (∏ x in s, f x * g x) = (∏ f in s) * ∏ g in s := by
        exact UnorderedList.map_prod.distrib f g s

    theorem congr [Semiring β] {f g : α → β} {s₁ s₂ : Finset α} (h : s₁ = s₂) :
      (∀ x ∈ s₂, f x = g x) → (∏ f in s₁) = ∏ g in s₂ :=
        UnorderedList.map_prod.congr (val_inj.mpr h)

    theorem union_inter [Semiring β] {f : α → β} {s₁ s₂ : Finset α} :
      (∏ f in (s₁ ∪ s₂)) * (∏ f in (s₁ ∩ s₂)) = (∏ f in s₁) * (∏ f in s₂) :=
        Finset.map_fold.union_inter (· * ·) mul_comm mul_assoc f

    theorem union [Semiring β] {f : α → β} {s₁ s₂ : Finset α} (h : disjoint s₁ s₂) :
      (∏ f in (s₁ ∪ s₂)) = (∏ f in s₁) * (∏ f in s₂) := by
        rw [←union_inter, h, empty, mul_one]

    theorem sdiff [Semiring β] {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) {f : α → β} :
      (∏ f in (s₂ ∖ s₁)) * (∏ f in s₁) = (∏ f in s₂) := by
        rw [←union (((s₂ ∖ s₁).inter_comm s₁).trans (s₁.inter_sdiff_self s₂)), sdiff_union_of_subset h]

    theorem subset_zero_on_sdiff [Semiring β] {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) {f g : α → β}
      (hg : ∀ x ∈ (s₂ ∖ s₁), g x = 1) (hfg : ∀ x ∈ s₁, f x = g x) : (∏ f in s₁) = ∏ g in s₂ := by
        rw [←sdiff h, eq_one hg, one_mul]
        exact congr rfl hfg

    theorem subset [Semiring β] {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) {f : α → β} (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
      (∏ f in s₁) = ∏ f in s₂ :=
        subset_zero_on_sdiff h (by simp only [mem_sdiff, and_imp]; exact hf) (fun _ _ => rfl)

    @[simp] theorem prod_insert [Semiring β] (f : α → β) {a : α} {s : Finset α} :
      a ∉ s → (∏ f in insert a s) = f a * ∏ f in s :=
        map_fold.fold_insert (· * ·) mul_comm mul_assoc 1 f

    theorem comm [Semiring γ] {s : Finset α} {t : Finset β} {f : α → β → γ} :
      (∏ x in s, ∏ y in t, f x y) = (∏ y in t, ∏ x in s, f x y) :=
        UnorderedList.map_prod.comm

    theorem map [Semiring γ] (s : Finset α) {e : α → β} (he : Function.injective e) (f : β → γ) :
      (∏ f in s.map_inj he) = ∏ f ∘ e in s :=
        UnorderedList.map_prod.map s.elems e f

    theorem antidiagonal_eq_range [Semiring α] (f : Nat × Nat → α) (n : Nat) :
      (∏ f in Finset.antidiagonal n) = ∏ k in Finset.range n.succ, f (k, n-k) := by
        have : Finset.antidiagonal n = (Finset.range n.succ).map_inj (fun _ _ h => by
          rw [Prod.mk.injEq] at h; exact h.left) := rfl
        rw [this, map_prod.map]

    theorem range'_start [Semiring α] (f : Nat → α) (s n : Nat) :
      (∏ f in Finset.range' s n.succ) = f s * ∏ f in Finset.range' s.succ n := by
        rw [Finset.range'.start, cons, mul_comm]

    theorem range'_succ [Semiring α] (f : Nat → α) (s n : Nat) :
      (∏ f in Finset.range' s n.succ) = (∏ f in Finset.range' s n) * f (s+n) := by
        rw [Finset.range'.succ, cons]

    theorem range_start [Semiring α] (f : Nat → α) (n : Nat) :
      (∏ f in Finset.range n.succ) = f 0 * ∏ f in Finset.range' 1 n := by
        rw [Finset.range.start, cons, mul_comm]

    theorem range_succ [Semiring α] (f : Nat → α) (n : Nat) :
      (∏ f in Finset.range n.succ) = (∏ f in Finset.range n) * f n := by
        rw [Finset.range.succ, cons]

    theorem range'_shift [Semiring α] (f : Nat → α) (s n : Nat) :
      (∏ f in Finset.range' s n) = ∏ f ∘ Nat.pred in Finset.range' s.succ n := by
        induction n with
        | zero => rw [Finset.range'.zero, Finset.range'.zero, empty, empty]
        | succ n ih =>
          rw [range'_succ, ih, range'_succ, Nat.succ_add]
          simp only [Function.comp, Nat.pred_succ]

    theorem range_shift [Semiring α] (f : Nat → α) (n : Nat) :
      (∏ f in Finset.range n) = ∏ f ∘ Nat.pred in Finset.range' 1 n := by
        rw [range_eq_range']; exact range'_shift f 0 n

    theorem range'_split [Semiring α] {f : Nat → α} {s n : Nat} (m : Nat) (h : m ≤ n) :
      (∏ f in Finset.range' s n) = (∏ f in Finset.range' s m) * (∏ f in Finset.range' (s + m) (n - m)) := by
        have := Finset.range'.append s m (n - m)
        rw [Nat.add_comm m, Nat.sub_add_cancel h] at this
        rw [←this, union ((Finset.range'.disjoint _ _ _ _).mpr (Or.inl (Nat.le_refl _)))]

    theorem prop_prod [Semiring β] (p : β → Prop) (f : α → β) (s : Finset α) (h₀ : p 1)
      (h₁ : ∀ a ∈ s, p (f a)) (h₂ : ∀ b₁ b₂, p b₁ → p b₂ → p (b₁ * b₂)) :
        p (∏ f in s) := UnorderedList.map_prod.prop_prod p f s h₀ h₁ h₂

    theorem prod_term [Semiring β] (f : α → β) (s : Finset α) {a : α} (ha : a ∈ s) : (∏ f in s) = (∏ f in s.erase a) * f a := by
      conv => lhs rw [s.erase_cons ha, cons]

  end Finset.map_prod

end M4R
