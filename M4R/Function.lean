import M4R.Set.Basic

namespace M4R
  namespace Function

    theorem comp_eq (f : β → γ) (g : α → β) (a : α) : f (g a) = (f ∘ g) a := rfl
    theorem comp_assoc (f : γ → δ) (g : β → γ) (h : α → β) : f ∘ g ∘ h = (f ∘ g) ∘ h := rfl

    def restrict (f : α → β) (s : Set α) : s → β := Function.comp f Set.inclusion

    def domain (f : α → β) := α
    def codomain (f : α → β) := β
    def image (f : α → β) : Set β := {y | ∃ x : α, f x = y}
    def image' (f : α → β) (s : Set α) : Set β := {y | ∃ x ∈ s, f x = y}
    def inv_image (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}
    def fibre (f : α → β) (b : β) : Set α := {x | f x = b}

    theorem image'_sub_image (f : α → β) (s : Set α) : image' f s ⊆ image f :=
      fun x ⟨y, hy, hye⟩ => ⟨y, hye⟩
    theorem image'_subset (f : α → β) {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) : image' f s₁ ⊆ image' f s₂ :=
      fun x ⟨y, hys₁, hyx⟩ => ⟨y, h hys₁, hyx⟩

    def injective (f : α → β) : Prop := ∀ ⦃x y : α⦄, f x = f y → x = y
    def surjective (f : α → β) : Prop := ∀ y : β, ∃ x : α, f x = y
    def bijective (f : α → β) : Prop := injective f ∧ surjective f
    def bijective.inj {f : α → β} (h : bijective f) : injective f := h.left
    def bijective.surj {f : α → β} (h : bijective f) : surjective f := h.right

    theorem injective.comp {g : β → γ} {f : α → β} (hg : injective g) (hf : injective f) : injective (g ∘ f) :=
        fun _ _ h => hf (hg h)
    theorem surjective.comp {g : β → γ} {f : α → β} (hg : surjective g) (hf : surjective f) : surjective (g ∘ f) :=
      fun (c : γ) => Exists.elim (hg c) (fun b hb => Exists.elim (hf b) (fun a ha =>
      Exists.intro a (show g (f a) = c from (Eq.trans (congrArg g ha) hb))))
    theorem bijective.comp {g : β → γ} {f : α → β} : bijective g → bijective f → bijective (g ∘ f)
    | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩

    def left_inverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x
    def has_left_inverse (f : α → β) : Prop := ∃ finv : β → α, left_inverse finv f

    def right_inverse (g : β → α) (f : α → β) : Prop := left_inverse f g
    def has_right_inverse (f : α → β) : Prop := ∃ finv : β → α, right_inverse finv f

    theorem left_inverse.injective {g : β → α} {f : α → β} : left_inverse g f → injective f :=
      fun h a b hf => h a ▸ h b ▸ hf ▸ rfl
    theorem left_inverse.inv_surjective {g : β → α} {f : α → β} : left_inverse g f → surjective g :=
      fun h a => ⟨f a, h a⟩
    theorem has_left_inverse.injective {f : α → β} : has_left_inverse f → injective f :=
      fun h => Exists.elim h (fun finv inv => inv.injective)
    theorem right_inverse_of_injective_of_left_inverse {f : α → β} {g : β → α}
        (injf : injective f) (lfg : left_inverse f g) :
      right_inverse f g :=
      fun x => injf (lfg (f x))

    theorem right_inverse.surjective {f : α → β} {g : β → α} (h : right_inverse g f) : surjective f :=
      fun y => ⟨g y, h y⟩
    theorem right_inverse.inv_injective {g : β → α} {f : α → β} : right_inverse g f → injective g :=
      fun h a b hg => by rw [←h a, ←h b]; exact congrArg f hg
    theorem has_right_inverse.surjective {f : α → β} : has_right_inverse f → surjective f
    | ⟨finv, inv⟩ => inv.surjective
    theorem left_inverse_of_surjective_of_right_inverse {f : α → β} {g : β → α} (surjf : surjective f)
      (rfg : right_inverse f g) : left_inverse f g :=
      fun y =>
        let ⟨x, hx⟩ := surjf y
        by rw [← hx, rfg]

    theorem bijective_of_inverse {f : α → β} {g : β → α} (hl : left_inverse g f) (hr : right_inverse g f) :
      Function.bijective f := ⟨hl.injective, hr.surjective⟩

    theorem id_injective : @injective α α id := fun _ _ => id
    theorem id_surjective : @surjective α α id := fun y => ⟨y, rfl⟩
    theorem id_bijective : @bijective α α id := ⟨id_injective, id_surjective⟩

    theorem surj_image (f : α → β) : surjective f ↔ image f = Set.Universal := by
      apply Iff.intro
      { intro surj; apply Set.subset.antisymm;
        { exact Set.subset.subUniversal _ }
        { intro y _; exact surj y } }
      intro heq y; simp only [image, Set.Universal] at heq; rw [congrFun heq y]; trivial

    namespace Quotient

      protected def map (ra : α → α → Prop) (rb : β → β → Prop) (f : α → β)
        (h : ∀ a₁ a₂, ra a₁ a₂ → rb (f a₁) (f a₂)) : Quot ra → Quot rb :=
        Quot.lift (fun x => Quot.mk rb (f x)) (fun _ _ hra => Quot.sound (h _ _ hra))

      protected def lift₂ (ra : α → α → Prop) (rb : β → β → Prop)
        (ha : ∀ a : α, ra a a) (hb : ∀ b : β, rb b b) (f : α → β → γ)
        (c : ∀ (a₁ a₂ : α) (b₁ b₂ : β), ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂)
        (qa : Quot ra) (qb : Quot rb) : γ :=
        Quot.lift
          (fun (x : α) => Quot.lift (f x) (fun (u v : β) => c x x u v (ha x)) qb)
          (fun (x y : α) (h : ra x y) =>
            @Quot.ind β rb
              (fun (q : Quot rb) =>
                  (Quot.lift (f x) (fun (u v : β) => c x x u v (ha x)) q)
                  =
                  (Quot.lift (f y) (fun (u v : β) => c y y u v (ha y)) q))
              (fun (u : β) => c x y u u h (hb u))
              qb)
          qa

      protected def map₂ (ra : α → α → Prop) (rb : β → β → Prop) (rc : γ → γ → Prop)
        (ha : ∀ a : α, ra a a) (hb : ∀ b : β, rb b b) (f : α → β → γ)
        (h : ∀ (a₁ a₂ : α) (b₁ b₂ : β), ra a₁ a₂ → rb b₁ b₂ → rc (f a₁ b₁) (f a₂ b₂)) :
        Quot ra → Quot rb → Quot rc :=
          Quotient.lift₂ ra rb ha hb
            (fun x y => Quot.mk rc (f x y))
            (fun _ _ _ _ h₁ h₂ => Quot.sound (h _ _ _ _ h₁ h₂))

      protected theorem ind₂ (ra : α → α → Prop) (rb : β → β → Prop) {motive : Quot ra → Quot rb → Prop}
        (h : ∀ (a : α) (b : β), motive (Quot.mk ra a) (Quot.mk rb b)) (qa : Quot ra) (qb : Quot rb) :
          motive qa qb :=
            @Quot.ind α ra (fun q : Quot ra => motive q qb)
             (fun a : α => @Quot.ind β rb (motive (Quot.mk ra a)) (fun b : β => h a b) qb) qa

      protected theorem ind₃ (ra : α → α → Prop) (rb : β → β → Prop) (rc : γ → γ → Prop)
        {motive : Quot ra → Quot rb → Quot rc → Prop}
        (h : ∀ (a : α) (b : β) (c : γ), motive (Quot.mk ra a) (Quot.mk rb b) (Quot.mk rc c))
        (qa : Quot ra) (qb : Quot rb) (qc : Quot rc) :
          motive qa qb qc :=
          @Quot.ind α ra (fun q : Quot ra => motive q qb qc) (fun a : α =>
          @Quot.ind β rb (fun q : Quot rb => motive (Quot.mk ra a) q qc) (fun b : β =>
          @Quot.ind γ rc (motive (Quot.mk ra a) (Quot.mk rb b)) (fun c : γ => h a b c) qc) qb) qa

    end Quotient

    section update

      def update [DecidableEq α] {β : α → Sort _} (f : (a : α) → β a) (a' : α) (v : β a') (a : α) : β a :=
        if h : a = a' then (by rw [h]; exact v) else f a

      theorem update_apply [DecidableEq α] (f : α → β) (a' : α) (b : β) (a : α) :
        update f a' b a = if a = a' then b else f a := rfl

      @[simp] theorem update_same [DecidableEq α] {β : α → Sort _} (a : α) (v : β a) (f : (a : α) → β a) :
        update f a v a = v := dif_pos rfl

      @[simp] theorem update_noteq [DecidableEq α] {β : α → Sort _} {a a' : α} (h : a ≠ a') (v : β a')
        (f : (a : α) → β a) : update f a' v a = f a :=
          dif_neg h

    end update
  end Function

  namespace minimal
    open Classical

    private def lbp (s : Set Nat) (m n : Nat) : Prop := m = n + 1 ∧ ∀ k, k ≤ n → k ∉ s

    private def wf_lbp {s : Set Nat} (hs : Nonempty s) : WellFounded (lbp s) :=
      let ⟨n, hn⟩ := hs
      ⟨fun a => have : (∀ m k, n ≤ k + m → Acc (lbp s) k) := fun m => by induction m with
          | zero      => exact fun k kn => ⟨k, fun y r => absurd hn (r.right n (Nat.add_zero k ▸ kn))⟩
          | succ m ih => exact fun k kn => ⟨_, fun y r => ih y (r.left ▸ Nat.succ_add _ _ ▸ Nat.add_succ _ _ ▸ kn)⟩
        this _ _ (Nat.le_add_left _ _)⟩

    protected noncomputable def find (s : Set Nat) (hs : Nonempty s) : {n // n ∈ s ∧ ∀ m, m < n → m ∉ s} :=
      @WellFounded.fix Nat (fun k => (∀ n, n < k → n ∉ s) → {n // n ∈ s ∧ ∀ m, m < n → m ∉ s}) (lbp s) (wf_lbp hs)
        (fun x h₁ h₂ => if hx : x ∈ s then ⟨x, hx, h₂⟩ else
          have : ∀ n, n ≤ x → n ∉ s := fun n hn => Or.elim (Nat.lt_or_eq_of_le hn) (h₂ n) (· ▸ hx)
          h₁ _ ⟨rfl, this⟩ fun n hn => this n (Nat.le_of_succ_le_succ hn))
        0 fun n h => absurd h (Nat.not_lt_zero n)

    theorem min_nat (s : Set Nat) (hs : Nonempty s) : ∃ n ∈ s, ∀ m ∈ s, n ≤ m :=
      let ⟨n, hn, h⟩ := minimal.find s hs
      ⟨n, hn, fun m hm => Nat.le_of_not_lt (mt (h m) (iff_not_not.mpr hm))⟩

    theorem min_exists (s : Set α) (hs : Nonempty s) (f : α → Nat) : ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
      let ⟨x, hx⟩ := hs
      let ⟨n, ⟨y, hy, hyn⟩, hmin⟩ := min_nat (Function.image' f s) ⟨f x, x, hx, rfl⟩
      ⟨y, hy, fun z hz => hyn ▸ hmin (f z) ⟨z, hz, rfl⟩⟩

  end minimal
  namespace maximal

    theorem max_exists (s : Set α) (hs : Nonempty s) (f : α → Nat) (hf : ∃ n, ∀ y ∈ s, f y ≤ n) :
      ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x := by
        let ⟨n, hn⟩ := hf
        let ⟨x, xs, hx⟩ := minimal.min_exists s hs (fun a => n - f a)
        exact ⟨x, xs, fun y ys => (Nat.sub_le_sub (hn y ys) (hn x xs)).mpr (hx y ys)⟩

  end maximal
end M4R
