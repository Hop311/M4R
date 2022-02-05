
theorem Or.assoc : p ∨ q ∨ r ↔ (p ∨ q) ∨ r :=
  ⟨fun pq_r => Or.elim pq_r
    (fun x => Or.inl (Or.inl x))
    (fun qr => Or.elim qr
      (fun x => Or.inl (Or.inr x))
      (fun x => Or.inr x)),
  fun pq_r => Or.elim pq_r
    (fun pq => Or.elim pq
      (fun x => Or.inl x)
      (fun x => Or.inr (Or.inl x)))
    (fun x => Or.inr (Or.inr x))⟩

theorem Or.comm : p ∨ q → q ∨ p := fun h => Or.elim h Or.inr Or.inl

theorem Or.comm' : p ∨ q ↔ q ∨ p := ⟨Or.comm, Or.comm⟩

theorem And.assoc : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, ⟨hb, hc⟩⟩, fun ⟨ha, ⟨hb, hc⟩⟩ => ⟨⟨ha, hb⟩, hc⟩⟩

theorem And.comm : a ∧ b → b ∧ a := fun ⟨p, q⟩ => ⟨q, p⟩

theorem And.comm' : a ∧ b ↔ b ∧ a := ⟨And.comm, And.comm⟩

theorem And.left_comm : a ∧ (b ∧ c) → b ∧ (a ∧ c) :=
  fun ⟨ha, hb, hc⟩ => ⟨hb, ha, hc⟩

theorem Or.resolve_left {a b : Prop} (h : a ∨ b) (na : ¬ a) : b :=
  Or.elim h (fun ha => absurd ha na) id

theorem Or.neg_resolve_left {a b : Prop} (h : ¬ a ∨ b) (ha : a) : b :=
  Or.elim h (fun na => absurd ha na) id

theorem Or.resolve_right {a b : Prop} (h : a ∨ b) (nb : ¬ b) : a :=
  Or.elim h id (fun hb => absurd hb nb)

theorem Or.neg_resolve_right {a b : Prop} (h : a ∨ ¬ b) (hb : b) : a :=
  Or.elim h id (fun nb => absurd hb nb)

theorem Or.imp (h₂ : a → c) (h₃ : b → d) : a ∨ b → c ∨ d :=
  Or.rec (fun h => Or.inl (h₂ h)) (fun h => Or.inr (h₃ h))

theorem Or.imp_left (h : a → b) : a ∨ c → b ∨ c :=
  Or.imp h id

theorem Or.imp_right (h : a → b) : c ∨ a → c ∨ b :=
  Or.imp id h

theorem M4R.exists_imp_exists {α : Sort u} {p q : α → Prop} (h : ∀ a, (p a → q a)) (p : ∃ a, p a) :
  ∃ a, q a := Exists.elim p (fun a hp => ⟨a, h a hp⟩)

theorem Exists.imp {p q : α → Prop} (h : ∀ a, (p a → q a)) (p : ∃ a, p a) : ∃ a, q a :=
  M4R.exists_imp_exists h p

namespace M4R

  @[simp] theorem exists_imp_distrib {p : α → Prop} : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
    ⟨fun h x hpx => h ⟨x, hpx⟩, fun h ⟨x, hpx⟩ => h x hpx⟩

  @[simp] theorem not_exists {p : α → Prop} : (¬ ∃ x, p x) ↔ ∀ x, ¬ p x :=
    exists_imp_distrib

  theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
    Iff.intro (fun h ha hb => h ⟨ha, hb⟩) (fun h ⟨ha, hb⟩ => h ha hb)

  @[simp] theorem not_and : ¬ (a ∧ b) ↔ (a → ¬ b) := and_imp

  open Classical

  @[simp] theorem not_and_iff_or_not : ¬(p ∧ q) ↔ ¬p ∨ ¬q := Decidable.not_and_iff_or_not p q

  @[simp] theorem not_or_iff_and_not : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    ⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩, fun ⟨h₁, h₂⟩ h => Or.elim h h₁ h₂⟩

  theorem or_iff_not_imp_left : a ∨ b ↔ (¬ a → b) :=
    ⟨Or.resolve_left, fun h => dite _ Or.inl (Or.inr ∘ h)⟩

  theorem or_iff_not_imp_right : a ∨ b ↔ (¬ b → a) :=
    Or.comm'.trans or_iff_not_imp_left

  @[simp] theorem of_not_not : ¬ ¬ p → p := Decidable.of_not_not
  
  theorem iff_not_not : ¬ ¬ p ↔ p := ⟨of_not_not, fun _ _ => by contradiction⟩

  theorem not_imp_symm (h : ¬a → b) (hb : ¬b) : a := byContradiction (hb ∘ h)

  theorem iff_not_comm : (a ↔ ¬ b) ↔ (b ↔ ¬ a) :=
    ⟨fun h =>
      ⟨fun hb ha => absurd hb (h.mp ha),
      fun ha => of_not_not (mt h.mpr ha)⟩,
    fun h =>
      ⟨fun ha hb => absurd ha (h.mp hb),
      fun hb => of_not_not (mt h.mpr hb)⟩⟩

  theorem imp_not_comm : (a → ¬b) ↔ (b → ¬a) :=
    ⟨fun h hb ha => absurd hb (h ha), fun h ha hb => absurd ha (h hb)⟩

  @[simp] theorem not_forall {p : α → Prop} : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x :=
    ⟨by apply not_imp_symm; intro nE x; apply not_imp_symm _ nE; exact fun h => ⟨x, h⟩,
    fun ⟨x, hn⟩ hA => hn (hA x)⟩

  @[simp] theorem not_iff_not : (¬p ↔ ¬q) ↔ (p ↔ q) :=
    have h : ∀ p q, (p ↔ q) → (¬ p ↔ ¬ q) := fun p q h => ⟨mt h.mpr, mt h.mp⟩
    ⟨by
      have := h (¬p) (¬q)
      simp only [iff_not_not] at this
      exact this, h p q⟩

  theorem iff_of_true (ha : a) (hb : b) : a ↔ b :=
    ⟨fun _ => hb, fun _ => ha⟩

  theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b :=
    ⟨fun h => absurd h ha, fun h => absurd h hb⟩

  theorem eq_self_iff_true (a : α) : a = a ↔ True :=
    ⟨fun _ => trivial, fun _ => rfl⟩

  theorem forall_true_iff : α → True ↔ True :=
    ⟨fun _ => trivial, fun _ _ => trivial⟩

  theorem forall_true_iff' {p : α → Prop} (h : ∀ a, p a ↔ True) : (∀ a, p a) ↔ True :=
    ⟨fun _ => trivial, fun t a => (h a).mpr t⟩

  @[simp] theorem forall_2_true_iff {β : α → Sort _} : (∀ a, β a → True) ↔ True :=
    forall_true_iff' fun _ => forall_true_iff

  @[simp] theorem forall_3_true_iff {β : α → Sort _} {γ : ∀ a, β a → Sort _} :
    (∀ (a : α) (b : β a), γ a b → True) ↔ True :=
      forall_true_iff' fun _ => forall_2_true_iff

end M4R

@[simp] theorem Quotient.eq [r : Setoid α] {x y : α} : Quotient.mk x = Quotient.mk y ↔ x ≈ y :=
  ⟨Quotient.exact, Quotient.sound⟩

@[simp] protected theorem Subtype.exists {p : α → Prop} {q : {a // p a} → Prop} : (∃ x, q x) ↔ (∃ a b, q ⟨a, b⟩) :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

def Option.guard (p : α → Prop) [DecidablePred p] (a : α) : Option α :=
  if p a then some a else none
