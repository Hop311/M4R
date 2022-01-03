
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

theorem And.comm : a ∧ b → b ∧ a := fun ⟨p, q⟩ => ⟨q, p⟩

theorem And.comm' : a ∧ b ↔ b ∧ a := ⟨And.comm, And.comm⟩

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

namespace M4R

  @[simp] theorem exists_imp_distrib {p : α → Prop} : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
    ⟨fun h x hpx => h ⟨x, hpx⟩, fun h ⟨x, hpx⟩ => h x hpx⟩

  theorem not_exists {p : α → Prop} : (¬ ∃ x, p x) ↔ ∀ x, ¬ p x :=
    exists_imp_distrib

  theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
    Iff.intro (fun h ha hb => h ⟨ha, hb⟩) (fun h ⟨ha, hb⟩ => h ha hb)

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

  @[simp] theorem not_forall {p : α → Prop} : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x :=
    ⟨by apply not_imp_symm; intro nE x; apply not_imp_symm _ nE; exact fun h => ⟨x, h⟩,
    fun ⟨x, hn⟩ hA => hn (hA x)⟩

end M4R