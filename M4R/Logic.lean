namespace M4R

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

  theorem Or.comm : p ∨ q ↔ q ∨ p := by
    have : ∀ {p q}, p ∨ q → q ∨ p := fun h => Or.elim h Or.inr Or.inl;
    exact ⟨this, this⟩

  theorem And.comm : a ∧ b ↔ b ∧ a := by
    have : ∀ {p q}, p ∧ q → q ∧ p := fun ⟨p, q⟩ => ⟨q, p⟩
    exact ⟨this, this⟩

  @[simp] theorem exists_imp_distrib {p : α → Prop} : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
    ⟨fun h x hpx => h ⟨x, hpx⟩, fun h ⟨x, hpx⟩ => h x hpx⟩

  @[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
    Iff.intro (fun h ha hb => h ⟨ha, hb⟩) (fun h ⟨ha, hb⟩ => h ha hb)

end M4R