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
    have : ∀ p q, p ∨ q → q ∨ p := fun _ _ h => Or.elim h Or.inr Or.inl;
    exact ⟨this p q, this q p⟩

end M4R