import M4R.Logic

namespace Nat

  @[simp] theorem pred_zero : pred 0 = 0 := rfl
  @[simp] theorem pred_succ (n : Nat) : pred (succ n) = n := rfl

  protected theorem lt_one {n : Nat} (hn : n < 1) : n = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hn)

  protected theorem ne_of_lt {m n : Nat} : m < n → m ≠ n :=
    fun h h' => Nat.lt_irrefl n (by rw [h'] at h; exact h)

  protected theorem le_or_lt (m n : Nat) : m ≤ n ∨ n < m :=
    Or.elim (Nat.lt_or_ge n m) Or.inr Or.inl

  protected theorem lt_or_eq_of_le {m n : Nat} (h : m ≤ n) : m < n ∨ m = n :=
    Or.elim (Nat.lt_or_ge m n) Or.inl (fun h' => Or.inr (Nat.le_antisymm h h'))

  protected theorem le_of_add_le_add_left {k n m : Nat} (h : k + n ≤ k + m) : n ≤ m :=
    match le.dest h with
    | ⟨w, hw⟩ => @le.intro _ _ w (by rw [Nat.add_assoc] at hw; exact Nat.add_left_cancel hw)

  protected theorem le_of_add_le_add_right {k n m : Nat} : n + k ≤ m + k → n ≤ m := by
    rw [Nat.add_comm _ k, Nat.add_comm _ k]
    exact Nat.le_of_add_le_add_left

  protected theorem lt_of_add_lt_add_left {k n m : Nat} (h : k + n < k + m) : n < m :=
    Nat.lt_of_le_and_ne (Nat.le_of_add_le_add_left (Nat.le_of_lt h))
      (fun heq => Nat.lt_irrefl (k + m) (by rw [heq] at h; exact h))

  protected theorem lt_of_add_lt_add_right {a b c : Nat} (h : a + b < c + b) : a < c :=
    have : b + a < b + c := by rw [Nat.add_comm b a, Nat.add_comm b c]; exact h
    Nat.lt_of_add_lt_add_left this

  protected theorem le_iff_eq_or_lt {a b : Nat} : a ≤ b ↔ a = b ∨ a < b :=
    ⟨fun h => (Nat.lt_or_eq_of_le h).comm, fun h => Or.elim h (· ▸ Nat.le.refl) (Nat.le_of_lt)⟩

  protected theorem lt_succ_if_le {a b : Nat} : a < b.succ ↔ a ≤ b :=
    ⟨le_of_lt_succ, lt_succ_of_le⟩

  theorem succ_ne_self : ∀ n : Nat, succ n ≠ n
  | 0  , h => absurd h (Nat.succ_ne_zero 0)
  | n+1, h => succ_ne_self n (Nat.succ.inj h)

  theorem lt_add_right (n m k : Nat) (h : n < m) : n < m + k := by
    induction k with
    | zero      => rw [Nat.add_zero] exact h
    | succ k ih => rw [Nat.add_succ]; exact Nat.lt_succ_of_le (Nat.le_of_lt ih)

  theorem lt_add_left (n m k : Nat) (h : n < m) : n < k + m := by
    rw [Nat.add_comm]; exact lt_add_right n m k h

  @[simp] theorem zero_sub : ∀ a : Nat, 0 - a = 0
  | 0     => rfl
  | (a+1) => congrArg pred (zero_sub a)

  theorem succ_pred_eq_of_pos : ∀ {n : Nat}, n > 0 → n.pred.succ = n
  | 0, h      => absurd h (Nat.lt_irrefl 0)
  | succ k, h => rfl

  protected theorem add_left_cancel' {n m k : Nat} : n + m = n + k ↔ m = k :=
    ⟨Nat.add_left_cancel, congrArg (n + ·)⟩

  protected theorem add_right_cancel' {n m k : Nat} : n + m = k + m ↔ n = k :=
    ⟨Nat.add_right_cancel, congrArg (· + m)⟩

  theorem add_sub_add_right : ∀ (n k m : Nat), (n + k) - (m + k) = n - m
  | n, 0     , m => by rw [add_zero, add_zero]
  | n, succ k, m => by rw [add_succ, add_succ, succ_sub_succ, add_sub_add_right n k m]

  theorem add_sub_add_left (k n m : Nat) : (k + n) - (k + m) = n - m := by
    rw [Nat.add_comm k n, Nat.add_comm k m, add_sub_add_right]

  theorem add_sub_cancel (n m : Nat) : n + m - m = n := by
    have : n + m - (0 + m) = n := by
      rw [add_sub_add_right, Nat.sub_zero]
    rw [Nat.zero_add] at this
    exact this

  theorem sub_self_add (n m : Nat) : n - (n + m) = 0 :=
    have : (n + 0) - (n + m) = 0 := by rw [add_sub_add_left, Nat.zero_sub]
    this

  theorem sub_eq_zero_of_le {n m : Nat} (h : n ≤ m) : n - m = 0 := by
    let ⟨k, hk⟩ := le.dest h
    rw [←hk, Nat.sub_self_add]

  theorem le_of_sub_eq_zero : ∀ {n m : Nat}, n - m = 0 → n ≤ m
  | n    , 0    , H => by rw [Nat.sub_zero] at H; rw [H]; exact Nat.le_refl 0
  | 0    , (m+1), H => zero_le _
  | (n+1), (m+1), H => Nat.add_le_add_right (le_of_sub_eq_zero (by simp only [add_sub_add_right] at H; exact H )) _

  @[simp] theorem sub_eq_zero_iff_le (a b : Nat) : a - b = 0 ↔ a ≤ b :=
    ⟨le_of_sub_eq_zero, sub_eq_zero_of_le⟩

  theorem add_sub_cancel_left (n m : Nat) : n + m - n = m :=
    have : n + m - (n + 0) = m :=
      by rw [add_sub_add_left, Nat.sub_zero]
    this

  theorem sub_sub : ∀ (n m k : Nat), n - m - k = n - (m + k)
  | n, m, zero   => by rw [add_zero, Nat.sub_zero]
  | n, m, succ k => by rw [add_succ, sub_succ, sub_succ, sub_sub n m k]

  theorem add_sub_of_le {n m : Nat} (h : n ≤ m) : n + (m - n) = m := by
    let ⟨k, hk⟩ := le.dest h
    rw [← hk, add_sub_cancel_left]

  theorem sub_add_cancel {n m : Nat} (h : n ≥ m) : n - m + m = n := by
    rw [Nat.add_comm, add_sub_of_le h]

  theorem add_sub_assoc {m k : Nat} (h : k ≤ m) (n : Nat) : n + m - k = n + (m - k) := by
    rw [←Classical.choose_spec (le.dest h), add_sub_cancel_left, Nat.add_comm k, ←Nat.add_assoc, add_sub_cancel]

  theorem succ_sub {m n : Nat} (h : m ≥ n) : m.succ - n = (m - n).succ := by
    let ⟨k, hk⟩ := le.dest h
    rw [←hk, add_sub_cancel_left, ←add_succ, add_sub_cancel_left]

  theorem sub_pos_of_lt {m n : Nat} (h : m < n) : n - m > 0 :=
    have : 0 + m < n - m + m := by rw [Nat.zero_add, sub_add_cancel (Nat.le_of_lt h)]; exact h
    Nat.lt_of_add_lt_add_right this

  theorem sub_pred {m n : Nat} (h₁ : 0 < n) (h₂ : n ≤ m) : m - n.pred = (m - n).succ := by
    cases n with
    | zero   => contradiction
    | succ n =>
      rw [Nat.pred_succ, Nat.sub_succ, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₂)]

  theorem lt_of_sub_eq_succ {m n l : Nat} (H : m - n = succ l) : n < m :=
    gt_of_not_le (mt (@sub_eq_zero_of_le m n) (fun h => by rw [h] at H; contradiction))

  theorem sub_eq_iff_eq_add {a b c : Nat} (ab : b ≤ a) : a - b = c ↔ a = c + b :=
    ⟨fun h => by rw [←h, sub_add_cancel ab], fun h => by rw [h, add_sub_cancel]⟩

  theorem eq_sub_iff_add_eq {a b c : Nat} (bc : c ≤ b) : a = b - c ↔ a + c = b :=
    ⟨fun h => ((sub_eq_iff_eq_add bc).mp h.symm).symm, fun h => ((sub_eq_iff_eq_add bc).mpr h.symm).symm⟩

  theorem mul_pred_left : ∀ (n m : Nat), n.pred * m = n * m - m
  | zero  , m => by simp
  | succ n, m => by rw [pred_succ, succ_mul, add_sub_cancel]

  theorem mul_sub_right_distrib : ∀ (n m k : Nat), (n - m) * k = n * k - m * k
  | n, zero  , k => by simp
  | n, succ m, k => by rw [sub_succ, mul_pred_left, mul_sub_right_distrib, succ_mul, sub_sub]

  theorem mul_sub_left_distrib (n m k : Nat) : n * (m - k) = n * m - n * k := by
    rw [Nat.mul_comm, mul_sub_right_distrib, Nat.mul_comm m n, Nat.mul_comm n k]

  theorem pos_iff_ne_zero {n : Nat} : 0 < n ↔ n ≠ 0 :=
    ⟨fun h => (Nat.ne_of_lt h).symm,
    fun h => Nat.lt_of_le_and_ne (Nat.zero_le n) h.symm⟩

  theorem ge_one_iff_ne_zero {n : Nat} : 1 ≤ n ↔ n ≠ 0 := by
    rw [←pos_iff_ne_zero]; exact Iff.rfl

  protected theorem sub_one (n : Nat) : n - 1 = pred n := rfl

  theorem one_add (n : Nat) : 1 + n = succ n :=
    (Nat.add_comm 1 n).trans (add_one n)

  theorem pred_sub (n m : Nat) : pred n - m = pred (n - m) := by
    rw [←Nat.sub_one, sub_sub, one_add, sub_succ]

  theorem le_of_not_ge {a b : Nat} : ¬ a ≥ b → a ≤ b :=
    Or.resolve_left (Nat.le_total b a)

  theorem le_of_not_le {a b : Nat} : ¬ a ≤ b → b ≤ a :=
    Or.resolve_left (Nat.le_total a b)

  theorem lt_trichotomy (a b : Nat) : a < b ∨ a = b ∨ b < a :=
    Or.elim (Nat.le_total a b)
      (fun h : a ≤ b => Or.elim (Nat.lt_or_eq_of_le h)
        (fun h : a < b => Or.inl h)
        (fun h : a = b => Or.inr (Or.inl h)))
      (fun h : b ≤ a => Or.elim (Nat.lt_or_eq_of_le h)
        (fun h : b < a => Or.inr (Or.inr h))
        (fun h : b = a => Or.inr (Or.inl h.symm)))

  theorem le_of_not_lt {a b : Nat} (h : ¬ b < a) : a ≤ b := by
    cases lt_trichotomy a b with
    | inl hlt => exact Nat.le_of_lt hlt
    | inr h =>
      cases h with
      | inl heq => exact heq ▸ Nat.le_refl a
      | inr hgt => exact absurd hgt h

  theorem le_of_not_gt {a b : Nat} : ¬ a > b → a ≤ b := le_of_not_lt

  theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
    fun hab => Nat.not_le_of_gt hab h

  @[simp] theorem not_lt {a b : Nat} : ¬ a < b ↔ b ≤ a :=
    ⟨le_of_not_gt, not_lt_of_ge⟩

  theorem not_lt_of_gt {a b : Nat} : a > b → ¬ a ≤ b :=
    fun h₁ h₂ => absurd h₁ (not_lt_of_ge h₂)

  @[simp] theorem not_le {a b : Nat} : ¬ a ≤ b ↔ b < a :=
    ⟨gt_of_not_le, not_lt_of_gt⟩

  theorem add_eq_zero {a b : Nat} : a + b = 0 ↔ a = 0 ∧ b = 0 :=
    ⟨fun h => by
      induction a with
      | zero => rw [Nat.zero_add] at h; exact ⟨rfl, h⟩
      | succ k ih => rw [succ_add] at h; exact absurd h (succ_ne_zero (k+b)),
    fun ⟨ha, hb⟩ => by rw [ha, hb]⟩

  theorem add_eq_one {a b : Nat} : a + b = 1 ↔ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
    cases a with
    | zero   =>
      simp only [Nat.zero_eq, Nat.zero_add, false_and, false_or, true_and]; exact Iff.rfl
    | succ a =>
      simp only [false_and, or_false]
      cases a with
      | zero   =>
        conv => lhs rhs rw [←Nat.add_zero 1]
        rw [Nat.add_left_cancel']; simp only [true_and]; exact Iff.rfl
      | succ a =>
        have : ∀ n : Nat, ¬ n.succ.succ = 1 := fun n h => absurd (Nat.succ.inj h) (Nat.succ_ne_zero n)
        simp only [Nat.succ_add, this, false_and]

  theorem mul_eq_zero (a b : Nat) : a * b = 0 ↔ a = 0 ∨ b = 0 :=
    ⟨fun h => by
      induction a with
      | zero      => exact Or.inl rfl
      | succ k ih => rw [succ_mul, add_eq_zero] at h; exact Or.inr h.right,
    fun h => by
      cases h with
      | inl h => rw [h, Nat.zero_mul]
      | inr h => rw [h, Nat.mul_zero]⟩

  theorem mul_neq_zero (a b : Nat) : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
    rw [←M4R.not_or_iff_and_not, M4R.not_iff_not]; exact mul_eq_zero a b

  theorem add_le {a b : Nat} : a + b ≤ a ↔ b = 0 :=
    ⟨fun h => by
      conv at h => rhs rw [←Nat.add_zero a]
      exact Nat.eq_zero_of_le_zero (Nat.le_of_add_le_add_left h),
    fun h => by rw [h, Nat.add_zero]; exact Nat.le_refl a⟩

  theorem lt_not_symm {a b : Nat} : ¬(a < b ∧ b < a) := by
    rw [M4R.not_and_iff_or_not, Nat.not_lt, Nat.not_lt]; exact Nat.le_total b a

  theorem add_sub_comm {a b c : Nat} (h : c ≤ a) : a + b - c = a - c + b := by
    induction b with
    | zero      => rw [Nat.add_zero, Nat.add_zero]
    | succ b ih =>
      rw [Nat.add_succ, Nat.add_succ, ←ih, Nat.succ_sub]
      exact Nat.add_zero _ ▸ Nat.add_le_add h (Nat.zero_le b)

  section choose

    protected def choose : Nat → Nat → Nat
    | _    ,     0 => 1
    | 0    , k + 1 => 0
    | n + 1, k + 1 => Nat.choose n k + Nat.choose n (k + 1)

    @[simp] theorem choose_zero_right (n : Nat) : n.choose 0 = 1 := by
      cases n; rfl; rfl

    theorem choose_zero_right_succ (n : Nat) : n.choose 0 = n.succ.choose 0 := by
      rw [choose_zero_right, choose_zero_right]

    @[simp] theorem choose_zero_succ (k : Nat) : (0 : Nat).choose k.succ = 0 := rfl

    theorem choose_succ_succ (n k : Nat) : n.succ.choose k.succ = n.choose k + n.choose (succ k) := rfl

    theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → n.choose k = 0
    | _    ,     0, hk => absurd hk (Nat.not_lt_zero _)
    | 0    , k + 1, hk => choose_zero_succ _
    | n + 1, k + 1, hk => by
      rw [choose_succ_succ, choose_eq_zero_of_lt (lt_of_succ_lt_succ hk),
        choose_eq_zero_of_lt (lt_of_succ_lt hk)]

    @[simp] theorem choose_self (n : Nat) : n.choose n = 1 := by
      induction n with
      | zero      => rfl
      | succ n ih => simp only [Nat.choose]; rw [ih, choose_eq_zero_of_lt (lt_succ_self n)]

    theorem choose_self_succ (n : Nat) : n.choose n = n.succ.choose n.succ := by
      rw [choose_self, choose_self]

    @[simp] theorem choose_succ_self (n : Nat) : n.choose n.succ = 0 :=
      choose_eq_zero_of_lt (lt_succ_self _)

    @[simp] theorem choose_one_right (n : Nat) : n.choose 1 = n := by
      induction n with
      | zero => rfl
      | succ n ih => simp only [Nat.choose]; rw [ih, choose_zero_right, one_add]

    theorem choose_pred {n k : Nat} (h : 0 < k) : n.choose k + n.choose k.pred = n.succ.choose k := by
      cases k with
      | zero => contradiction
      | succ k => rw [Nat.pred_succ, Nat.add_comm]; rfl

  end choose

  theorem le_succ_pred (n : Nat) : n ≤ n.pred.succ := by
    byCases h : n > 0
    { exact Nat.le_of_eq (succ_pred_eq_of_pos h).symm }
    { exact Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h) ▸ Nat.zero_le _ }

  theorem pred_le_iff {n m : Nat} : n.pred ≤ m ↔ n ≤ m.succ :=
    ⟨fun h => Nat.le_trans (le_succ_pred n) (succ_le_succ h),
     fun h => by cases n with
      | zero   => exact Nat.zero_le m
      | succ n => exact Nat.le_of_succ_le_succ h⟩
  
  theorem le_pred_iff {n m : Nat} (hm : m > 0) : n ≤ m.pred ↔ n.succ ≤ m :=
    ⟨fun h => succ_pred_eq_of_pos hm ▸ Nat.succ_le_succ h,
     fun h => by cases m with
      | zero   => exact absurd hm (Nat.lt_irrefl 0)
      | succ m => exact Nat.le_of_succ_le_succ h⟩
  
  theorem sub_le_iff_right {a b c : Nat} : a - c ≤ b ↔ a ≤ b + c := by
    induction c generalizing b with
    | zero      => rw [Nat.sub_zero, Nat.add_zero]; exact Iff.rfl
    | succ c ih => rw [sub_succ, add_succ, ←succ_add, pred_le_iff]; exact ih

  theorem le_zero {n : Nat} : n ≤ 0 ↔ n = 0 :=
    ⟨Nat.eq_zero_of_le_zero, (· ▸ Nat.le_refl n)⟩

  theorem le_sub_iff_right {a b c : Nat} (h : c ≤ b) : a ≤ b - c ↔ a + c ≤ b := by
    induction c generalizing a with
    | zero      => rw [Nat.sub_zero, Nat.add_zero]; exact Iff.rfl
    | succ c ih =>
      rw [sub_succ, add_succ, ←succ_add, le_pred_iff (sub_pos_of_lt h)]
      exact ih (Nat.le_trans (Nat.le_succ c) h)

  theorem sub_le_sub {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : a ≤ b ↔ c - b ≤ c - a := by
    rw [sub_le_iff_right, Nat.add_comm, ←add_sub_assoc ha, le_sub_iff_right
      (Nat.le_trans ha (Nat.le_add_left c b)), Nat.add_comm]
    exact ⟨(Nat.add_le_add_right · c), Nat.le_of_add_le_add_right⟩

  theorem lt_sub_iff_right {a b c : Nat} (h : c ≤ b) : a < b - c ↔ a + c < b :=
    ⟨fun h' => Nat.lt_of_le_and_ne ((le_sub_iff_right h).mp (Nat.le_of_lt h'))
      (fun h'' => absurd ((eq_sub_iff_add_eq h).mpr h'') (Nat.ne_of_lt h')),
    fun h' => Nat.lt_of_le_and_ne ((le_sub_iff_right h).mpr (Nat.le_of_lt h'))
      (fun h'' => absurd ((eq_sub_iff_add_eq h).mp h'') (Nat.ne_of_lt h'))⟩

  theorem sub_lt_iff_right {a b c : Nat} (h : c ≤ a) : a - c < b ↔ a < b + c := by
    apply M4R.not_iff_not.mp
    simp only [Nat.not_lt]
    exact le_sub_iff_right h

  theorem zero_lt_iff_neq_zero {n : Nat} : 0 < n ↔ n ≠ 0 :=
    ⟨fun h₁ h₂ => absurd (h₂ ▸ h₁) (Nat.lt_irrefl 0), fun h => by
      cases n; contradiction; exact Nat.zero_lt_succ _⟩

  theorem lt.dest {m n : Nat} (h : m < n) : ∃ k, k ≠ 0 ∧ m + k = n :=
    let ⟨k, hk⟩ := le.dest (Nat.le_of_lt h)
    ⟨k, fun h' => absurd ((h' ▸ hk : m + 0 = n) ▸ h) (Nat.lt_irrefl n), hk⟩

  theorem ne_zero_dest {m : Nat} (h : m ≠ 0) : ∃ k, m = k + 1 :=
    ⟨m.pred, (succ_pred_eq_of_pos (pos_iff_ne_zero.mpr h)).symm⟩

  theorem of_lt_add_left {n m : Nat} (h : n < m + n) : 0 < m :=
    Nat.sub_self n ▸ (sub_lt_iff_right (Nat.le_refl n)).mpr h

  theorem of_lt_add_right {n m : Nat} (h : n < n + m) : 0 < m :=
    of_lt_add_left (Nat.add_comm n m ▸ h : n < m + n)

  theorem lt_add_pos_left (n : Nat) {m : Nat} (h : m ≠ 0) : n < m + n :=
    Nat.lt_of_le_and_ne (le_add_left n m)
      (fun h' => absurd (Nat.sub_self n ▸ (sub_eq_iff_eq_add (Nat.le_refl n)).mpr h') h.symm)

  theorem lt_add_pos_right (n : Nat) {m : Nat} (h : m ≠ 0) : n < n + m :=
    Nat.add_comm n m ▸ lt_add_pos_left n h

  theorem sub_pos_iff_lt {m n : Nat} : 0 < m - n ↔ n < m :=
    (pos_iff_ne_zero.trans (M4R.not_iff_not.mpr (sub_eq_zero_iff_le m n))).trans Nat.not_le

end Nat

namespace Int

  /- Helper "packing" theorems -/
  @[simp] theorem zero_eq : ofNat 0 = 0 := rfl
  @[simp] theorem one_eq : ofNat 1 = 1 := rfl
  @[simp] theorem add_eq : Int.add x y = x + y := rfl
  @[simp] theorem sub_eq : Int.sub x y = x - y := rfl
  @[simp] theorem mul_eq : Int.mul x y = x * y := rfl
  @[simp] theorem neg_eq : Int.neg x = - x := rfl
  @[simp] theorem lt_eq : Int.lt x y = (x < y) := rfl
  @[simp] theorem le_eq : Int.le x y = (x ≤ y) := rfl

  @[simp] theorem negOfNat_of_succ (n : Nat) : -(ofNat n.succ) = negSucc n := rfl
  @[simp] theorem ofNat_add_ofNat (m n : Nat) : ofNat m + ofNat n = ofNat (m + n) := rfl
  @[simp] theorem ofNat_add_negSucc_ofNat (m n : Nat) :
                  ofNat m + negSucc n = subNatNat m (n.succ) := rfl
  @[simp] theorem negSucc_ofNat_add_ofNat (m n : Nat) :
                  negSucc m + ofNat n = subNatNat n (m.succ) := rfl
  @[simp] theorem negSucc_ofNat_add_negSucc_ofNat (m n : Nat) :
                  negSucc m + negSucc n = negSucc (m + n).succ := rfl

  @[simp] theorem ofNat_mul_ofNat (m n : Nat) : ofNat m * ofNat n = ofNat (m * n) := rfl
  @[simp] theorem ofNat_mul_negSucc_ofNat (m n : Nat) :
                  ofNat m * negSucc n = negOfNat (m * n.succ) := rfl
  @[simp] theorem negSucc_ofNat_ofNat (m n : Nat) :
                  negSucc m * ofNat n = negOfNat (m.succ * n) := rfl
  @[simp] theorem mul_negSucc_ofNat_negSucc_ofNat (m n : Nat) :
                negSucc m * negSucc n = ofNat (m.succ * n.succ) := rfl

  @[simp] protected theorem neg_zero : - (0 : Int) = 0 := rfl
  @[simp] protected theorem negOfNat_zero : negOfNat 0 = 0 := rfl

  @[simp] theorem subNatNat_self: ∀ n : Nat, subNatNat n n = 0
  | 0            => rfl
  | (Nat.succ m) => by simp only [subNatNat, Nat.sub_self]

  @[simp] protected theorem add_neg : ∀ n : Int, n + -n = 0
  | ofNat 0 => rfl
  | ofNat (Nat.succ k) => by
    simp only [Neg.neg, Int.neg, negOfNat, HAdd.hAdd, Add.add, Int.add, subNatNat_self]
  | negSucc k => by
    simp only [Neg.neg, Int.neg, negOfNat, HAdd.hAdd, Add.add, Int.add, subNatNat_self]

  protected theorem add_comm : ∀ m n : Int, m + n = n + m
  | ofNat   m', ofNat   n' => by simp [Nat.add_comm]
  | ofNat   m', negSucc n' => rfl
  | negSucc m', ofNat   n' => rfl
  | negSucc m', negSucc n' => by simp [Nat.add_comm]

  @[simp] protected theorem add_zero : ∀ n : Int, n + 0 = n
  | ofNat   k => rfl
  | negSucc k => rfl

  @[simp] protected theorem zero_add : ∀ n : Int, 0 + n = n :=
    fun n => by rw [Int.add_comm, Int.add_zero]

  theorem subNatNat_elim (m n : Nat) (P : Nat → Nat → Int → Prop)
    (hp : ∀ i n : Nat, P (n + i) n (ofNat i))
    (hn : ∀ i m : Nat, P m (m + i + 1) (negSucc i)) :
    P m n (subNatNat m n) := by
      have H : ∀ k : Nat, n - m = k → P m n (subNatNat m n) := by
        intro k; simp only [subNatNat]; cases k with
        | zero =>
          intro e; simp only [e]
          cases (Nat.le.dest (Nat.le_of_sub_eq_zero e)) with
          | intro k h =>
            rw [h.symm, Nat.add_sub_cancel_left];
            exact hp k n
        | succ k' =>
          intro heq; simp only [heq]
          have h : m ≤ n := Nat.le_of_lt (Nat.lt_of_sub_eq_succ heq)
          rw [Nat.sub_eq_iff_eq_add h] at heq
          rw [heq, Nat.add_comm]
          exact hn k' m
      exact H (n - m) rfl

  theorem subNatNat_add_left {m n : Nat} : subNatNat (m + n) m = ofNat n := by
    simp only [subNatNat]
    rw [Nat.sub_eq_zero_of_le, Nat.add_sub_cancel_left]
    exact Nat.le_add_right m n

  theorem subNatNat_add_right {m n : Nat} : subNatNat m (m + n + 1) = negSucc n := by
    simp only [subNatNat, Nat.add_assoc, Nat.add_sub_cancel_left]; rfl

  theorem subNatNat_add_add (m n k : Nat) : subNatNat (m + k) (n + k) = subNatNat m n :=
    subNatNat_elim m n (fun m n i => subNatNat (m + k) (n + k) = i)
      (fun i n => by
        have : n + i + k = (n + k) + i := by simp only [Nat.add_comm, Nat.add_left_comm]
        simp only [this]; exact subNatNat_add_left)
      (fun i m => by
        have : m + i + 1 + k = (m + k) + i + 1 := by simp only [Nat.add_comm, Nat.add_left_comm]
        simp only [this]; exact subNatNat_add_right)

  theorem subNatNat_of_sub_eq_zero {m n : Nat} (h : n - m = 0) : subNatNat m n = ofNat (m - n) := by
    simp only [subNatNat, h]

  theorem subNatNat_of_sub_eq_succ {m n k : Nat} (h : n - m = k.succ) : subNatNat m n = negSucc k := by
    simp only [subNatNat, h]

  theorem subNatNat_of_ge {m n : Nat} (h : m ≥ n) : subNatNat m n = ofNat (m - n) :=
    subNatNat_of_sub_eq_zero (Nat.sub_eq_zero_of_le h)

  theorem subNatNat_of_lt {m n : Nat} (h : m < n) : subNatNat m n = negSucc (n - m).pred := by
    rw [subNatNat_of_sub_eq_succ];
    exact Eq.symm (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h))

  theorem subNatNat_sub {m n : Nat} (h : m ≥ n) (k : Nat) : subNatNat (m - n) k = subNatNat m (k + n) := by
      rw [←subNatNat_add_add (m-n) k n, Nat.sub_add_cancel h]

  theorem subNatNat_add (m n k : Nat) : subNatNat (m + n) k = ofNat m + subNatNat n k := by
    cases Nat.le_or_lt k n with
    | inl h =>
      rw [subNatNat_of_ge h]
      have h₂ : k ≤ m + n := (Nat.le_trans h (Nat.le_add_left _ _))
      simp [subNatNat_of_ge h₂, Nat.add_sub_assoc h]
    | inr h =>
      rw [subNatNat_of_lt h, ofNat_add_negSucc_ofNat, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]
      have := subNatNat_add_add m (k - n) n
      rw [Nat.sub_add_cancel (Nat.le_of_lt h)] at this
      exact this

  theorem subNatNat_add_negSucc_ofNat (m n k : Nat) : subNatNat m n + negSucc k = subNatNat m (n + k.succ) := by
    cases Nat.le_or_lt n m with
    | inl h => rw [subNatNat_of_ge h, ofNat_add_negSucc_ofNat, subNatNat_sub h, Nat.add_comm]
    | inr h =>
      have h₂ : m < n + k.succ := Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
      have h₃ : m ≤ n + k := Nat.le_of_succ_le_succ h₂
      rw [subNatNat_of_lt h, subNatNat_of_lt h₂]; simp; rw [Nat.add_comm, ←Nat.add_succ,
        Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), Nat.add_succ, Nat.succ_sub h₃,
        Nat.pred_succ, Nat.add_comm n, Nat.add_sub_assoc (Nat.le_of_lt h)]

  private theorem add_assoc₁ (a b : Nat) : ∀ c : Int, ofNat a + ofNat b + c = ofNat a + (ofNat b + c)
  | ofNat   c => by simp [Nat.add_assoc]
  | negSucc c => by simp [subNatNat_add]

  private theorem add_assoc₂ (a b c : Nat) : negSucc a + negSucc b + ofNat c = negSucc a + (negSucc b + ofNat c) := by
    rw [negSucc_ofNat_add_negSucc_ofNat, Int.add_comm, ofNat_add_negSucc_ofNat,
      Int.add_comm (negSucc b), ofNat_add_negSucc_ofNat, Int.add_comm, subNatNat_add_negSucc_ofNat,
      Nat.add_succ, Nat.succ_add, Nat.add_comm]

  protected theorem add_assoc : ∀ a b c : Int, a + b + c = a + (b + c)
  | ofNat   a, ofNat   b,         c => add_assoc₁ a b c
  | ofNat   a,         b, ofNat   c => by
    rw [Int.add_comm, ←add_assoc₁, Int.add_comm (ofNat c), add_assoc₁, Int.add_comm b]
  |         a, ofNat   b, ofNat   c => by 
    rw [Int.add_comm, Int.add_comm a, ←add_assoc₁, Int.add_comm a, Int.add_comm (ofNat c)]
  | negSucc a, negSucc b, ofNat   c => add_assoc₂ a b c
  | negSucc a, ofNat   b, negSucc c => by
    rw [Int.add_comm, ←add_assoc₂, Int.add_comm (ofNat b), ←add_assoc₂, Int.add_comm (negSucc a)]
  | ofNat   a, negSucc b, negSucc c => by
    rw [Int.add_comm, Int.add_comm (ofNat a), Int.add_comm (ofNat a), ←add_assoc₂, Int.add_comm (negSucc c)]
  | negSucc a, negSucc b, negSucc c => by
    simp [Nat.succ_eq_add_one] rw [Nat.add_right_comm b, ←Nat.add_assoc, ←Nat.add_assoc]

  protected theorem mul_comm : ∀ a b : Int, a * b = b * a
  | ofNat   a, ofNat   b => by simp [Nat.mul_comm]
  | ofNat   a, negSucc b => by simp [Nat.mul_comm]
  | negSucc a, ofNat   b => by simp [Nat.mul_comm]
  | negSucc a, negSucc b => by simp [Nat.mul_comm]

  @[simp] protected theorem mul_one : ∀ a : Int, a * 1 = a
  | ofNat   a => by simp [HMul.hMul, Mul.mul, Int.mul]; exact Nat.mul_one a
  | negSucc a => by simp [HMul.hMul, Mul.mul, Int.mul, negOfNat]; rw [Nat.mul_one a.succ]

  @[simp] protected theorem one_mul : ∀ a : Int, 1 * a = a :=
    fun a => Int.mul_comm a 1 ▸ Int.mul_one a

  @[simp] protected theorem mul_zero : ∀ a : Int, a * 0 = 0
  | ofNat   m => rfl
  | negSucc m => rfl

  @[simp] protected theorem zero_mul : ∀ a : Int, 0 * a = 0 :=
    fun a => Int.mul_comm a 0 ▸ Int.mul_zero a

  theorem negOfNat_eq_subNatNat_zero : ∀ n, negOfNat n = subNatNat 0 n
  | Nat.zero   => rfl
  | Nat.succ n => rfl

  @[simp] theorem ofNat_mul_negOfNat (m : Nat) : ∀n, ofNat m * negOfNat n = negOfNat (m * n)
  | Nat.zero   => rfl
  | Nat.succ n => by simp [negOfNat]

  @[simp] theorem negOfNat_mul_ofNat (m n : Nat) : negOfNat m * ofNat n = negOfNat (m * n) := by
    rw [Int.mul_comm]; simp only [ofNat_mul_negOfNat, Nat.mul_comm]

  @[simp] theorem negSucc_ofNat_mul_negOfNat (m : Nat) : ∀ n, negSucc m * negOfNat n = ofNat (m.succ * n)
  | Nat.zero   => rfl
  | Nat.succ n => by simp [negOfNat]

  @[simp] theorem negOfNat_mul_negSucc_ofNat (m n : Nat) : negOfNat n * negSucc m = ofNat (n * m.succ) := by
    rw [Int.mul_comm]; simp [negSucc_ofNat_mul_negOfNat, Nat.mul_comm]

  @[simp] theorem ofNat_mul_subNatNat (m n k : Nat) : ofNat m * subNatNat n k = subNatNat (m * n) (m * k) := by
    cases Nat.eq_zero_or_pos m with
    | inl h => simp [h]
    | inr h =>
      cases Nat.lt_or_ge n k with
      | inl h' =>
        have : m * n < m * k := Nat.mul_lt_mul_of_pos_left h' h
        rw [subNatNat_of_lt h', subNatNat_of_lt this]; simp
        rw [Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h'),
          ←negOfNat_of_succ, Nat.mul_sub_left_distrib,
          Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt this)]; rfl
      | inr h' =>
        have : m * k ≤ m * n := Nat.mul_le_mul_left _ h'
        rw [subNatNat_of_ge h', subNatNat_of_ge this]; simp
        rw [Nat.mul_sub_left_distrib]

  @[simp] theorem negOfNat_add : ∀ (m n : Nat), negOfNat m + negOfNat n = negOfNat (m + n)
  | Nat.zero  ,          n   => by simp
  | Nat.succ m,          0 => by simp
  | Nat.succ m, Nat.succ n => by simp [Nat.succ_add]; rfl

  @[simp] theorem negSucc_ofNat_mul_subNatNat (m n k : Nat) :
    negSucc m * subNatNat n k = subNatNat (m.succ * k) (m.succ * n) := by
      cases Nat.lt_or_ge n k with
      | inl h =>
        have h' : m.succ * n < m.succ * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
        rw [subNatNat_of_lt h, subNatNat_of_ge (Nat.le_of_lt h')]
        simp [Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), Nat.mul_sub_left_distrib]
      | inr h =>
        cases Nat.lt_or_eq_of_le h with
        | inl h' =>
          have h₁ : m.succ * n > m.succ * k := Nat.mul_lt_mul_of_pos_left h' (Nat.succ_pos m)
          rw [subNatNat_of_ge h, subNatNat_of_lt h₁]; simp [Nat.mul_sub_left_distrib, Nat.mul_comm]
          rw [Nat.mul_comm k, Nat.mul_comm n, ←Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁),
              ←negOfNat_of_succ]; rfl
        | inr h' => rw [h']; simp

  protected theorem mul_assoc : ∀ a b c : Int, (a * b) * c = a * (b * c)
  | ofNat   a, ofNat   b, ofNat   c => by simp [Nat.mul_assoc]
  | ofNat   a, ofNat   b, negSucc c => by simp [Nat.mul_assoc]
  | ofNat   a, negSucc b, ofNat   c => by simp [Nat.mul_assoc]
  | ofNat   a, negSucc b, negSucc c => by simp [Nat.mul_assoc]
  | negSucc a, ofNat   b, ofNat   c => by simp [Nat.mul_assoc]
  | negSucc a, ofNat   b, negSucc c => by simp [Nat.mul_assoc]
  | negSucc a, negSucc b, ofNat   c => by simp [Nat.mul_assoc]
  | negSucc a, negSucc b, negSucc c => by simp [Nat.mul_assoc]

  protected theorem mul_distrib_left : ∀ a b c : Int, a * (b + c) = a * b + a * c
  | ofNat   a, ofNat   b, ofNat   c => by simp [Nat.left_distrib]
  | ofNat   a, ofNat   b, negSucc c => by simp [negOfNat_eq_subNatNat_zero]; rw [←subNatNat_add]; rfl
  | ofNat   a, negSucc b, ofNat   c => by simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ←subNatNat_add]; rfl
  | ofNat   a, negSucc b, negSucc c => by simp; rw [←Nat.left_distrib, Nat.succ_add, Nat.add_succ]
  | negSucc a, ofNat   b, ofNat   c => by simp [Nat.mul_comm]; rw [←Nat.right_distrib, Nat.mul_comm]
  | negSucc a, ofNat   b, negSucc c => by simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ←subNatNat_add]; rfl
  | negSucc a, negSucc b, ofNat   c => by simp [negOfNat_eq_subNatNat_zero]; rw [←subNatNat_add]; rfl
  | negSucc a, negSucc b, negSucc c => by simp; rw [←Nat.left_distrib, Nat.succ_add, Nat.add_succ]

  protected theorem mul_distrib_right : ∀ a b c : Int, (a + b) * c = a * c + b * c := fun a b c => by
    rw [Int.mul_comm, Int.mul_distrib_left]; simp [Int.mul_comm]

end Int
