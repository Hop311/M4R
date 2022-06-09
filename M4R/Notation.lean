namespace M4R
  /-- Class defining a membership predicate, allowing the use of `∈` notation. -/
  class Mem (α : outParam (Type u)) (γ : Type v) where
    mem : α → γ → Prop
  infixl:55 " ∈ " => Mem.mem
  notation:55 x:55 " ∉ " s:56 => ¬ (x ∈ s)

  declare_syntax_cat binderterm -- notation for `a` or `a : A` or `a ∈ S`
  syntax ident : binderterm
  syntax ident " ∈ " term : binderterm
  syntax ident " ∉ " term : binderterm

  syntax "∀ " binderterm ", " term : term
  syntax "∃ " binderterm ", " term : term

  macro_rules
  -- ∀ x ∈ s, p := ∀ x, x ∈ s → p
  | `(∀ $x:ident ∈ $s, $p) => `(∀ $x:ident, $x ∈ $s → $p)
  -- ∃ x ∈ s, p := ∃ x, x ∈ s ∧ p
  | `(∃ $x:ident ∈ $s, $p) => `(∃ $x:ident, $x ∈ $s ∧ $p)
  -- ∀ x ∉ s, p := ∀ x, x ∉ s → p
  | `(∀ $x:ident ∉ $s, $p) => `(∀ $x:ident, $x ∉ $s → $p)
  -- ∃ x ∉ s, p := ∃ x, x ∉ s ∧ p
  | `(∃ $x:ident ∉ $s, $p) => `(∃ $x:ident, $x ∉ $s ∧ $p)

  /-- Class defining a subset predicate, allowing the use of `⊆` notation. -/
  class Subset (α : Type u) where
    subset : α → α → Prop
  infix:50 " ⊆ " => Subset.subset

  /-- Class defining a propert subset predicate, allowing the use of `⊊` notation. -/
  class ProperSubset (α : Type u) where
    propersubset : α → α → Prop
  infix:50 " ⊊ " => ProperSubset.propersubset

  /-- Class defining a not subset predicate, allowing the use of `⊈` notation. -/
  class NotSubset (α : Type u) where
     notsubset : α → α → Prop
  infix:50 " ⊈ " => NotSubset.notsubset

  /-- Class defining a union operation, allowing the use of `∪` notation. -/
  class Union (α : Type u) where
    union : α → α → α
  infixl:65 " ∪ " => Union.union

  /-- Class defining an intersection operation, allowing the use of `∩` notation. -/
  class Intersection (α : Type u) where
    intersection : α → α → α
  infixl:70 " ∩ " => Intersection.intersection

  /-- Class defining a set difference operation, allowing the use of `∖` notation. -/
  class SetMinus (α : Type u) where
    setminus : α → α → α
  infix:70 " ∖ " => SetMinus.setminus

  /-- Class defining a complement operation, allowing the use of `ᶜ` notation. -/
  class Complement (α : Type u) where
    complement : α → α
  postfix:max " ᶜ " => Complement.complement

  /- Notation for sets -/
  syntax "{ " ident " | " term " }" : term
  syntax "{ " ident ":" term " | " term " }" : term
  syntax "{ " ident "∈" term " | " term " }" : term
  macro_rules
  -- {a : A | p a}
  | `({ $x:ident : $t | $p }) => `(fun ($x:ident : $t) => $p)
  -- {a | p a}
  | `({ $x:ident | $p }) => `(fun ($x:ident) => $p)
  -- {a ∈ s | p a} := {a | a ∈ s ∧ p a}
  | `({ $x:ident ∈ $s | $p }) => `(fun $x => $x ∈ $s ∧ $p)

  /-- Class defining an inverse operation, allowing the use of `⁻¹` notation. -/
  class Inv (α : Type u) where
    inv : α → α
  postfix:max " ⁻¹ " => Inv.inv

  /-- Class defining a zero element, represented by the notation `0`. -/
  class Zero (α : Type _) where
    zero : α
  /-- Class defining a one element, represented by the notation `1`. -/
  class One  (α : Type _) where
    one  : α
  /-- The natural literal `0` can be interpreted as the element `0` of `Zero α`. -/
  instance Nat0 [Zero α] : OfNat α (nat_lit 0) where
    ofNat := Zero.zero
  /-- The natural literal `1` can be interpreted as the element `1` of `One α`. -/
  instance Nat1 [One  α] : OfNat α (nat_lit 1) where
    ofNat := One.one
  /-- A type with a zero element is inhabited. -/
  instance InhabitedZero [Zero α] : Inhabited α where default := 0
  /-- A type with a one element is inhabited. -/
  instance InhabitedOne  [One α]  : Inhabited α where default := 1
  /-- The natural number `0` is the zero element of `Nat`. -/
  instance NatZero : Zero Nat where zero := 0
  /-- The natural number `1` is the one element of `Nat`. -/
  instance NatOne  : One  Nat where one  := 1
  /-- The integer `0` is the zero element of `Int`. -/
  instance IntZero : Zero Int where zero := 0
  /-- The integer `1` is the one element of `Int`. -/
  instance IntOne  : One  Int where one  := 1

  /-- Class defining a type with a zero and one element which are not equal. -/
  class NonTrivial (α : Type _) [Zero α] [One α] where
    one_neq_zero : (1 : α) ≠ 0
  /-- The zero and one elements of `Nat` are not equal. -/
  instance NatNonTrivial : NonTrivial Nat where one_neq_zero := Nat.one_ne_zero
  /-- The zero and one elements of `Int` are not equal. -/
  instance IntNonTrivial : NonTrivial Int where one_neq_zero := by simp

  /-- Class defining a division predicate, allowing the use of `÷` notation. -/
  class Divides (α : Type u) where
    divides : α → α → Prop
  infix:55 " ÷ " => Divides.divides

  /-- Class defining a "ring equal" predicate, allowing the use of `≗` notation (used for associates). -/
  class RingEq (α : Type u) where
    ringeq : α → α → Prop
  infix:55 " ≗ " => RingEq.ringeq -- ≗ written \=o

  syntax "∑ " term : term
  syntax "∏ " term : term
  syntax "∑ " term " in " term : term
  syntax "∏ " term " in " term : term
  syntax "∑ " ident " in " term ", " term : term
  syntax "∏ " ident " in " term ", " term : term

   macro_rules
  -- ∑ s = s.sum
  | `(∑ $s) => `( ($s).sum )
  -- ∏ s := s.prod
  | `(∏ $s) => `( ($s).prod )
  -- ∑ f in s = s.map_sum f
  | `(∑ $f in $s) => `( ($s).map_sum $f )
  -- ∏ f in s := s.map_prod f
  | `(∏ $f in $s) => `( ($s).map_prod $f )
  -- ∑ x in s, f := s.map_sum fun x => f
  | `(∑ $x:ident in $s, $f) => `( ($s).map_sum fun $x => $f )
  -- ∏ x in s, f := s.map_prod fun x => f
  | `(∏ $x:ident in $s, $f) => `( ($s).map_prod fun $x => $f )

  @[simp] theorem zero_eq [z : Zero α] : z.zero    = 0     := rfl
  @[simp] theorem one_eq  [o : One  α] : o.one     = 1     := rfl
  @[simp] theorem neg_eq  [n : Neg  α] : n.neg x   = - x   := rfl
  @[simp] theorem hadd_eq [a : HAdd α β γ] : a.hAdd x y = x + y := rfl
  @[simp] theorem hsub_eq [s : HSub α β γ] : s.hSub x y = x - y := rfl
  @[simp] theorem hmul_eq [m : HMul α β γ] : m.hMul x y = x * y := rfl
  @[simp] theorem add_eq  [a : Add α] : a.add x y = x + y := rfl
  @[simp] theorem sub_eq  [s : Sub α] : s.sub x y = x - y := rfl
  @[simp] theorem mul_eq  [m : Mul α] : m.mul x y = x * y := rfl

end M4R