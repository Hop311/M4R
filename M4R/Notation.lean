namespace M4R

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

  class Subset (α : Type u) where
    subset : α → α → Prop
  infix:50 " ⊆ " => Subset.subset

  class ProperSubset (α : Type u) where
    propersubset : α → α → Prop
  infix:50 " ⊊ " => ProperSubset.propersubset

  class NotSubset (α : Type u) where
     notsubset : α → α → Prop
  infix:50 " ⊈ " => NotSubset.notsubset

  class Union (α : Type u) where
    union : α → α → α
  infixl:65 " ∪ " => Union.union

  class Intersection (α : Type u) where
    intersection : α → α → α
  infixl:70 " ∩ " => Intersection.intersection

  class SetMinus (α : Type u) where
    setminus : α → α → α
  infix:70 " ∖ " => SetMinus.setminus

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

  class Inv (α : Type u) where
    inv : α → α
  postfix:max " ⁻¹ " => Inv.inv

  class Zero (α : Type _) where
    zero : α
  class One  (α : Type _) where
    one  : α
  instance Nat0 [Zero α] : OfNat α (nat_lit 0) where
    ofNat := Zero.zero
  instance Nat1 [One  α] : OfNat α (nat_lit 1) where
    ofNat := One.one
  instance InhabitedZero [Zero α] : Inhabited α where default := 0
  instance InhabitedOne  [One α]  : Inhabited α where default := 1
  instance NatZero : Zero Nat where zero := 0
  instance NatOne  : One  Nat where one  := 1
  instance IntZero : Zero Int where zero := 0
  instance IntOne  : One  Int where one  := 1
    
  class Divides (α : Type u) where
    divides : α → α → Prop
  infix:55 " ÷ " => Divides.divides

  class RingEq (α : Type u) where
    ringeq : α → α → Prop
  infix:55 " ≗ " => RingEq.ringeq -- \=o -> ≗

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
  @[simp] theorem hadd_eq  [a : HAdd α β γ] : a.hAdd x y = x + y := rfl
  @[simp] theorem hsub_eq  [s : HSub α β γ] : s.hSub x y = x - y := rfl
  @[simp] theorem hmul_eq  [m : HMul α β γ] : m.hMul x y = x * y := rfl
  @[simp] theorem add_eq  [a : Add α] : a.add x y = x + y := rfl
  @[simp] theorem sub_eq  [s : Sub α] : s.sub x y = x - y := rfl
  @[simp] theorem mul_eq  [m : Mul α] : m.mul x y = x * y := rfl
  
end M4R