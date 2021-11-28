namespace M4R

  class Mem (α : outParam (Type u)) (γ : Type v) where
    mem : α → γ → Prop
  infixl:55 " ∈ " => Mem.mem
  notation:55 x:55 " ∉ " s:56 => ¬ (x ∈ s)

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
  class One (α : Type _) where
    one : α
  instance [Zero α] : OfNat α (nat_lit 0) where
    ofNat := Zero.zero
  instance [One α] : OfNat α (nat_lit 1) where
    ofNat := One.one

end M4R