import M4R.Algebra.Group.Monoid

namespace M4R
 
  instance MapZero (α : Type _) (β : Type _) [Zero β] : Zero (α → β) where zero := fun _ => 0

  instance MapAdd (α : Type _) (β : Type _) [Monoid β] : Add (α → β) where add := fun x y a => x a + y a

  instance MapMonoid (α : Type _) (β : Type _) [Monoid β] : Monoid (α → β) where
    add_zero := fun x => funext fun _ => Monoid.add_zero _
    zero_add := fun x => funext fun a => by conv => rhs rw [←Monoid.zero_add (x a)]
    add_assoc := fun x y z => funext fun a => Monoid.add_assoc _ _ _
  
  instance MapCommMonoid (α : Type _) (β : Type _) [CommMonoid β] : CommMonoid (α → β) where
    add_comm := fun x y => funext fun a => CommMonoid.add_comm _ _

  instance MapNeg (α : Type _) (β : Type _) [Group β] : Neg (α → β) where neg := fun x a => - x a

  instance MapGroup (α : Type _) (β : Type _) [Group β] : Group (α → β) where
    add_neg := fun _ => funext fun _ => Group.add_neg _
  
  instance MapAbelianGroup (α : Type _) (β : Type _) [AbelianGroup β] : AbelianGroup (α → β) where
    add_comm := (MapCommMonoid α β).add_comm

  structure Finsupp (α : Type _) (β : Type _) [Zero β] :=
  (support            : Finset α)
  (to_fun             : α → β)
  (mem_support_to_fun : ∀a, a ∈ support ↔ to_fun a ≠ 0)

  infixr:25 " →₀ " => Finsupp
  
  namespace Finsupp

    instance FinsuppFun [Zero β] : CoeFun (α →₀ β) (fun (x : α →₀ β) => α → β) where coe := to_fun
  
    protected theorem ext [Zero β] (x y : α →₀ β) : x = y ↔ x.to_fun = y.to_fun :=
      ⟨fun h => by rw [h],
        match x, y with | ⟨xs, xf, xc⟩, ⟨ys, yf, yc⟩ => fun hf => by
          simp at hf
          have hs : xs = ys :=
            Finset.ext fun _ => by rw [xc, yc, hf]; exact Iff.refl _
          rw [Finsupp.mk.injEq];
          exact ⟨hs, hf⟩⟩

    protected def zero (α : Type _) (β : Type _) [Zero β] : α →₀ β where
      support            := ∅
      to_fun             := fun _ => 0
      mem_support_to_fun := fun a => ⟨fun h _ => h, fun h => h rfl⟩
    
    instance FinsuppZero [Zero β] : Zero (α →₀ β) where zero := Finsupp.zero α β

    theorem empty_support [Zero β] {f : α →₀ β} (h : f.support = ∅) : f = 0 := by
      rw [Finsupp.ext]; apply funext; intro x;
      have : x ∉ f.support := fun h' => by rw [h] at h'; contradiction
      rw [of_not_not (mt (f.mem_support_to_fun x).mpr this)]; rfl

    theorem zero_fun [Zero β] {f : α →₀ β} (h : ∀ a, f a = 0) : f = 0 := by
      rw [Finsupp.ext]; apply funext; intro x; rw [h x]; rfl

    def support_set_of_fun [Zero β] (f : α → β) : Set α := {a | f a ≠ 0}

    theorem support_of_fun_finite [Zero β] (x y : α →₀ β) (f : α → β) (h : ∀ a, x a = 0 → y a = 0 → f a = 0) :
      finite (support_set_of_fun f) :=
        finite.subset (finite.union x.support.to_finite y.support.to_finite) fun a af =>
          Classical.byContradiction fun h' =>
            have h' := not_or_iff_and_not.mp h'
            af (h a
              (of_not_not (mt (x.mem_support_to_fun a).mpr h'.left))
              (of_not_not (mt (y.mem_support_to_fun a).mpr h'.right)))

    noncomputable def support_of_fun [Zero β] (x y : α →₀ β) (f : α → β) (h : ∀ a, x a = 0 → y a = 0 → f a = 0) : Finset α :=
      (support_of_fun_finite x y f h).to_finset

    theorem support_of_fun_complete [Zero β] (x y : α →₀ β) (f : α → β) (h : ∀ a, x a = 0 → y a = 0 → f a = 0) :
      ∀ a, a ∈ support_of_fun x y f h ↔ f a ≠ 0 := fun _ => by
        simp [support_of_fun]; exact Iff.refl _

    noncomputable def finsupp_fun [Zero β] (f : (α →₀ β) → (α →₀ β) → α → β)  
      (h : ∀ (x y : α →₀ β) (a : α), x a = 0 → y a = 0 → f x y a = 0) (x y : α →₀ β) : α →₀ β where
      to_fun := f x y
      support := support_of_fun x y (f x y) (h x y)
      mem_support_to_fun := support_of_fun_complete x y (f x y) (h x y)

    protected noncomputable def add [Monoid β] : (α →₀ β) → (α →₀ β) → α →₀ β :=
      finsupp_fun (·.to_fun + ·.to_fun) (fun x y a hx hy => by
        simp only [HAdd.hAdd, Add.add, add_eq]; rw [hx, hy, Monoid.add_zero])

    noncomputable instance toMonoid [Monoid β] : Monoid (α →₀ β) where
      add := Finsupp.add
      add_zero := fun a => (Finsupp.ext _ _).mpr (funext fun _ => Monoid.add_zero _)
      zero_add := fun a => (Finsupp.ext _ _).mpr (funext fun _ => Monoid.zero_add _)
      add_assoc := fun a b c => (Finsupp.ext _ _).mpr (funext fun _ => Monoid.add_assoc _ _ _)

    noncomputable instance toCommMonoid [CommMonoid β] : CommMonoid (α →₀ β) where
      add_comm := fun a b => (Finsupp.ext _ _).mpr (funext fun _ => CommMonoid.add_comm _ _)

  end Finsupp
end M4R
