import M4R.Algebra.Ring.MaxPrimeIdeal

namespace M4R

  class LocalRing (α : Type _) extends NonTrivialRing α where
    loc : ∃ m : Ideal α, Ring.MaxSpec α = Set.singleton m
  
  class SemilocalRing (α : Type _) extends NonTrivialRing α where
    semi_loc : ∃ fm : Finset (Ideal α), Ring.MaxSpec α = fm.toSet

  namespace LocalRing
    open Classical QuotientRing Semiring

    variable {α : Type _} [LocalRing α]

    noncomputable def m : Ideal α := choose LocalRing.loc
    theorem m_maxspec : Ring.MaxSpec α = Set.singleton m := choose_spec LocalRing.loc
    theorem m_max : (m : Ideal α).is_maximal := (m_maxspec ▸ rfl : m ∈ Ring.MaxSpec α)
    theorem m_proper : (m : Ideal α).proper_ideal := m_max.left

    theorem units {a : α} : isUnit a ↔ a ∉ m :=
      ⟨fun h₁ h₂ => absurd (Ideal.is_unit_ideal'.mpr ⟨a, h₁, h₂⟩) m_proper,
       not_imp_symm fun h => by
        -- requires matsumura t1_1?
        sorry⟩

    instance to_SemilocalRing (α : Type _) [R : LocalRing α] : SemilocalRing α where
      toNonTrivialRing := R.toNonTrivialRing
      semi_loc := ⟨Finset.singleton m, Set.ext.mp fun x => by
        rw [m_maxspec, ←Finset.ext_Set, Finset.mem_singleton]; exact Iff.rfl⟩

    def residue_field (α : Type u) [LocalRing α] := QClass (m : Ideal α)

  end LocalRing

  namespace SemilocalRing

  end SemilocalRing
end M4R
