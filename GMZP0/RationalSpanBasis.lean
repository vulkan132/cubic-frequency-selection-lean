import GMZP0.ObservationRationalSpan
import GMZP0.RationalHeightFinite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Select an actual basis from a finite original rational spanning
family. Every chosen basis vector keeps its original rational coordinates. -/
noncomputable section
open Module
namespace GMZP0
variable {E iota : Type*} [AddCommGroup E] [Module ℝ E] [Fintype iota]

/-- A rational finite span has a basis selected from the actual original
generators, with no coordinate change in the ambient original space. -/
theorem rational_span_selected_basis (b : Basis iota ℝ E) (N : Submodule ℝ E)
    (S : Finset (iota → ℚ))
    (hN : N = Submodule.span ℝ (rationalBasisVector b '' (S : Set (iota → ℚ)))) :
    ∃ J : Set E, J.Finite ∧ ∃ bN : Basis J ℝ N,
      ∀ j : J, ∃ a ∈ S, (bN j : E) = rationalBasisVector b a := by
  classical
  obtain ⟨J, hJ, hspan, hli⟩ := exists_linearIndependent ℝ
    (rationalBasisVector b '' (S : Set (iota → ℚ)))
  have hfin : J.Finite := (S.finite_toSet.image (rationalBasisVector b)).subset hJ
  have hspan' : Submodule.span ℝ (Set.range ((↑) : J → E)) = N := by
    rw [Subtype.range_coe, hspan, ← hN]
  let e := LinearEquiv.ofEq (Submodule.span ℝ (Set.range ((↑) : J → E))) N hspan'
  refine ⟨J, hfin, (Basis.span hli).map e, ?_⟩
  intro j
  obtain ⟨a, ha, hea⟩ := hJ j.property
  refine ⟨a, ha, ?_⟩
  change (e ((Basis.span hli) j) : E) = _
  change ((Basis.span hli) j : E) = _
  simpa only [Basis.coe_span_apply] using hea.symm

/-- Selecting from the original generators preserves their common
coordinate-height bound on every basis vector. -/
theorem rational_span_bounded_basis (b : Basis iota ℝ E) (N : Submodule ℝ E)
    (S : Finset (iota → ℚ))
    (hN : N = Submodule.span ℝ (rationalBasisVector b '' (S : Set (iota → ℚ))))
    (H : ℕ) (hH : ∀ a ∈ S, ∀ i, rationalHeight (a i) ≤ H) :
    ∃ J : Set E, J.Finite ∧ ∃ bN : Basis J ℝ N,
      ∀ j : J, ∃ a : iota → ℚ, ∀ i,
        b.repr (bN j : E) i = (a i : ℝ) ∧ rationalHeight (a i) ≤ H := by
  obtain ⟨J, hJ, bN, hbN⟩ := rational_span_selected_basis b N S hN
  refine ⟨J, hJ, bN, ?_⟩
  intro j
  obtain ⟨a, ha, hvec⟩ := hbN j
  refine ⟨a, ?_⟩
  intro i
  rw [hvec, rationalBasisVector_repr]
  exact ⟨rfl, hH a ha i⟩

end GMZP0
