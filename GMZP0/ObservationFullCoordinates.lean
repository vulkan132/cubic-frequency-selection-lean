import GMZP0.ObservationGroupCompact
import GMZP0.PolynomialCoordinateMetric

/-! Full coordinates of the actual observation group. The base is the
original coordinate map and the fiber consists of actual basis coefficients. -/
noncomputable section
open Module
namespace GMZP0
variable {G sigma iota : Type*} [Group G] [TopologicalSpace G]
  [Fintype iota]

/-- The original product topology identified with all actual finite
base and fiber coordinates, with no quotient or rounding. -/
def observationFullCoordinates (V : ObservationModule G)
    (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space) :
    ObservationGroup V ≃ₜ ((sigma ⊕ iota) → ℝ) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  exact (observationPairHomeomorph V).trans
    ((coord.prodCongr b.equivFun.toContinuousLinearEquiv.toHomeomorph).trans
      (Homeomorph.sumPiEquivProdPi sigma iota (fun _ => ℝ)).symm)

/-- Base coordinate components read precisely the original base point. -/
theorem observation_full_coordinates_base (V : ObservationModule G)
    (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space) (a : ObservationGroup V) (s : sigma) :
    observationFullCoordinates V coord b a (Sum.inl s) = coord a.base s := rfl

/-- Fiber coordinate components read precisely the original observation coefficients. -/
theorem observation_full_coordinates_fiber (V : ObservationModule G)
    (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space) (a : ObservationGroup V) (i : iota) :
    observationFullCoordinates V coord b a (Sum.inr i) = b.equivFun a.obs i := rfl

/-- Literal polynomial basis functions make every actual observation
continuous, including arbitrary unrestricted real coefficients. -/
theorem observation_basis_polynomials_continuous (V : ObservationModule G)
    (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (P : iota → MvPolynomial sigma ℝ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∀ F : V.space, Continuous (fun g : G => F g) := by
  intro F
  have he : (fun g : G => F g) =
      fun g => ∑ j, b.equivFun F j * MvPolynomial.aeval (coord g) (P j) := by
    funext g
    rw [observation_evaluation_basis V b F g]
    simp only [hP]
  rw [he]
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((P j).continuous_eval.comp coord.continuous)

end GMZP0
