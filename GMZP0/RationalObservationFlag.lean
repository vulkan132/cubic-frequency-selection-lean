import GMZP0.PolynomialPresentationBounds
import GMZP0.RationalCoordinateLieGroup

/-! Construct the common finite flag and nilpotent Lie structure from
the original fixed rational base law and observation basis. Degree bounds
for all original translations and observations are derived internally. -/
noncomputable section
open Module MvPolynomial
open scoped Manifold ContDiff
namespace GMZP0
variable {G iota : Type*} [Group G] [Fintype iota] {m : ℕ}

/-- The fixed original rational presentation gives one finite flag
before all translating points and all unrestricted original observations. -/
theorem original_rational_observation_flag
    (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (P : iota → MvPolynomial (Fin m) ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ K : ℕ, 0 < K ∧ ∃ flag : ℕ → Submodule ℝ V.space,
      flag 0 = ⊥ ∧ (∀ F : V.space, F ∈ flag K) ∧
      (∀ n g (F : V.space), F ∈ flag (n + 1) → observationTranslate V g F - F ∈ flag n) := by
  obtain ⟨D, hD⟩ := original_triangular_correction_uniform_degree coord p hjoint q htri
  obtain ⟨R, hR⟩ := observation_rational_basis_uniform_degree V b coord P hP
  let w : Fin m → ℕ := triangularCoordinateWeight D
  let K := R * (D + 1) ^ m + 1
  refine ⟨K, by dsimp [K]; omega, coordinateObservationFlag V coord w,
    coordinateObservationFlag_zero V coord w, ?_, ?_⟩
  · exact coordinateObservationFlag_top V coord w K
      (triangular_observation_uniform_bound V coord D R hR)
  · apply coordinateObservationFlag_lowers V coord w q htri
    intro g i
    exact triangular_correction_mem D i (q g i) (hD g i) (hlow g i)

/-- The original fixed data construct a nilpotent smooth observation
group and a coefficient-independent finite nilpotency bound. The base
nilpotence is the manuscript's original structural hypothesis. -/
theorem original_rational_observation_nilpotent_lie
    [TopologicalSpace G] [Group.IsNilpotent G]
    (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ₜ (Fin m → ℝ)) (b : Basis iota ℝ V.space)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (P : iota → MvPolynomial (Fin m) ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ K : ℕ, 0 < K ∧ Group.IsNilpotent (ObservationGroup V) ∧
      Group.nilpotencyClass (ObservationGroup V) ≤ Group.nilpotencyClass G + K ∧
      ContractibleSpace (ObservationGroup V) ∧
      (letI := (observationFullCoordinates V coord b).isOpenEmbedding.singletonChartedSpace
       LieGroup 𝓘(ℝ, (Fin m ⊕ iota) → ℝ) ∞ (ObservationGroup V)) := by
  obtain ⟨K, hK, flag, hzero, htop, hdrop⟩ :=
    original_rational_observation_flag V b coord.toEquiv p hjoint q htri hlow P hP
  have hn := observation_nilpotent_of_flag V flag K hzero htop hdrop
  let := hn
  refine ⟨K, hK, hn, ?_, coordinate_group_contractible (observationFullCoordinates V coord b),
    original_observation_coordinate_lie_group V Gamma coord b hint hcover p hjoint q htri hlow P hP⟩
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  exact observation_lowerCentral_vanishes_of_flag V flag K (Group.nilpotencyClass G)
    hzero htop hdrop (Subgroup.lowerCentralSeries_nilpotencyClass (G := G))

end GMZP0
