import GMZP0.ObservationIntegerLattice
import Mathlib.LinearAlgebra.FreeModule.PID

/-! Actual integer evaluation embeds V_Z in a finite free integer module.
The resulting integer basis is qualitative; bounded adapted bases require
further rational-height and quotient arguments. -/
noncomputable section
open Module
namespace GMZP0
variable {G : Type*} [Group G]

/-- Taking the floor of an actual integer value recovers that value exactly. -/
theorem observation_integer_floor_cast (V : ObservationModule G) (Gamma : Subgroup G)
    (P : observationIntegerLattice V Gamma) (gamma : Gamma) :
    ((⌊(P : V.space) gamma⌋ : ℤ) : ℝ) = (P : V.space) gamma := by
  obtain ⟨n, hn⟩ := P.property gamma
  simp [hn]

/-- The exact integer evaluations, including their original actual subgroup points. -/
def observationIntegerEvaluation (V : ObservationModule G) (Gamma : Subgroup G)
    {n : ℕ} (gamma : Fin n → Gamma) : observationIntegerLattice V Gamma →ₗ[ℤ] (Fin n → ℤ) :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun P i => ⌊(P : V.space) (gamma i)⌋
    map_zero' := by funext i; simp
    map_add' := by
      intro P Q
      funext i
      apply Int.cast_injective (α := ℝ)
      simp only [Pi.add_apply]
      rw [Int.cast_add, observation_integer_floor_cast, observation_integer_floor_cast,
        observation_integer_floor_cast]
      rfl }

/-- Casting the integer evaluation vector recovers every actual real function value exactly. -/
theorem observationIntegerEvaluation_cast (V : ObservationModule G) (Gamma : Subgroup G)
    {n : ℕ} (gamma : Fin n → Gamma) (P : observationIntegerLattice V Gamma) (i : Fin n) :
    (observationIntegerEvaluation V Gamma gamma P i : ℝ) = (P : V.space) (gamma i) :=
  observation_integer_floor_cast V Gamma P (gamma i)

/-- Determining actual subgroup evaluations give an injective integer-linear map of the actual lattice. -/
theorem observationIntegerEvaluation_injective (V : ObservationModule G) (Gamma : Subgroup G)
    {n : ℕ} (gamma : Fin n → Gamma)
    (hsep : ∀ P : V.space, (∀ i, P (gamma i) = 0) → P = 0) :
    Function.Injective (observationIntegerEvaluation V Gamma gamma) := by
  intro P Q h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hsep
  intro i
  have hi := congrArg (fun f : Fin n → ℤ => (f i : ℝ)) h
  rw [observationIntegerEvaluation_cast, observationIntegerEvaluation_cast] at hi
  change (P : V.space) (gamma i) - (Q : V.space) (gamma i) = 0
  exact sub_eq_zero.mpr hi

/-- A finite determining family constructs an integer basis of the actual V_Z via its embedded range. -/
theorem observation_integer_basis_of_evaluations (V : ObservationModule G) (Gamma : Subgroup G)
    {n : ℕ} (gamma : Fin n → Gamma)
    (hsep : ∀ P : V.space, (∀ i, P (gamma i) = 0) → P = 0) :
    ∃ d : ℕ, Nonempty (Basis (Fin d) ℤ (observationIntegerLattice V Gamma)) := by
  let f := observationIntegerEvaluation V Gamma gamma
  have hf := observationIntegerEvaluation_injective V Gamma gamma hsep
  obtain ⟨d, b⟩ := (LinearMap.range f).basisOfPid (Pi.basisFun ℤ (Fin n))
  exact ⟨d, ⟨b.map (LinearEquiv.ofInjective f hf).symm⟩⟩

/-- A finite integer basis exists from finite dimension and separating original subgroup evaluations. -/
theorem observation_integer_basis (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (Gamma : Subgroup G)
    (hsep : ∀ P : V.space, (∀ gamma : Gamma, P gamma = 0) → P = 0) :
    ∃ d : ℕ, Nonempty (Basis (Fin d) ℤ (observationIntegerLattice V Gamma)) := by
  obtain ⟨n, _, gamma, hgamma⟩ := observation_finite_determining_points V Gamma hsep
  exact observation_integer_basis_of_evaluations V Gamma gamma hgamma

/-- A literal rational polynomial basis and integer-coordinate coverage supply a finite basis of V_Z. -/
theorem observation_integer_basis_of_presentation (V : ObservationModule G) (Gamma : Subgroup G)
    {sigma iota : Type*} [Fintype iota] (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) :
    ∃ d : ℕ, Nonempty (Basis (Fin d) ℤ (observationIntegerLattice V Gamma)) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  apply observation_integer_basis V Gamma
  exact observation_integer_points_separate V Gamma coord hcover
    (observation_representatives_of_rational_basis V b coord P hb)

end GMZP0
