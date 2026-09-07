import GMZP0.FourierCubeExpansion
import GMZP0.LocalCubeDifference
import GMZP0.ParameterEnergy

/-! Exact local Fourier expansion and its explicit remaining mixed-cube hypothesis. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem localCubeMoment_eq_differenceWeighted {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [DecidableEq G] (n : ℕ) (H : G → ℂ) (r : A → G) :
    (localCubeMoment n H r : ℂ) = differenceWeightedCubeMean (n + 1) H (parameterDensity r) :=
  localCubeMoment_difference n H r

theorem localCubeMoment_fourier {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [DecidableEq G] (n : ℕ) (H : G → ℂ) (r : A → G) :
    (localCubeMoment n H r : ℂ) = ∑ ψ : Fin (n + 1) → AddChar G ℂ,
      ((∏ i, fourierEnergyWeight (parameterDensity r) (ψ i) : ℝ) : ℂ) *
        globalTwistedCubeMean (n + 1) H ψ := by
  rw [localCubeMoment_eq_differenceWeighted, differenceWeightedCubeMean_fourier]

theorem localCubeMoment_bound_of_twisted {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [DecidableEq G] (n : ℕ) (H : G → ℂ) (r : A → G) (C L : ℝ) (hL : 0 ≤ L)
    (hν : realUniformMean (fun y => parameterDensity r y ^ 2) ≤ C)
    (hTwist : ∀ ψ : Fin (n + 1) → AddChar G ℂ, ‖globalTwistedCubeMean (n + 1) H ψ‖ ≤ L) :
    localCubeMoment n H r ≤ C ^ (n + 1) * L := by
  have hh := differenceWeightedCubeMean_bound (n + 1) H (parameterDensity r) C L hL hν hTwist
  rw [← localCubeMoment_eq_differenceWeighted, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (localCubeMoment_nonneg n H r)] at hh
  exact hh

end GMZP0
