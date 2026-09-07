import GMZP0.FiniteFourierEnergy
import GMZP0.DifferenceDensity

/-! Difference densities have a nonnegative Fourier expansion with the exact L2 coefficient mass. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def fourierEnergyWeight {G : Type*} [AddCommGroup G] [Fintype G]
    (ν : G → ℝ) (ψ : AddChar G ℂ) : ℝ := ‖finiteFourier (fun y => (ν y : ℂ)) ψ‖ ^ 2

theorem realDifferenceDensity_nonneg {G : Type*} [AddCommGroup G] [Fintype G]
    (ν : G → ℝ) (hν : ∀ y, 0 ≤ ν y) (d : G) : 0 ≤ realDifferenceDensity ν d :=
  realUniformMean_nonneg _ (fun y => mul_nonneg (hν (y + d)) (hν y))

theorem finiteCorrelation_ofReal {G : Type*} [AddCommGroup G] [Fintype G]
    (ν : G → ℝ) (d : G) : finiteCorrelation (fun y => (ν y : ℂ)) d = (realDifferenceDensity ν d : ℂ) := by
  simp only [finiteCorrelation, Complex.conj_ofReal, ← Complex.ofReal_mul,
    complexUniformMean_ofReal, realDifferenceDensity]

theorem fourierEnergyWeight_nonneg {G : Type*} [AddCommGroup G] [Fintype G]
    (ν : G → ℝ) (ψ : AddChar G ℂ) : 0 ≤ fourierEnergyWeight ν ψ := sq_nonneg _

theorem fourierEnergyWeight_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (ν : G → ℝ) : (∑ ψ : AddChar G ℂ, fourierEnergyWeight ν ψ) = realUniformMean (fun y => ν y ^ 2) := by
  simpa only [fourierEnergyWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    using finiteFourier_parseval (fun y => (ν y : ℂ))

theorem realDifferenceDensity_fourier {G : Type*} [AddCommGroup G] [Fintype G]
    (ν : G → ℝ) (d : G) :
    (realDifferenceDensity ν d : ℂ) = ∑ ψ : AddChar G ℂ, (fourierEnergyWeight ν ψ : ℂ) * ψ d := by
  rw [← finiteCorrelation_ofReal]
  calc
    _ = ∑ ψ : AddChar G ℂ, finiteFourier (finiteCorrelation (fun y => (ν y : ℂ))) ψ * ψ d :=
      (finiteFourier_inversion _ d).symm
    _ = _ := by simp only [finiteFourier_correlation, fourierEnergyWeight]

end GMZP0
