import GMZP0.PositiveFourierMixture
import GMZP0.DifferenceFourier
import GMZP0.AdditiveCube

/-! Exact Fourier expansion of the difference-weighted global cube kernel. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def globalTwistedCubeMean {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (H : G → ℂ) (ψ : Fin d → AddChar G ℂ) : ℂ :=
  complexUniformMean (fun Y : G => complexUniformMean (fun v : Fin d → G =>
    (∏ i, ψ i (v i)) * additiveCubeProduct d H Y v))

def differenceWeightedCubeMean {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (H : G → ℂ) (ν : G → ℝ) : ℂ :=
  complexUniformMean (fun Y : G => complexUniformMean (fun v : Fin d → G =>
    ((∏ i, realDifferenceDensity ν (v i) : ℝ) : ℂ) * additiveCubeProduct d H Y v))

theorem differenceDensity_product_fourier {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (ν : G → ℝ) (v : Fin d → G) :
    ((∏ i, realDifferenceDensity ν (v i) : ℝ) : ℂ) =
      ∑ ψ : Fin d → AddChar G ℂ,
        ((∏ i, fourierEnergyWeight ν (ψ i) : ℝ) : ℂ) * ∏ i, ψ i (v i) := by
  simp only [Complex.ofReal_prod, realDifferenceDensity_fourier]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem differenceWeightedCubeMean_fourier {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (H : G → ℂ) (ν : G → ℝ) :
    differenceWeightedCubeMean d H ν = ∑ ψ : Fin d → AddChar G ℂ,
      ((∏ i, fourierEnergyWeight ν (ψ i) : ℝ) : ℂ) * globalTwistedCubeMean d H ψ := by
  simp only [differenceWeightedCubeMean, differenceDensity_product_fourier,
    Finset.sum_mul, mul_assoc, complexUniformMean_sum, complexUniformMean_const_mul,
    globalTwistedCubeMean]

theorem differenceWeightedCubeMean_bound {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (H : G → ℂ) (ν : G → ℝ) (C L : ℝ) (hL : 0 ≤ L)
    (hν : realUniformMean (fun y => ν y ^ 2) ≤ C)
    (hTwist : ∀ ψ : Fin d → AddChar G ℂ, ‖globalTwistedCubeMean d H ψ‖ ≤ L) :
    ‖differenceWeightedCubeMean d H ν‖ ≤ C ^ d * L := by
  rw [differenceWeightedCubeMean_fourier]
  apply positive_product_mixture_bound d (fourierEnergyWeight ν) (fourierEnergyWeight_nonneg ν) C L
  · rwa [fourierEnergyWeight_sum]
  · exact hL
  · exact hTwist

end GMZP0
