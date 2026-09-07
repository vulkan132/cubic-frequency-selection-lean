import GMZP0.LocalCubeDifference
import GMZP0.DensityNormalization

/-! Global Gowers moments in the same convention as the checked local moments. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def globalCubeMoment {G : Type*} [AddCommGroup G] [Fintype G] (n : ℕ) (H : G → ℂ) : ℝ :=
  localCubeMoment n H (fun y : G => y)

def globalCubeNorm {G : Type*} [AddCommGroup G] [Fintype G] (n : ℕ) (H : G → ℂ) : ℝ :=
  localCubeNorm n H (fun y : G => y)

theorem globalCubeMoment_additive {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (H : G → ℂ) :
    (globalCubeMoment n H : ℂ) = complexUniformMean (fun Y : G =>
      complexUniformMean (fun v : Fin (n + 1) → G => additiveCubeProduct (n + 1) H Y v)) := by
  classical
  simpa only [globalCubeMoment, parameterDensity_identity, realDifferenceDensity,
    one_mul, realUniformMean_const, Finset.prod_const_one, Complex.ofReal_one]
    using localCubeMoment_difference n H (fun y : G => y)

end GMZP0
