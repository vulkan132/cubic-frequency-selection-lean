import GMZP0.AdditiveCube
import GMZP0.DifferenceDensity
import GMZP0.ProductPushforward

/-! The local moment is exactly a global cube average weighted by the actual parameter difference law. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem parameterDifference_product_pushforward {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [DecidableEq G] (r : A → G) (d : ℕ) (T : (Fin d → G) → ℂ) :
    complexUniformMean (fun v : Fin d → G =>
      ((∏ i, realDifferenceDensity (parameterDensity r) (v i) : ℝ) : ℂ) * T v) =
      complexUniformMean (fun u : Fin d → A × A => T (fun i => r (u i).2 - r (u i).1)) := by
  simp only [Complex.ofReal_prod]
  apply uniform_product_pushforward (fun z : A × A => r z.2 - r z.1)
    (fun v => (realDifferenceDensity (parameterDensity r) v : ℂ))
  intro U
  rw [parameterDifference_pushforward]
  exact (complexUniformMean_prod (fun a b => U (r b - r a))).symm

theorem localCubeMoment_difference {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [DecidableEq G] (n : ℕ) (H : G → ℂ) (r : A → G) :
    (localCubeMoment n H r : ℂ) = complexUniformMean (fun Y : G =>
      complexUniformMean (fun v : Fin (n + 1) → G =>
        ((∏ i, realDifferenceDensity (parameterDensity r) (v i) : ℝ) : ℂ) *
          additiveCubeProduct (n + 1) H Y v)) := by
  rw [← localCubeMoment_complex]
  simp only [cubeMean]
  rw [complexUniformMean_comm]
  simp only [local_cube_mean_reroot]
  rw [complexUniformMean_comm]
  congr 1
  funext Y
  exact (parameterDifference_product_pushforward r (n + 1) (additiveCubeProduct (n + 1) H Y)).symm

end GMZP0
