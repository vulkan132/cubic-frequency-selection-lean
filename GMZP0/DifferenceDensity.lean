import GMZP0.ParameterDensity

/-! Exact difference density of two independently sampled parameters, with repetitions. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def realDifferenceDensity {G : Type*} [AddCommGroup G] [Fintype G] (ν : G → ℝ) (d : G) : ℝ :=
  realUniformMean (fun y => ν (y + d) * ν y)

theorem realDifferenceDensity_weighted {G : Type*} [AddCommGroup G] [Fintype G]
    (ν : G → ℝ) (T : G → ℂ) :
    complexUniformMean (fun d => (realDifferenceDensity ν d : ℂ) * T d) =
      complexUniformMean (fun y => (ν y : ℂ) *
        complexUniformMean (fun x => (ν x : ℂ) * T (x - y))) := by
  have hw (d : G) : (realDifferenceDensity ν d : ℂ) =
      complexUniformMean (fun y => (ν (y + d) : ℂ) * (ν y : ℂ)) := by
    simp only [← Complex.ofReal_mul, complexUniformMean_ofReal, realDifferenceDensity]
  simp only [hw, ← complexUniformMean_mul_const]
  rw [complexUniformMean_comm]
  congr 1
  funext y
  calc
    _ = (ν y : ℂ) * complexUniformMean (fun d => (ν (y + d) : ℂ) * T d) := by
      rw [← complexUniformMean_const_mul]
      congr 1
      funext d
      ring
    _ = _ := by
      congr 1
      have he := complexUniformMean_equiv (Equiv.addLeft y) (fun x => (ν x : ℂ) * T (x - y))
      simpa only [Equiv.coe_addLeft, add_sub_cancel_left] using he

theorem parameterDifference_pushforward {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [DecidableEq G] (r : A → G) (T : G → ℂ) :
    complexUniformMean (fun d => (realDifferenceDensity (parameterDensity r) d : ℂ) * T d) =
      complexUniformMean (fun a : A => complexUniformMean (fun b : A => T (r b - r a))) := by
  rw [realDifferenceDensity_weighted]
  simp only [parameterDensity_pushforward]

end GMZP0
