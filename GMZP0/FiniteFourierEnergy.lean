import GMZP0.FiniteFourier

/-! Parseval and the nonnegative Fourier coefficients of an actual difference correlation. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem finiteFourier_inner {G : Type*} [AddCommGroup G] [Fintype G] (F H : G → ℂ) :
    (∑ ψ : AddChar G ℂ, finiteFourier F ψ * conj (finiteFourier H ψ)) =
      complexUniformMean (fun x => F x * conj (H x)) := by
  classical
  calc
    _ = ∑ ψ : AddChar G ℂ, complexUniformMean
        (fun x => (F x * conj (ψ x)) * conj (finiteFourier H ψ)) := by
      apply Finset.sum_congr rfl
      intro ψ _
      exact (complexUniformMean_mul_const _ _).symm
    _ = complexUniformMean (fun x => F x * conj (∑ ψ : AddChar G ℂ, finiteFourier H ψ * ψ x)) := by
      rw [← complexUniformMean_sum]
      congr 1
      funext x
      simp only [map_sum, map_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ψ _
      ring
    _ = _ := by simp only [finiteFourier_inversion]

theorem finiteFourier_parseval {G : Type*} [AddCommGroup G] [Fintype G] (F : G → ℂ) :
    (∑ ψ : AddChar G ℂ, ‖finiteFourier F ψ‖ ^ 2) = realUniformMean (fun x => ‖F x‖ ^ 2) := by
  have h := finiteFourier_inner F F
  simp only [Complex.mul_conj, ← Complex.sq_norm] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.re_sum, complexUniformMean_re, Complex.ofReal_re] using hr

theorem finite_character_mul_conj {G : Type*} [AddCommGroup G] [Fintype G]
    (ψ : AddChar G ℂ) (x : G) : ψ x * conj (ψ x) = 1 := by
  simpa only [← Complex.sq_norm, ψ.norm_apply, one_pow, Complex.ofReal_one]
    using Complex.mul_conj (ψ x)

def finiteCorrelation {G : Type*} [AddCommGroup G] [Fintype G] (F : G → ℂ) (d : G) : ℂ :=
  complexUniformMean (fun y => F (y + d) * conj (F y))

theorem correlation_character_factor {G : Type*} [AddCommGroup G] [Fintype G]
    (F : G → ℂ) (ψ : AddChar G ℂ) (y d : G) :
    F (y + d) * conj (F y) * conj (ψ d) =
      (F (y + d) * conj (ψ (y + d))) * conj (F y * conj (ψ y)) := by
  symm
  simp only [AddChar.map_add_eq_mul, map_mul, starRingEnd_self_apply]
  calc
    _ = (F (y + d) * conj (F y) * conj (ψ d)) * (ψ y * conj (ψ y)) := by ring
    _ = _ := by rw [finite_character_mul_conj, mul_one]

theorem finiteFourier_correlation {G : Type*} [AddCommGroup G] [Fintype G]
    (F : G → ℂ) (ψ : AddChar G ℂ) :
    finiteFourier (finiteCorrelation F) ψ = (‖finiteFourier F ψ‖ ^ 2 : ℝ) := by
  unfold finiteFourier finiteCorrelation
  simp only [← complexUniformMean_mul_const]
  rw [complexUniformMean_comm]
  simp only [correlation_character_factor, complexUniformMean_mul_const]
  have ht (y : G) :
      complexUniformMean (fun d => F (y + d) * conj (ψ (y + d))) =
        complexUniformMean (fun d => F d * conj (ψ d)) := by
    exact complexUniformMean_equiv (Equiv.addLeft y) (fun d => F d * conj (ψ d))
  simp only [ht, complexUniformMean_const_mul, complexUniformMean_conj]
  rw [Complex.mul_conj, ← Complex.sq_norm]

end GMZP0
