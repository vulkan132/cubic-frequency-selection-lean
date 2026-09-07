import GMZP0.FiniteFourierEnergy
import GMZP0.FiniteEnergyPermutation

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def finiteCrossCorrelation {G : Type*} [AddCommGroup G] [Fintype G]
    (F H : G → ℂ) (d : G) : ℂ :=
  complexUniformMean (fun y => F (y + d) * conj (H y))

theorem crossCorrelation_character_factor {G : Type*} [AddCommGroup G] [Fintype G]
    (F H : G → ℂ) (ψ : AddChar G ℂ) (y d : G) :
    F (y + d) * conj (H y) * conj (ψ d) =
      (F (y + d) * conj (ψ (y + d))) * conj (H y * conj (ψ y)) := by
  symm
  simp only [AddChar.map_add_eq_mul, map_mul, starRingEnd_self_apply]
  calc
    _ = (F (y + d) * conj (H y) * conj (ψ d)) * (ψ y * conj (ψ y)) := by ring
    _ = _ := by rw [finite_character_mul_conj, mul_one]

theorem finiteFourier_crossCorrelation {G : Type*} [AddCommGroup G] [Fintype G]
    (F H : G → ℂ) (ψ : AddChar G ℂ) :
    finiteFourier (finiteCrossCorrelation F H) ψ =
      finiteFourier F ψ * conj (finiteFourier H ψ) := by
  unfold finiteFourier finiteCrossCorrelation
  simp only [← complexUniformMean_mul_const]
  rw [complexUniformMean_comm]
  simp only [crossCorrelation_character_factor, complexUniformMean_mul_const]
  have ht (y : G) :
      complexUniformMean (fun d => F (y + d) * conj (ψ (y + d))) =
        complexUniformMean (fun d => F d * conj (ψ d)) := by
    exact complexUniformMean_equiv (Equiv.addLeft y) (fun d => F d * conj (ψ d))
  simp only [ht, complexUniformMean_const_mul, complexUniformMean_conj]

theorem finiteFourier_modulation {G : Type*} [AddCommGroup G] [Fintype G]
    (H : G → ℂ) (ψ φ : AddChar G ℂ) :
    finiteFourier (fun y => H y * conj (ψ y)) φ = finiteFourier H (φ + ψ) := by
  unfold finiteFourier
  congr 1
  funext y
  simp only [AddChar.add_apply, map_mul]
  ring

def cubeDerivative {G : Type*} [AddCommGroup G] (H : G → ℂ) (h y : G) : ℂ :=
  H y * conj (H (y + h))

theorem derivativeFourier_crossCorrelation {G : Type*} [AddCommGroup G] [Fintype G]
    (H : G → ℂ) (ψ : AddChar G ℂ) (h : G) :
    finiteFourier (cubeDerivative H h) ψ =
      conj (finiteCrossCorrelation H (fun y => H y * conj (ψ y)) h) := by
  rw [finiteCrossCorrelation, ← complexUniformMean_conj]
  unfold finiteFourier cubeDerivative
  congr 1
  funext y
  simp only [map_mul, starRingEnd_self_apply]
  ring

theorem derivativeFourier_energy {G : Type*} [AddCommGroup G] [Fintype G]
    (H : G → ℂ) (ψ : AddChar G ℂ) :
    realUniformMean (fun h => ‖finiteFourier (cubeDerivative H h) ψ‖ ^ 2) =
      ∑ φ : AddChar G ℂ, ‖finiteFourier H φ‖ ^ 2 * ‖finiteFourier H (φ + ψ)‖ ^ 2 := by
  simp only [derivativeFourier_crossCorrelation, Complex.norm_conj]
  rw [← finiteFourier_parseval]
  simp only [finiteFourier_crossCorrelation, finiteFourier_modulation, norm_mul, Complex.norm_conj, mul_pow]

theorem derivativeFourier_energy_le {G : Type*} [AddCommGroup G] [Fintype G]
    (H : G → ℂ) (ψ : AddChar G ℂ) :
    realUniformMean (fun h => ‖finiteFourier (cubeDerivative H h) ψ‖ ^ 2) ≤
      ∑ φ : AddChar G ℂ, ‖finiteFourier H φ‖ ^ 4 := by
  rw [derivativeFourier_energy]
  have ht := finite_self_correlation_le (Equiv.addRight ψ)
    (fun φ : AddChar G ℂ => ‖finiteFourier H φ‖ ^ 2)
  simpa only [Equiv.coe_addRight, ← pow_mul] using ht

end GMZP0
