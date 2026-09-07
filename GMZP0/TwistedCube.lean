import GMZP0.FiniteCrossCorrelation
import GMZP0.FourierCubeExpansion
import GMZP0.GlobalCube

/-! Character-twisted cube bounds for every dimension at least two. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem globalTwistedCubeMean_succ {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (H : G → ℂ) (ψ₀ : AddChar G ℂ) (ψ : Fin d → AddChar G ℂ) :
    globalTwistedCubeMean (d + 1) H (Fin.cons ψ₀ ψ) =
      complexUniformMean (fun h => ψ₀ h * globalTwistedCubeMean d (cubeDerivative H h) ψ) := by
  unfold globalTwistedCubeMean
  conv_lhs => arg 1; ext Y; rw [complexUniformMean_cons d]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, additiveCubeProduct_succ,
    mul_assoc, complexUniformMean_const_mul]
  rw [complexUniformMean_comm]
  simp only [complexUniformMean_const_mul]

theorem globalTwistedCubeMean_zero_twist {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (H : G → ℂ) :
    globalTwistedCubeMean (n + 1) H (fun _ => 0) = (globalCubeMoment n H : ℂ) := by
  simpa only [globalTwistedCubeMean, AddChar.zero_apply, Finset.prod_const_one, one_mul]
    using (globalCubeMoment_additive n H).symm

theorem globalTwistedCubeMean_one {G : Type*} [AddCommGroup G] [Fintype G]
    (H : G → ℂ) (ψ : AddChar G ℂ) :
    globalTwistedCubeMean 1 H (Fin.cons ψ default) = (‖finiteFourier H ψ‖ ^ 2 : ℝ) := by
  have he : globalTwistedCubeMean 1 H (Fin.cons ψ default) =
      conj (finiteFourier (finiteCorrelation H) ψ) := by
    unfold globalTwistedCubeMean
    conv_lhs => arg 1; ext Y; rw [complexUniformMean_cons 0]
    simp only [complexUniformMean_unique, Fin.prod_univ_succ, Fin.cons_zero,
      Finset.univ_eq_empty, Finset.prod_empty, mul_one, additiveCubeProduct_one]
    unfold finiteFourier finiteCorrelation
    rw [← complexUniformMean_conj]
    simp only [← complexUniformMean_mul_const, ← complexUniformMean_conj,
      map_mul, starRingEnd_self_apply]
    rw [complexUniformMean_comm]
    congr 1
    funext Y
    congr 1
    funext h
    ring
  rw [he, finiteFourier_correlation, Complex.conj_ofReal]



theorem globalCubeMoment_nonneg {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (H : G → ℂ) : 0 ≤ globalCubeMoment n H := localCubeMoment_nonneg n H _

theorem globalCubeMoment_succ {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (H : G → ℂ) : globalCubeMoment (n + 1) H =
      realUniformMean (fun h => globalCubeMoment n (cubeDerivative H h)) := by
  have hz : Fin.cons (0 : AddChar G ℂ) (fun _ : Fin (n + 1) => 0) = (fun _ => (0 : AddChar G ℂ)) := by
    funext i
    cases i using Fin.cases <;> rfl
  have ht := globalTwistedCubeMean_succ (n + 1) H 0 (fun _ => 0)
  simp only [hz, globalTwistedCubeMean_zero_twist, AddChar.zero_apply, one_mul,
    complexUniformMean_ofReal] at ht
  exact_mod_cast ht

theorem globalCubeMoment_one {G : Type*} [AddCommGroup G] [Fintype G]
    (H : G → ℂ) : globalCubeMoment 0 H = ‖finiteFourier H 0‖ ^ 2 := by
  have hz : Fin.cons (0 : AddChar G ℂ) (default : Fin 0 → AddChar G ℂ) = (fun _ => (0 : AddChar G ℂ)) := by
    funext i
    fin_cases i
    rfl
  have ht := globalTwistedCubeMean_one H 0
  rw [hz, globalTwistedCubeMean_zero_twist] at ht
  exact_mod_cast ht

theorem globalCubeMoment_two_fourier {G : Type*} [AddCommGroup G] [Fintype G]
    (H : G → ℂ) : globalCubeMoment 1 H = ∑ φ : AddChar G ℂ, ‖finiteFourier H φ‖ ^ 4 := by
  rw [globalCubeMoment_succ]
  simp only [globalCubeMoment_one, derivativeFourier_energy, add_zero]
  apply Finset.sum_congr rfl
  intro φ _
  ring

theorem globalTwistedCubeMean_two_le {G : Type*} [AddCommGroup G] [Fintype G]
    (H : G → ℂ) (ψ₀ ψ₁ : AddChar G ℂ) :
    ‖globalTwistedCubeMean 2 H (Fin.cons ψ₀ (Fin.cons ψ₁ default))‖ ≤ globalCubeMoment 1 H := by
  rw [globalTwistedCubeMean_succ]
  simp only [globalTwistedCubeMean_one]
  calc
    _ ≤ realUniformMean (fun h => ‖ψ₀ h * (‖finiteFourier (cubeDerivative H h) ψ₁‖ ^ 2 : ℝ)‖) :=
      norm_complexUniformMean_le_mean_norm _
    _ = realUniformMean (fun h => ‖finiteFourier (cubeDerivative H h) ψ₁‖ ^ 2) := by
      simp only [norm_mul, ψ₀.norm_apply, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_pow, abs_norm]
    _ ≤ _ := by rw [globalCubeMoment_two_fourier]; exact derivativeFourier_energy_le H ψ₁

theorem globalTwistedCubeMean_le {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) : ∀ (H : G → ℂ) (ψ : Fin (n + 2) → AddChar G ℂ),
      ‖globalTwistedCubeMean (n + 2) H ψ‖ ≤ globalCubeMoment (n + 1) H := by
  induction n with
  | zero =>
      intro H ψ
      have he : ψ = Fin.cons (ψ 0) (Fin.cons (ψ 1) default) := by
        funext i
        fin_cases i <;> rfl
      rw [he]
      exact globalTwistedCubeMean_two_le H (ψ 0) (ψ 1)
  | succ n ih =>
      intro H ψ
      rw [← Fin.cons_self_tail ψ, globalTwistedCubeMean_succ]
      calc
        _ ≤ realUniformMean (fun h =>
            ‖ψ 0 h * globalTwistedCubeMean (n + 2) (cubeDerivative H h) (Fin.tail ψ)‖) :=
          norm_complexUniformMean_le_mean_norm _
        _ ≤ realUniformMean (fun h => globalCubeMoment (n + 1) (cubeDerivative H h)) := by
          apply realUniformMean_mono
          intro h
          rw [norm_mul, (ψ 0).norm_apply, one_mul]
          exact ih (cubeDerivative H h) (Fin.tail ψ)
        _ = _ := (globalCubeMoment_succ (n + 1) H).symm




end GMZP0
