import GMZP0.FiniteFourierEnergy
import GMZP0.FiniteEnergyPermutation
import GMZP0.FourierCubeExpansion
import GMZP0.GlobalCube
import GMZP0.LocalFourierBound

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


theorem additiveCubeVertex_cons {G : Type*} [AddCommGroup G] (d : ℕ)
    (Y h : G) (v : Fin d → G) (b : Bool) (ω : Fin d → Bool) :
    additiveCubeVertex (d + 1) Y (Fin.cons h v) (Fin.cons b ω) =
      additiveCubeVertex d (Y + if b then h else 0) v ω := by
  simp only [additiveCubeVertex, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]

theorem additiveCubeProduct_zero {G : Type*} [AddCommGroup G]
    (H : G → ℂ) (Y : G) (v : Fin 0 → G) : additiveCubeProduct 0 H Y v = H Y := by
  simp [additiveCubeProduct, additiveCubeVertex, cubeConj]

theorem additiveCubeProduct_succ {G : Type*} [AddCommGroup G] (d : ℕ)
    (H : G → ℂ) (Y h : G) (v : Fin d → G) :
    additiveCubeProduct (d + 1) H Y (Fin.cons h v) =
      additiveCubeProduct d (cubeDerivative H h) Y v := by
  rw [additiveCubeProduct, prod_boolean_cons]
  simp only [additiveCubeVertex_cons, Bool.false_eq_true, if_false, if_true, add_zero,
    cubeConj, Fin.cons_zero, Fin.tail_cons, additiveCubeProduct, cubeDerivative,
    cubeConj_mul, cubeConj_conj, Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro ω _
  congr 3
  simp only [additiveCubeVertex]
  abel

theorem additiveCubeProduct_one {G : Type*} [AddCommGroup G]
    (H : G → ℂ) (Y h : G) :
    additiveCubeProduct 1 H Y (Fin.cons h default) = H Y * conj (H (Y + h)) := by
  rw [additiveCubeProduct_succ, additiveCubeProduct_zero]
  rfl



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



theorem localCubeMoment_le_global {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [DecidableEq G] (n : ℕ) (H : G → ℂ) (r : A → G) (C : ℝ)
    (hν : realUniformMean (fun y => parameterDensity r y ^ 2) ≤ C) :
    localCubeMoment (n + 1) H r ≤ C ^ (n + 2) * globalCubeMoment (n + 1) H := by
  exact localCubeMoment_bound_of_twisted (n + 1) H r C (globalCubeMoment (n + 1) H)
    (globalCubeMoment_nonneg (n + 1) H) hν (globalTwistedCubeMean_le n H)

theorem globalCubeNorm_nonneg {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (H : G → ℂ) : 0 ≤ globalCubeNorm n H := localCubeNorm_nonneg n H _

theorem globalCubeNorm_pow {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (H : G → ℂ) : globalCubeNorm n H ^ (2 ^ (n + 1)) = globalCubeMoment n H :=
  localCubeNorm_pow n H _

theorem localCubeNorm_le_global {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [DecidableEq G] (n : ℕ) (H : G → ℂ) (r : A → G) (C : ℝ)
    (hν : realUniformMean (fun y => parameterDensity r y ^ 2) ≤ C) :
    localCubeNorm (n + 1) H r ≤
      iteratedSqrt (n + 2) (C ^ (n + 2)) * globalCubeNorm (n + 1) H := by
  have hC : 0 ≤ C := (realUniformMean_nonneg _ (fun _ => sq_nonneg _)).trans hν
  have hc := pow_nonneg hC (n + 2)
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))
    (mul_nonneg (iteratedSqrt_nonneg _ _ hc) (globalCubeNorm_nonneg _ H))
  rw [mul_pow, localCubeNorm_pow, globalCubeNorm_pow, iteratedSqrt_pow _ _ hc]
  exact localCubeMoment_le_global n H r C hν

theorem globalCubeMoment_lower_from_local {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [DecidableEq G] (n : ℕ) (H : G → ℂ) (r : A → G) (C ρ : ℝ)
    (hC : 0 < C) (hρ : 0 ≤ ρ)
    (hν : realUniformMean (fun y => parameterDensity r y ^ 2) ≤ C)
    (hLocal : ρ ≤ localCubeNorm (n + 1) H r) :
    ρ ^ (2 ^ (n + 2)) / C ^ (n + 2) ≤ globalCubeMoment (n + 1) H := by
  apply (div_le_iff₀ (pow_pos hC _)).mpr
  have hp := pow_le_pow_left₀ hρ hLocal (2 ^ (n + 2))
  rw [localCubeNorm_pow] at hp
  simpa only [mul_comm] using hp.trans (localCubeMoment_le_global n H r C hν)



theorem character_first_cube_obstruction {G : Type*} [AddCommGroup G] [Fintype G]
    (ψ : AddChar G ℂ) (hψ : ψ ≠ 0) :
    globalTwistedCubeMean 1 (fun y => ψ y) (Fin.cons ψ default) = 1 ∧
      globalCubeMoment 0 (fun y => ψ y) = 0 := by
  have hself : finiteFourier (fun y => ψ y) ψ = 1 := by
    simp only [finiteFourier, finite_character_mul_conj, complexUniformMean_const]
  have hzero : finiteFourier (fun y => ψ y) 0 = 0 := by
    simp only [finiteFourier, AddChar.zero_apply, map_one, mul_one, complexUniformMean]
    rw [AddChar.sum_eq_zero_iff_ne_zero.mpr hψ, zero_div]
  constructor
  · rw [globalTwistedCubeMean_one, hself, norm_one, one_pow, Complex.ofReal_one]
  · rw [globalCubeMoment_one, hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem dimension_one_twist_obstruction : ∃ (H : ZMod 2 → ℂ) (ψ : AddChar (ZMod 2) ℂ),
    (∀ y, ‖H y‖ = 1) ∧
      globalTwistedCubeMean 1 H (Fin.cons ψ default) = 1 ∧ globalCubeMoment 0 H = 0 := by
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : ZMod 2))).mpr one_ne_zero
  have hn : ψ ≠ 0 := by
    intro he
    apply hψ
    simp only [he, AddChar.zero_apply]
  exact ⟨(fun y => ψ y), ψ, (fun y => ψ.norm_apply y), character_first_cube_obstruction ψ hn⟩

end GMZP0
