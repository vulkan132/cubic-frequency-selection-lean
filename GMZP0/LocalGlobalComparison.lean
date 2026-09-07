import GMZP0.TwistedCube
import GMZP0.LocalFourierBound

/-! The complete multiset local-to-global comparison, with uniform density normalization. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

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




end GMZP0
