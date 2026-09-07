import GMZP0.CubeExpansion
import GMZP0.BoxNorm

/-! Local Gowers moments from a uniform multiset of shifts, including multiplicities. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def localBoxFunction {G A : Type*} [AddCommGroup G] (n : ℕ) (H : G → ℂ)
    (r : A → G) (Y : G) (v : Fin (n + 1) → A) : ℂ := H (Y + ∑ i, r (v i))

def localCubeMoment {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A]
    (n : ℕ) (H : G → ℂ) (r : A → G) : ℝ :=
  realUniformMean (fun Y : G => boxMoment n (localBoxFunction n H r Y))

def localCubeNorm {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A]
    (n : ℕ) (H : G → ℂ) (r : A → G) : ℝ := iteratedSqrt (n + 1) (localCubeMoment n H r)

theorem localCubeMoment_nonneg {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A]
    (n : ℕ) (H : G → ℂ) (r : A → G) : 0 ≤ localCubeMoment n H r :=
  realUniformMean_nonneg _ (fun Y => boxMoment_nonneg n (localBoxFunction n H r Y))

theorem localCubeMoment_le_one {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A] [Nonempty A]
    (n : ℕ) (H : G → ℂ) (r : A → G) (hH : ∀ Y, ‖H Y‖ ≤ 1) : localCubeMoment n H r ≤ 1 := by
  have hm := realUniformMean_mono
    (fun Y : G => boxMoment n (localBoxFunction n H r Y)) (fun _ : G => 1)
    (fun Y => boxMoment_le_one n _ (fun v => hH (Y + ∑ i, r (v i))))
  simpa only [localCubeMoment, realUniformMean_const] using hm

theorem localCubeNorm_nonneg {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A]
    (n : ℕ) (H : G → ℂ) (r : A → G) : 0 ≤ localCubeNorm n H r :=
  iteratedSqrt_nonneg _ _ (localCubeMoment_nonneg n H r)

theorem localCubeNorm_pow {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A]
    (n : ℕ) (H : G → ℂ) (r : A → G) : localCubeNorm n H r ^ (2 ^ (n + 1)) = localCubeMoment n H r :=
  iteratedSqrt_pow _ _ (localCubeMoment_nonneg n H r)

theorem localCubeNorm_le_one {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A] [Nonempty A]
    (n : ℕ) (H : G → ℂ) (r : A → G) (hH : ∀ Y, ‖H Y‖ ≤ 1) : localCubeNorm n H r ≤ 1 := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) zero_le_one
  rw [localCubeNorm_pow, one_pow]
  exact localCubeMoment_le_one n H r hH

theorem localCubeMoment_complex {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A]
    (n : ℕ) (H : G → ℂ) (r : A → G) :
    complexUniformMean (fun Y : G => cubeMean (n + 1) (localBoxFunction n H r Y)) =
      (localCubeMoment n H r : ℂ) := by
  simp only [cubeMean_eq_boxMoment, complexUniformMean_ofReal, localCubeMoment]

end GMZP0
