import GMZP0.CyclicLocalCube

/-! The complete mesh average is exactly the original weighted real-zero four-cube mass. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def cyclicLocalFourMoment (N q ℓ M : ℕ) [NeZero q] (σ : Base N → ℝ)
    (F : Fin N → ZMod q → ℝ) : ℝ :=
  realUniformMean (fun x : Fin N => realUniformMean (fun j : Fin (1024 * M) =>
    realUniformMean (fun h : Fin N => localCubeMoment 3
      (modulatedCyclicField N q M σ F x j) (cyclicShiftMap q ℓ (label h)))))

def cyclicLocalFourthNormAverage (N q ℓ M : ℕ) [NeZero q] (σ : Base N → ℝ)
    (F : Fin N → ZMod q → ℝ) : ℝ :=
  realUniformMean (fun x : Fin N => realUniformMean (fun j : Fin (1024 * M) =>
    realUniformMean (fun h : Fin N => localCubeNorm 3
      (modulatedCyclicField N q M σ F x j) (cyclicShiftMap q ℓ (label h)) ^ 16)))

theorem cyclicLocalFourMoment_eq_mass {N q ℓ M : ℕ} [NeZero q] (hM : 0 < M)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ)
    (hgrid : ∀ x Y, ∃ k : ℤ, F x Y = (k : ℝ) / M) (hF : ∀ x Y, |F x Y| ≤ 3) :
    cyclicLocalFourMoment N q ℓ M σ F = cyclicRealCubeMass N q ℓ σ F := by
  unfold cyclicLocalFourMoment cyclicRealCubeMass
  rw [realUniformMean_prod_four (fun (x : Fin N) (h : Fin N) (Y : ZMod q) (u : CubeShiftPairs ℓ) =>
    if cyclicRealCubeDifference q ℓ F x Y (label h) u = 0
    then cyclicCubeWeight N q ℓ σ x Y (label h) u else 0)]
  congr 1
  funext x
  rw [realUniformMean_comm]
  congr 1
  funext h
  exact cyclic_local_frequency_row hM σ F hgrid hF x (label h)

theorem cyclicLocalFourthNormAverage_eq_moment (N q ℓ M : ℕ) [NeZero q]
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) :
    cyclicLocalFourthNormAverage N q ℓ M σ F = cyclicLocalFourMoment N q ℓ M σ F := by
  unfold cyclicLocalFourthNormAverage cyclicLocalFourMoment
  simp only [show (16 : ℕ) = 2 ^ (3 + 1) by decide, localCubeNorm_pow]

theorem cyclicLocalFourthNormAverage_eq_mass {N q ℓ M : ℕ} [NeZero q] (hM : 0 < M)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ)
    (hgrid : ∀ x Y, ∃ k : ℤ, F x Y = (k : ℝ) / M) (hF : ∀ x Y, |F x Y| ≤ 3) :
    cyclicLocalFourthNormAverage N q ℓ M σ F = cyclicRealCubeMass N q ℓ σ F := by
  rw [cyclicLocalFourthNormAverage_eq_moment]
  exact cyclicLocalFourMoment_eq_mass hM σ F hgrid hF

end GMZP0
