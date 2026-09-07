import GMZP0.GlobalCube
import GMZP0.CyclicLocalCube

/-! Exact global cube frequency averaging for the same bounded real lift. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

def globalRealCubeMass {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (σ F : G → ℝ) : ℝ :=
  realUniformMean (fun Y : G => realUniformMean (fun v : Fin (n + 1) → G =>
    if realSignedCubeSum (n + 1) (fun ω => F (additiveCubeVertex (n + 1) Y v ω)) = 0
    then ∏ ω, σ (additiveCubeVertex (n + 1) Y v ω) else 0))

theorem globalCubeMoment_real_expansion {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (H : G → ℂ) :
    globalCubeMoment n H = realUniformMean (fun Y : G =>
      realUniformMean (fun v : Fin (n + 1) → G => (additiveCubeProduct (n + 1) H Y v).re)) := by
  have he := congrArg Complex.re (globalCubeMoment_additive n H)
  simpa only [Complex.ofReal_re, complexUniformMean_re] using he

theorem global_frequency_moment_exact {G : Type*} [AddCommGroup G] [Fintype G]
    {n M : ℕ} (hn : n + 1 ≤ 7) (hM : 0 < M) (σ F : G → ℝ)
    (hgrid : ∀ Y, ∃ k : ℤ, F Y = (k : ℝ) / M) (hF : ∀ Y, |F Y| ≤ 3) :
    realUniformMean (fun j : Fin (1024 * M) => globalCubeMoment n
      (fun Y => (σ Y : ℂ) * circleCharacter ((meshFrequency M j * F Y : ℝ) : Frequency))) =
      globalRealCubeMass n σ F := by
  simp only [globalCubeMoment_real_expansion, globalRealCubeMass]
  rw [realUniformMean_comm]
  congr 1
  funext Y
  rw [realUniformMean_comm]
  congr 1
  funext v
  exact weighted_frequency_cube_real hn hM
    (fun ω => σ (additiveCubeVertex (n + 1) Y v ω))
    (fun ω => F (additiveCubeVertex (n + 1) Y v ω))
    (fun ω => hgrid _) (fun ω => hF _)

def cyclicGlobalSeventhMoment (N q M : ℕ) [NeZero q]
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) : ℝ :=
  realUniformMean (fun x : Fin N => realUniformMean (fun j : Fin (1024 * M) =>
    globalCubeMoment 6 (modulatedCyclicField N q M σ F x j)))

def cyclicGlobalRealSevenMass (N q : ℕ) [NeZero q]
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) : ℝ :=
  realUniformMean (fun x : Fin N =>
    globalRealCubeMass 6 (fun Y => cyclicField N q σ 0 x Y) (F x))

theorem cyclicGlobalSeventhMoment_eq_mass {N q M : ℕ} [NeZero q] (hM : 0 < M)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ)
    (hgrid : ∀ x Y, ∃ k : ℤ, F x Y = (k : ℝ) / M) (hF : ∀ x Y, |F x Y| ≤ 3) :
    cyclicGlobalSeventhMoment N q M σ F = cyclicGlobalRealSevenMass N q σ F := by
  unfold cyclicGlobalSeventhMoment cyclicGlobalRealSevenMass
  congr 1
  funext x
  exact global_frequency_moment_exact (by decide : 6 + 1 ≤ 7) hM
    (fun Y => cyclicField N q σ 0 x Y) (F x) (hgrid x) (hF x)

end GMZP0
