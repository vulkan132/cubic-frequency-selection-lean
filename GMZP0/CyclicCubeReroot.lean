import GMZP0.CyclicCubeExpansion

/-! Cyclic translation of the complete cube average, without division by the lag step. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def cubeShiftSum (ℓ : ℕ) (u : CubeShiftPairs ℓ) (ω : Fin 4 → Bool) : ℤ :=
  fourShiftSum ℓ (cubeVertex u ω)

def cyclicCubeVertex (q ℓ : ℕ) (h : ℤ) (Y : ZMod q) (u : CubeShiftPairs ℓ)
    (ω : Fin 4 → Bool) : ZMod q := Y + ((2 * h * cubeShiftSum ℓ u ω : ℤ) : ZMod q)

def cyclicRerootedVertexG (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (Y : ZMod q) (h t k : ℤ)
    (u : CubeShiftPairs ℓ) (ω : Fin 4 → Bool) : ℂ :=
  let v := cyclicCubeVertex q ℓ h Y u ω
  ((cyclicField N q σ 0 x v : ℝ) : ℂ) * conj (cyclicField N q lam 1 x v) *
    circleCharacter (-((t + h - k - cubeShiftSum ℓ u ω) ^ 3 • cyclicField N q p 0 x v))

def cyclicRerootedCubeProduct (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (Y : ZMod q) (h t k : ℤ) (u : CubeShiftPairs ℓ) : ℂ :=
  ∏ ω : Fin 4 → Bool, cubeConj 4 ω (cyclicRerootedVertexG N q ℓ p σ lam x Y h t k u ω)

theorem cyclicLagG_shift_reroot (N q : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k s : ℤ) :
    cyclicLagG N q p σ lam x v h t (k + s) =
      ((cyclicField N q σ 0 x ((v + ((2 * h * k : ℤ) : ZMod q)) +
        ((2 * h * s : ℤ) : ZMod q)) : ℝ) : ℂ) *
      conj (cyclicField N q lam 1 x ((v + ((2 * h * k : ℤ) : ZMod q)) +
        ((2 * h * s : ℤ) : ZMod q))) *
      circleCharacter (-((t + h - k - s) ^ 3 • cyclicField N q p 0 x
        ((v + ((2 * h * k : ℤ) : ZMod q)) + ((2 * h * s : ℤ) : ZMod q)))) := by
  have hv : v + ((2 * h * (k + s) : ℤ) : ZMod q) =
      (v + ((2 * h * k : ℤ) : ZMod q)) + ((2 * h * s : ℤ) : ZMod q) := by
    push_cast
    ring
  have ht : t + h - (k + s) = t + h - k - s := by ring
  simp only [cyclicLagG, hv, ht]

theorem cyclicCubeProduct_reroot (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ) (u : CubeShiftPairs ℓ) :
    cyclicCubeProduct N q ℓ p σ lam x v h t k u =
      cyclicRerootedCubeProduct N q ℓ p σ lam x (v + ((2 * h * k : ℤ) : ZMod q)) h t k u := by
  simp only [cyclicCubeProduct, cubeProduct, cyclicLagBoxFunction, cyclicLagG_shift_reroot,
    cyclicRerootedCubeProduct, cyclicRerootedVertexG, cyclicCubeVertex, cubeShiftSum]

def cyclicCubeReroot (N q : ℕ) : CyclicBoxSamplingSpace N q ≃ CyclicBoxSamplingSpace N q where
  toFun z := ((z.1.1, z.1.2.1,
    z.1.2.2.1 + ((2 * z.1.2.1.val * z.2.val : ℤ) : ZMod q), z.1.2.2.2), z.2)
  invFun z := ((z.1.1, z.1.2.1,
    z.1.2.2.1 - ((2 * z.1.2.1.val * z.2.val : ℤ) : ZMod q), z.1.2.2.2), z.2)
  left_inv z := by rcases z with ⟨⟨x, h, v, t⟩, k⟩; simp
  right_inv z := by rcases z with ⟨⟨x, h, v, t⟩, k⟩; simp

def cyclicRerootedCubeAverage (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℂ :=
  complexUniformMean (fun z : CyclicBoxSamplingSpace N q =>
    complexUniformMean (fun u : CubeShiftPairs ℓ => cyclicRerootedCubeProduct N q ℓ p σ lam
      z.1.1 z.1.2.2.1 z.1.2.1.val (label z.1.2.2.2) z.2.val u))

theorem cyclicCubeAverage_reroot (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    cyclicCubeAverage N q ℓ p σ lam = cyclicRerootedCubeAverage N q ℓ p σ lam := by
  simp only [cyclicCubeAverage, cyclicCubeProduct_reroot, cyclicRerootedCubeAverage]
  exact complexUniformMean_equiv (cyclicCubeReroot N q)
    (fun z => complexUniformMean (fun u : CubeShiftPairs ℓ =>
      cyclicRerootedCubeProduct N q ℓ p σ lam z.1.1 z.1.2.2.1 z.1.2.1.val
        (label z.1.2.2.2) z.2.val u))

theorem cyclicRerootedCubeAverage_eq_moment (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    cyclicRerootedCubeAverage N q ℓ p σ lam = (cyclicBoxMomentAverage N q ℓ p σ lam : ℂ) := by
  rw [← cyclicCubeAverage_reroot, cyclic_cube_expansion]

end GMZP0
