import GMZP0.BoxNorm
import GMZP0.CubicFaces

/-! The box inequality applied to the four independent shifts of the actual original sequence. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def shiftCubicFaces (ℓ : ℕ) (t k : ℤ) (c : Frequency)
    (i : Fin 4) (u : FourShiftSpace ℓ) : ℂ := cubicFacePhase t k c (fun j => (u j).val) i

theorem shiftCubicFaces_norm (ℓ : ℕ) (t k : ℤ) (c : Frequency) (i : Fin 4) (u : FourShiftSpace ℓ) :
    ‖shiftCubicFaces ℓ t k c i u‖ = 1 := cubicFacePhase_norm _ _ _ _ _

theorem shiftCubicFaces_independent (ℓ : ℕ) (t k : ℤ) (c : Frequency) (i : Fin 4) :
    FaceIndependent (shiftCubicFaces ℓ t k c i) i := by
  intro u a
  have he : (fun j => ((Function.update u i a) j).val) =
      Function.update (fun j => (u j).val) i a.val := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update, hj]
  simp only [shiftCubicFaces, he, cubicFacePhase_independent]

def cyclicLagBoxFunction (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ) (u : FourShiftSpace ℓ) : ℂ :=
  cyclicLagG N q p σ lam x v h t (k + fourShiftSum ℓ u)

def cyclicLagBoxNorm (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ) : ℝ :=
  boxNorm 3 (cyclicLagBoxFunction N q ℓ p σ lam x v h t k)

theorem cyclicLagBoxNorm_nonneg (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ) :
    0 ≤ cyclicLagBoxNorm N q ℓ p σ lam x v h t k := boxNorm_nonneg _ _

theorem cyclicLagBoxNorm_le_one (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    cyclicLagBoxNorm N q ℓ p σ lam x v h t k ≤ 1 :=
  boxNorm_le_one 3 _ (fun u =>
    cyclicLagG_norm_le N q p σ lam x v h t (k + fourShiftSum ℓ u) hσ hlam)

theorem cyclicLagBoxNorm_pow (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ) :
    cyclicLagBoxNorm N q ℓ p σ lam x v h t k ^ 16 =
      boxMoment 3 (cyclicLagBoxFunction N q ℓ p σ lam x v h t k) := boxNorm_pow _ _

theorem cyclicShiftMean_le_boxNorm (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ) :
    ‖complexUniformMean (fun u : FourShiftSpace ℓ =>
      cyclicLagSequence N q p σ lam x v h t (k + fourShiftSum ℓ u))‖ ≤
      cyclicLagBoxNorm N q ℓ p σ lam x v h t k := by
  let c := originalFieldExtension N p 0
    ((x.val : ℤ) + 1 + h, ((v + ((h ^ 2 + 2 * h * t : ℤ) : ZMod q)).val : ℤ))
  have he : complexUniformMean (fun u : FourShiftSpace ℓ =>
      cyclicLagSequence N q p σ lam x v h t (k + fourShiftSum ℓ u)) =
        boxCorrelation (cyclicLagBoxFunction N q ℓ p σ lam x v h t k) (shiftCubicFaces ℓ t k c) := by
    simp only [boxCorrelation, cyclicLagBoxFunction, shiftCubicFaces, fourShiftSum,
      cyclicLagSequence_four_faces, c]
  rw [he]
  exact boxCorrelation_le_boxNorm 3 _ _ (shiftCubicFaces_norm ℓ t k c)
    (shiftCubicFaces_independent ℓ t k c)

theorem cyclicSmoothedLagB_le_boxSum {N : ℕ} (hN : 0 < N) (q ℓ : ℕ)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (x : Fin N) (v : ZMod q) (h t : ℤ) :
    ‖cyclicSmoothedLagB N q ℓ p σ lam x v h t‖ ≤
      (∑ k ∈ lagInnerInterval N h t, cyclicLagBoxNorm N q ℓ p σ lam x v h t k) / N := by
  rw [cyclicSmoothedLagB, fourShiftSmoothedAverage, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (le_of_lt (show (0 : ℝ) < N by exact_mod_cast hN))
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
    cyclicShiftMean_le_boxNorm N q ℓ p σ lam x v h t k)

end GMZP0
