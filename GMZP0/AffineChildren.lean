import GMZP0.CircleGrid
import GMZP0.AffineNoRelation

/-! Actual finite constant-in-y children for the affine slope-relation rows. -/
noncomputable section
namespace GMZP0

/-- A relation at slope scale N^(-5) puts every original vertical increment in a cubic major arc. -/
theorem affine_increment_majorArc {N : ℕ} (hN : 0 < N) (Q R : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hQR : Q ≤ R) (hER : E ≤ R) (a : Frequency) (y : Fin (N ^ 2))
    (ha : AffineTopRelation Q E N a) : MajorArc R N ((label y : ℤ) • a) := by
  obtain ⟨q, hq, hqQ, hb⟩ := ha
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := hnR.ne'
  have hy : (label y : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast (Nat.succ_le_of_lt y.isLt)
  have he : q • ((label y : ℤ) • a) = (label y) • (q • a) := by
    rw [natCast_zsmul]
    module
  refine ⟨q, hq, hqQ.trans hQR, ?_⟩
  rw [he]
  calc
    ‖label y • (q • a)‖ ≤ (label y : ℝ) * ‖q • a‖ := norm_nsmul_le
    _ ≤ (label y : ℝ) * (E / (N : ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) ^ 2 * (E / (N : ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_right hy (by positivity)
    _ = E / (N : ℝ) ^ 3 := by field_simp
    _ ≤ (R : ℝ) / (N : ℝ) ^ 3 := div_le_div_of_nonneg_right hER (by positivity)

/-- Each child is global on the original box and constant only in the vertical coordinate. -/
def affineConstantChild {N J : ℕ} (b : Fin N → Frequency) (offset : Fin J → Frequency)
    (i : Fin J) (z : Base N) : Frequency := b z.1 + offset i

/-- Horizontal dependence of the original intercept is retained in every child. -/
theorem affineConstantChild_vertical_constant {N J : ℕ} (b : Fin N → Frequency)
    (offset : Fin J → Frequency) (i : Fin J) (x : Fin N) (y y' : Fin (N ^ 2)) :
    affineConstantChild b offset i (x, y) = affineConstantChild b offset i (x, y') := rfl

/-- Parent-minus-child error is exactly the original slope increment minus the chosen grid value. -/
theorem affine_child_error {N J : ℕ} (a b : Fin N → Frequency) (offset : Fin J → Frequency)
    (i : Fin J) (z : Base N) :
    affineOriginalProfile a b z - affineConstantChild b offset i z =
      (label z.2 : ℤ) • a z.1 - offset i := by
  simp only [affineOriginalProfile, affineVerticalProfile, affineConstantChild]
  abel

/-- The finite offset list precedes the slope and intercept fields; every relation point receives an actual child. -/
theorem uniform_affine_constant_children (Q : ℕ) (hQ : 0 < Q) (E : ℝ) (hE : 0 ≤ E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∀ N : ℕ, 0 < N → ∃ offset : Fin J → Frequency,
      ∀ a : Fin N → Frequency, ∃ j : Base N → Fin J,
        ∀ b : Fin N → Frequency, ∀ z : Base N, AffineTopRelation Q E N (a z.1) →
          ‖affineOriginalProfile a b z - affineConstantChild b offset (j z) z‖ ≤
            ε / (2 * (N : ℝ) ^ 3) := by
  classical
  let R := max Q (Nat.ceil E)
  have hR : 0 < R := hQ.trans_le (le_max_left _ _)
  have hER : E ≤ (R : ℝ) := (Nat.le_ceil E).trans (by exact_mod_cast (le_max_right Q (Nat.ceil E)))
  obtain ⟨J, hJ, hgrid⟩ := majorArc_universal_circle_list R hR ε hε
  refine ⟨J, hJ, ?_⟩
  intro N hN
  obtain ⟨offset, hoffset⟩ := hgrid N hN
  refine ⟨offset, ?_⟩
  intro a
  have hp (z : Base N) : ∃ i : Fin J, AffineTopRelation Q E N (a z.1) →
      ‖(label z.2 : ℤ) • a z.1 - offset i‖ ≤ ε / (2 * (N : ℝ) ^ 3) := by
    by_cases hz : AffineTopRelation Q E N (a z.1)
    · obtain ⟨i, hi⟩ := hoffset ((label z.2 : ℤ) • a z.1)
        (affine_increment_majorArc hN Q R E hE (le_max_left _ _) hER (a z.1) z.2 hz)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨0, hJ⟩, fun h => (hz h).elim⟩
  choose j hj using hp
  refine ⟨j, ?_⟩
  intro b z hz
  rw [affine_child_error]
  exact hj z hz

end GMZP0
