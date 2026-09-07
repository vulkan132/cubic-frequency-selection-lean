import GMZP0.FlatCubeCoordinates
import Mathlib.Algebra.Field.ZMod

/-! A pair of distinct cube labels collides for at most one value of a separating shift. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem cube_collision_update_unique {q ℓ : ℕ} [Fact q.Prime] (hℓ : 2 * ℓ < q)
    (h : ℤ) (hs : ((2 * h : ℤ) : ZMod q) ≠ 0) (Y : ZMod q)
    (ω ω' : Fin 4 → Bool) (i : Fin 4) (hi : ω i ≠ ω' i)
    (v : FlatCubeShiftSpace ℓ) (a b : smoothingShiftLabels ℓ)
    (ha : cyclicCubeVertex q ℓ h Y (flatCubePairsEquiv ℓ (Function.update v (i, ω i) a)) ω =
      cyclicCubeVertex q ℓ h Y (flatCubePairsEquiv ℓ (Function.update v (i, ω i) a)) ω')
    (hb : cyclicCubeVertex q ℓ h Y (flatCubePairsEquiv ℓ (Function.update v (i, ω i) b)) ω =
      cyclicCubeVertex q ℓ h Y (flatCubePairsEquiv ℓ (Function.update v (i, ω i) b)) ω') :
    a = b := by
  simp only [cyclicCubeVertex, cubeShiftSum_flat,
    flatCubeShiftSum_update_other ℓ v ω ω' i hi] at ha hb
  have he := add_left_cancel (ha.trans hb.symm)
  have hm : ((flatCubeShiftSum ℓ (Function.update v (i, ω i) a) ω : ℤ) : ZMod q) =
      ((flatCubeShiftSum ℓ (Function.update v (i, ω i) b) ω : ℤ) : ZMod q) := by
    apply mul_left_cancel₀ hs
    simpa only [Int.cast_mul] using he
  have hd : ((a.val - b.val : ℤ) : ZMod q) = 0 := by
    rw [← flatCubeShiftSum_update_sub ℓ v ω i a b, Int.cast_sub, hm, sub_self]
  apply smoothingShift_cast_injective hℓ
  exact sub_eq_zero.mp (by simpa only [Int.cast_sub] using hd)

theorem cube_pair_collision_probability {q ℓ : ℕ} [Fact q.Prime] (hℓ : 2 * ℓ < q)
    (h : ℤ) (hs : ((2 * h : ℤ) : ZMod q) ≠ 0) (Y : ZMod q)
    (ω ω' : Fin 4 → Bool) (hne : ω ≠ ω') :
    realUniformMean (fun u : CubeShiftPairs ℓ =>
      if cyclicCubeVertex q ℓ h Y u ω = cyclicCubeVertex q ℓ h Y u ω' then 1 else 0) ≤
        1 / (2 * (ℓ : ℝ) + 1) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, ω i ≠ ω' i := by
    by_contra he
    push Not at he
    exact hne (funext he)
  rw [← realUniformMean_equiv (flatCubePairsEquiv ℓ)]
  have hu := uniform_event_le_of_update_unique (i, ω i)
    (fun v : FlatCubeShiftSpace ℓ =>
      cyclicCubeVertex q ℓ h Y (flatCubePairsEquiv ℓ v) ω =
        cyclicCubeVertex q ℓ h Y (flatCubePairsEquiv ℓ v) ω')
    (cube_collision_update_unique hℓ h hs Y ω ω' i hi)
  simpa only [Fintype.card_coe, card_smoothingShiftLabels, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one] using hu

end GMZP0
