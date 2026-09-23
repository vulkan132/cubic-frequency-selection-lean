import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Scope obstructions for clearing denominators: origin compatibility
matters, and nonlinear rational coordinate images need not be additive. -/
namespace GMZP0

/-- The rational affine translate Z+1/2 contains no full q*Z, since it
misses zero. Rational inverse maps alone do not imply the lower inclusion. -/
theorem rational_affine_origin_obstruction :
    ¬ ∃ q : ℕ, 0 < q ∧ ∀ z : ℤ, ∃ w : ℤ,
      (w : ℝ) + 1 / 2 = (q : ℝ) * (z : ℝ) := by
  rintro ⟨q, _, hq⟩
  obtain ⟨w, hw⟩ := hq 0
  have hwR : (2 : ℝ) * (w : ℝ) = -1 := by norm_num at hw; linarith
  have hwZ : (2 : ℤ) * w = -1 := by exact_mod_cast hwR
  omega

/-- The image of the full integer grid under a rational triangular
polynomial bijection need not be closed under ordinary vector addition. -/
theorem rational_triangular_lattice_image_not_additive :
    let S : Set (ℝ × ℝ × ℝ) :=
      {v | ∃ x y z : ℤ, v = ((x : ℝ), (y : ℝ), (z : ℝ) + (x : ℝ) * (y : ℝ) / 2)}
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a + b ∉ S := by
  dsimp
  refine ⟨(1, 0, 0), (0, 1, 0), ⟨1, 0, 0, by norm_num⟩, ⟨0, 1, 0, by norm_num⟩, ?_⟩
  rintro ⟨x, y, z, he⟩
  have hxR : (x : ℝ) = 1 := by have h := congrArg Prod.fst he; simpa using h.symm
  have hyR : (y : ℝ) = 1 := by have h := congrArg (fun v : ℝ × ℝ × ℝ => v.2.1) he; simpa using h.symm
  have hz := congrArg (fun v : ℝ × ℝ × ℝ => v.2.2) he
  norm_num [hxR, hyR] at hz
  have hzR : (2 : ℝ) * (z : ℝ) = -1 := by linarith
  have hzZ : (2 : ℤ) * z = -1 := by exact_mod_cast hzR
  omega

end GMZP0
