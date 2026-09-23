import GMZP0.OriginalWeakBasis
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Exponential images in the original group. These are sets until
closure under multiplication has actually been proved. -/
noncomputable section
open scoped Manifold ContDiff
namespace GMZP0
variable {G sigma : Type*} [Group G] [TopologicalSpace G] [Fintype sigma]

/-- The actual exponential image, expressed using its global inverse. -/
def originalExponentialImage (logCoord : G ≃ (sigma → ℝ))
    (U : Submodule ℝ (sigma → ℝ)) : Set G := logCoord ⁻¹' (U : Set (sigma → ℝ))

/-- The proved rational coordinate arrays upgrade the very same global
equivalence to a homeomorphism on the original topology. -/
def originalLogHomeomorph (coord : G ≃ₜ (sigma → ℝ))
    (logCoord : G ≃ (sigma → ℝ)) (S T : sigma → MvPolynomial sigma ℚ)
    (hS : ∀ x i, coord (logCoord.symm x) i = MvPolynomial.aeval x (S i))
    (hT : ∀ a i, logCoord a i = MvPolynomial.aeval (coord a) (T i)) :
    G ≃ₜ (sigma → ℝ) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  have h := original_rational_equiv_smooth coord logCoord S T hS hT
  exact { logCoord with continuous_toFun := h.2.continuous, continuous_invFun := h.1.continuous }

/-- Restricting the original logarithm identifies the exponential image
with the actual subspace, with both inherited topologies. -/
def originalExponentialImageHomeomorph (logHomeo : G ≃ₜ (sigma → ℝ))
    (U : Submodule ℝ (sigma → ℝ)) :
    originalExponentialImage logHomeo.toEquiv U ≃ₜ U :=
  logHomeo.subtype (fun _ => Iff.rfl)

omit [Group G] in
/-- Every linear subspace has a closed actual exponential image. -/
theorem original_exponential_image_closed (logHomeo : G ≃ₜ (sigma → ℝ))
    (U : Submodule ℝ (sigma → ℝ)) :
    IsClosed (originalExponentialImage logHomeo.toEquiv U) :=
  U.closed_of_finiteDimensional.preimage logHomeo.continuous

omit [Group G] [Fintype sigma] in
/-- Every such image is contractible; this does not assert subgroup closure. -/
theorem original_exponential_image_contractible (logHomeo : G ≃ₜ (sigma → ℝ))
    (U : Submodule ℝ (sigma → ℝ)) :
    ContractibleSpace (originalExponentialImage logHomeo.toEquiv U) :=
  (originalExponentialImageHomeomorph logHomeo U).contractibleSpace

/-- Native exponential lines give the exact original inverse. -/
theorem original_weak_basis_exp_neg (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q) (v : sigma → ℝ) :
    logCoord.symm (-v) = (logCoord.symm v)⁻¹ := by
  have h := (hweak.native_subgroups v).1
  apply eq_inv_iff_mul_eq_one.mpr
  calc
    _ = logCoord.symm ((0 : ℝ) • v) := by simpa using (h.2.1 (-1) 1).symm
    _ = 1 := h.1

/-- Integer-time values are actual powers in the original group. -/
theorem original_weak_basis_exp_nsmul (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q) (v : sigma → ℝ) (n : ℕ) :
    logCoord.symm ((n : ℝ) • v) = (logCoord.symm v) ^ n := by
  have h := (hweak.native_subgroups v).1
  induction n with
  | zero => simpa using h.1
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, one_smul, ih, pow_succ] using h.2.1 (n : ℝ) 1

/-- Powers preserve the original logarithmic coordinates exactly. -/
theorem original_weak_basis_log_pow (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q) (g : G) (n : ℕ) :
    logCoord (g ^ n) = (n : ℝ) • logCoord g := by
  have h := original_weak_basis_exp_nsmul coord Gamma logCoord Q hweak (logCoord g) n
  simpa using (congrArg logCoord h).symm

/-- Exponential subspaces contain the identity, are inverse closed and
detect every positive power. Multiplicative closure is a separate obligation. -/
theorem original_exponential_image_power_properties (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (U : Submodule ℝ (sigma → ℝ)) :
    1 ∈ originalExponentialImage logCoord U ∧
      (∀ g ∈ originalExponentialImage logCoord U, g⁻¹ ∈ originalExponentialImage logCoord U) ∧
      ∀ g (n : ℕ), 0 < n →
        (g ^ n ∈ originalExponentialImage logCoord U ↔ g ∈ originalExponentialImage logCoord U) := by
  have hzero : logCoord (1 : G) = 0 := by
    have h := (hweak.native_subgroups (0 : sigma → ℝ)).1.1
    simpa using (congrArg logCoord h).symm
  refine ⟨?_, ?_, ?_⟩
  · change logCoord 1 ∈ U
    rw [hzero]
    exact U.zero_mem
  · intro g hg
    change logCoord g⁻¹ ∈ U
    have h := original_weak_basis_exp_neg coord Gamma logCoord Q hweak (logCoord g)
    have hi : logCoord g⁻¹ = -logCoord g := by
      simpa using (congrArg logCoord h).symm
    rw [hi]
    exact U.neg_mem hg
  · intro g n hn
    change logCoord (g ^ n) ∈ U ↔ logCoord g ∈ U
    rw [original_weak_basis_log_pow coord Gamma logCoord Q hweak]
    exact U.smul_mem_iff (by exact_mod_cast (ne_of_gt hn))

end GMZP0
