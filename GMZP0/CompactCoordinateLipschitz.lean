import GMZP0.OriginalMetricBoundary
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Thickening

/-! Local Lipschitz coordinates give uniform comparison constants near the
actual compact cell. The intended metrics and local Lipschitz property
must still be derived from the original Malcev/Lie presentation. -/
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure
namespace GMZP0

/-- One pair of constants controls all nearby pairs with the first point
in a fixed compact set, including second points outside that set. -/
theorem compact_locally_lipschitz_uniform {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] [LocallyCompactSpace X]
    (f : X → Y) (hf : LocallyLipschitz f) (K : Set X) (hK : IsCompact K) :
    ∃ L r : ℝ, 0 ≤ L ∧ 0 < r ∧ ∀ x ∈ K, ∀ y : X, dist x y < r →
      dist (f x) (f y) ≤ L * dist x y := by
  obtain ⟨r, hr, hKr⟩ := hK.exists_isCompact_cthickening
  obtain ⟨L, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    hKr hf.locallyLipschitzOn
  refine ⟨L, r, L.coe_nonneg, hr, ?_⟩
  intro x hx y hxy
  exact hLip.dist_le_mul x (self_subset_cthickening K hx) y
    (mem_cthickening_of_dist_le y x r K hx (by simpa only [dist_comm] using hxy.le))

/-- Compact closure of the actual coordinate cell supplies uniform local
metric constants before every cell point and every nearby group point. -/
theorem coordinate_cell_uniform_local_metric {G : Type*} [PseudoMetricSpace G]
    {m : ℕ} (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ)
    (hlocal : LocallyLipschitz coord) :
    ∃ L r : ℝ, 0 ≤ L ∧ 0 < r ∧ ∀ g ∈ coordinateHalfOpenCell coord a,
      ∀ v : G, dist g v < r → dist (coord g) (coord v) ≤ L * dist g v := by
  let : LocallyCompactSpace G := coord.isOpenEmbedding.locallyCompactSpace
  obtain ⟨L, r, hL, hr, hbound⟩ := compact_locally_lipschitz_uniform coord hlocal
    (closure (coordinateHalfOpenCell coord a)) (coordinate_half_open_cell_compact_closure coord a)
  exact ⟨L, r, hL, hr, fun g hg v hgv => hbound g (subset_closure hg) v hgv⟩

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {m : ℕ}
  (Gamma : Subgroup G) [DiscreteTopology Gamma] [PseudoMetricSpace (G ⧸ Gamma)]

local instance compactTubeMetricTopology : TopologicalSpace (G ⧸ Gamma) :=
  (inferInstance : PseudoMetricSpace (G ⧸ Gamma)).toUniformSpace.toTopologicalSpace

variable [BorelSpace (G ⧸ Gamma)]

/-- The tube constant is chosen before every specified invariant probability
and every positive scale. Local comparison constants are constructed on
the actual compact cell; the literal metric and local regularity remain inputs. -/
theorem original_quotient_face_tube_linear_of_locallyLipschitz
    (coord : G ≃ₜ (Fin m → ℝ)) (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hgroup : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (a : Fin m → ℝ)
    (hdist : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h)
    (hlocal : LocallyLipschitz coord) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ mu : Measure (G ⧸ Gamma), IsProbabilityMeasure mu →
      SMulInvariantMeasure G (G ⧸ Gamma) mu → ∀ t : ℝ, 0 < t →
      (mu (boundaryTube (originalCellFaceImage Gamma coord a) t)).toReal ≤ C * t := by
  obtain ⟨L, r, hL, hr, hmetric⟩ := coordinate_cell_uniform_local_metric coord a hlocal
  refine ⟨2 * (m : ℝ) * L + r⁻¹, by positivity, ?_⟩
  intro mu hprob hinv
  let := hprob
  let := hinv
  exact original_quotient_face_tube_linear_bound Gamma coord q hgroup hlow hint hcover
    a hdist L r hL hr hmetric mu

end GMZP0
