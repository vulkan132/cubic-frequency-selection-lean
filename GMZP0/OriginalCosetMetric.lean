import GMZP0.CosetDistanceAlgebra
import GMZP0.CompactCosetLifts

/-! Construct the actual metric on original cosets under isometric right
lattice translations and closedness of the original lattice. A compact
original cover identifies its topology, without normality or minimizers. -/
noncomputable section
open Set Metric
namespace GMZP0
variable {G : Type*} [Group G] [PseudoMetricSpace G] (Gamma : Subgroup G)

/-- The one-sided original infimum respects both exact coset relations. -/
theorem original_coset_infDist_respects
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a))
    {g g' h h' : G} (hg : QuotientGroup.leftRel Gamma g g')
    (hh : QuotientGroup.leftRel Gamma h h') :
    originalCosetInfDist Gamma g h = originalCosetInfDist Gamma g' h' := by
  let a : Gamma := ⟨g⁻¹ * g', QuotientGroup.leftRel_apply.mp hg⟩
  let b : Gamma := ⟨h⁻¹ * h', QuotientGroup.leftRel_apply.mp hh⟩
  have ha : g * a = g' := by simp [a]
  have hb : h * b = h' := by simp [b]
  rw [← ha, ← hb, original_coset_infDist_first_translate Gamma hright,
    original_coset_infDist_second_translate]

/-- Distance on the original quotient, using every actual lattice translate. -/
def originalQuotientDistance
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a)) :
    (G ⧸ Gamma) → (G ⧸ Gamma) → ℝ :=
  Quotient.lift₂ (originalCosetInfDist Gamma)
    (fun _ _ _ _ hg hh => original_coset_infDist_respects Gamma hright hg hh)

/-- The constructed function has the literal original infimum formula. -/
theorem original_quotient_distance_mk
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a)) (g h : G) :
    originalQuotientDistance Gamma hright (QuotientGroup.mk g) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h := rfl

variable [IsTopologicalGroup G]

/-- A genuine metric on the actual coset type; the lattice need not be normal. -/
@[instance_reducible] def originalRawCosetMetric (hclosed : IsClosed (Gamma : Set G))
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a)) : MetricSpace (G ⧸ Gamma) where
  dist := originalQuotientDistance Gamma hright
  dist_self x := by
    induction x using Quotient.inductionOn with | h g =>
      exact original_coset_infDist_self Gamma g
  dist_comm x y := by
    induction x using Quotient.inductionOn with | h g =>
      induction y using Quotient.inductionOn with | h h =>
        exact original_coset_infDist_symm Gamma hright g h
  dist_triangle x y z := by
    induction x using Quotient.inductionOn with | h g =>
      induction y using Quotient.inductionOn with | h h =>
        induction z using Quotient.inductionOn with | h k =>
          exact original_coset_infDist_triangle Gamma hright g h k
  eq_of_dist_eq_zero := by
    intro x y
    induction x using Quotient.inductionOn with | h g =>
      induction y using Quotient.inductionOn with | h h =>
        exact original_coset_infDist_zero_implies_eq Gamma hclosed g h

/-- Exact topology agreement follows from the original compact cover. -/
theorem original_raw_coset_metric_topology
    (hclosed : IsClosed (Gamma : Set G))
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a))
    (C : Set G) (hC : IsCompact C)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ C) :
    (originalRawCosetMetric Gamma hclosed hright).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Gamma := by
  let := originalRawCosetMetric Gamma hclosed hright
  exact coset_metric_topology_eq_coinduced Gamma C hC hcover (fun _ _ => rfl)

/-- The constructed metric retains the original quotient topology definitionally. -/
@[instance_reducible] def originalCosetMetric (hclosed : IsClosed (Gamma : Set G))
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a))
    (C : Set G) (hC : IsCompact C)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ C) : MetricSpace (G ⧸ Gamma) :=
  @MetricSpace.replaceTopology (G ⧸ Gamma) (QuotientGroup.instTopologicalSpace Gamma)
    (originalRawCosetMetric Gamma hclosed hright)
    (original_raw_coset_metric_topology Gamma hclosed hright C hC hcover).symm

/-- The compatible metric still uses the unchanged actual infimum. -/
theorem original_coset_metric_formula (hclosed : IsClosed (Gamma : Set G))
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a))
    (C : Set G) (hC : IsCompact C)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ C) (g h : G) :
    @dist (G ⧸ Gamma) (originalCosetMetric Gamma hclosed hright C hC hcover).toDist
      (QuotientGroup.mk g) (QuotientGroup.mk h) = originalCosetInfDist Gamma g h := rfl

/-- The compatible metric has exactly the original quotient topology. -/
theorem original_coset_metric_topology (hclosed : IsClosed (Gamma : Set G))
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a))
    (C : Set G) (hC : IsCompact C)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ C) :
    (originalCosetMetric Gamma hclosed hright C hC hcover).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Gamma := rfl

/-- The actual quotient map is 1-Lipschitz for this constructed metric. -/
theorem original_coset_metric_mk_lipschitz (hclosed : IsClosed (Gamma : Set G))
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a))
    (C : Set G) (hC : IsCompact C)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ C) :
    letI := originalCosetMetric Gamma hclosed hright C hC hcover
    LipschitzWith 1 (QuotientGroup.mk : G → G ⧸ Gamma) := by
  let := originalCosetMetric Gamma hclosed hright C hC hcover
  exact quotient_mk_lipschitz_of_coset_formula Gamma (fun _ _ => rfl)

end GMZP0
