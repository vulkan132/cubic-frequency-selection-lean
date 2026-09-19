import GMZP0.QuotientBoundaryTube

/-! The original one-sided coset infimum is a quotient distance when
every actual right lattice translation is an isometry. No normality,
commutation, or attained nearest representative is assumed. -/
noncomputable section
open Set Metric
namespace GMZP0
variable {G : Type*} [Group G] (Gamma : Subgroup G)

/-- Right lattice translation permutes the complete original right coset. -/
theorem original_coset_range_right_translate (h : G) (a : Gamma) :
    (fun x : G => x * a) '' Set.range (fun gamma : Gamma => h * gamma) =
      Set.range (fun gamma : Gamma => h * gamma) := by
  ext x
  constructor
  · rintro ⟨y, ⟨gamma, rfl⟩, rfl⟩
    exact ⟨gamma * a, by simp [mul_assoc]⟩
  · rintro ⟨gamma, rfl⟩
    exact ⟨h * (gamma * a⁻¹ : Gamma), ⟨gamma * a⁻¹, rfl⟩, by simp [mul_assoc]⟩

/-- Changing the original coset representative permutes its actual lattice points. -/
theorem original_coset_range_representative (h : G) (a : Gamma) :
    Set.range (fun gamma : Gamma => (h * a) * gamma) =
      Set.range (fun gamma : Gamma => h * gamma) := by
  ext x
  constructor
  · rintro ⟨gamma, rfl⟩
    exact ⟨a * gamma, by simp [mul_assoc]⟩
  · rintro ⟨gamma, rfl⟩
    exact ⟨a⁻¹ * gamma, by simp [mul_assoc]⟩

variable [PseudoMetricSpace G]

/-- Isometric right lattice action makes the first representative irrelevant. -/
theorem original_coset_infDist_first_translate
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a)) (g h : G) (a : Gamma) :
    originalCosetInfDist Gamma (g * a) h = originalCosetInfDist Gamma g h := by
  unfold originalCosetInfDist
  have he := original_coset_range_right_translate Gamma h a
  calc
    infDist (g * a) (Set.range (fun gamma : Gamma => h * gamma)) =
        infDist (g * a) ((fun x : G => x * a) '' Set.range (fun gamma : Gamma => h * gamma)) :=
      congrArg (infDist (g * a)) he.symm
    _ = infDist g (Set.range (fun gamma : Gamma => h * gamma)) := infDist_image (hright a)

/-- The second representative is irrelevant by the exact original coset relation. -/
theorem original_coset_infDist_second_translate (g h : G) (a : Gamma) :
    originalCosetInfDist Gamma g (h * a) = originalCosetInfDist Gamma g h := by
  unfold originalCosetInfDist
  rw [original_coset_range_representative]

/-- The actual original coset contains its representative. -/
theorem original_coset_infDist_self (g : G) : originalCosetInfDist Gamma g g = 0 :=
  infDist_zero_of_mem ⟨(1 : Gamma), by simp⟩

/-- Symmetry uses the inverse of the actual lattice translate, preserving order. -/
theorem original_coset_infDist_symm
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a)) (g h : G) :
    originalCosetInfDist Gamma g h = originalCosetInfDist Gamma h g := by
  have hle (u v : G) : originalCosetInfDist Gamma u v ≤ originalCosetInfDist Gamma v u := by
    apply (le_infDist (Set.range_nonempty _)).mpr
    rintro z ⟨a, rfl⟩
    calc
      originalCosetInfDist Gamma u v ≤ dist u (v * (a⁻¹ : Gamma)) :=
        infDist_le_dist_of_mem ⟨a⁻¹, rfl⟩
      _ = dist (u * a) v := by
        simpa [mul_assoc] using ((hright a).dist_eq u (v * (a⁻¹ : Gamma))).symm
      _ = dist v (u * a) := dist_comm _ _
  exact le_antisymm (hle g h) (hle h g)

/-- The triangle bound follows from infimum inequalities and actual
right lattice invariance, without selecting minimizers. -/
theorem original_coset_infDist_triangle
    (hright : ∀ a : Gamma, Isometry (fun x : G => x * a)) (g h k : G) :
    originalCosetInfDist Gamma g k ≤ originalCosetInfDist Gamma g h + originalCosetInfDist Gamma h k := by
  have hle : originalCosetInfDist Gamma g k - originalCosetInfDist Gamma h k ≤
      originalCosetInfDist Gamma g h := by
    apply (le_infDist (Set.range_nonempty _)).mpr
    rintro z ⟨a, rfl⟩
    have hb := infDist_le_infDist_add_dist (x := g) (y := h * a)
      (s := Set.range (fun gamma : Gamma => k * gamma))
    change originalCosetInfDist Gamma g k ≤ originalCosetInfDist Gamma (h * a) k + dist g (h * a) at hb
    rw [original_coset_infDist_first_translate Gamma hright] at hb
    linarith
  linarith

variable [IsTopologicalGroup G]

/-- Closedness of the actual lattice gives closed original cosets. -/
theorem original_coset_range_closed (hclosed : IsClosed (Gamma : Set G)) (h : G) :
    IsClosed (Set.range (fun gamma : Gamma => h * gamma)) := by
  have he : Set.range (fun gamma : Gamma => h * gamma) = (fun g : G => h * g) '' (Gamma : Set G) := by
    ext x
    constructor
    · rintro ⟨gamma, rfl⟩
      exact ⟨gamma, gamma.property, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [he]
  exact (Homeomorph.mulLeft h).isClosedMap _ hclosed

/-- Zero original coset distance forces equality of actual cosets.
Closedness, rather than mere nonemptiness or discreteness as a set, is used. -/
theorem original_coset_infDist_zero_implies_eq (hclosed : IsClosed (Gamma : Set G)) (g h : G)
    (hzero : originalCosetInfDist Gamma g h = 0) :
    (QuotientGroup.mk g : G ⧸ Gamma) = QuotientGroup.mk h := by
  have hg := ((original_coset_range_closed Gamma hclosed h).mem_iff_infDist_zero
    (Set.range_nonempty _)).mpr hzero
  obtain ⟨gamma, rfl⟩ := hg
  exact QuotientGroup.mk_mul_of_mem h gamma.property

end GMZP0
