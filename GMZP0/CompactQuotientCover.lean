import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Compactness.LocallyCompact

/-! A compact quotient by right multiplication in a locally compact group has a compact
covering set in the original group. No global continuous section is assumed. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Compactness of G/Gamma supplies finitely many compact pieces meeting every coset g * Gamma. -/
theorem compact_quotient_right_cover [LocallyCompactSpace G] (Gamma : Subgroup G)
    [CompactSpace (G ⧸ Gamma)] :
    ∃ K : Set G, IsCompact K ∧ ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ K := by
  classical
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have h1 : (1 : G) ∈ interior C := mem_interior_iff_mem_nhds.mpr hC1
  let pi : G → G ⧸ Gamma := QuotientGroup.mk
  let U (g : G) : Set (G ⧸ Gamma) := pi '' ((fun u : G => g * u) '' interior C)
  have hopen (g : G) : IsOpen (U g) :=
    QuotientGroup.isOpenMap_coe _ ((Homeomorph.mulLeft g).isOpenMap _ isOpen_interior)
  have hcover : (Set.univ : Set (G ⧸ Gamma)) ⊆ ⋃ g : G, U g := by
    intro x _
    induction x using Quotient.inductionOn with
    | h g =>
      exact Set.mem_iUnion.mpr ⟨g, ⟨g, ⟨1, h1, mul_one g⟩, rfl⟩⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨⋃ g ∈ S, (fun u : G => g * u) '' C,
    S.isCompact_biUnion (fun g _ => hC.image (continuous_const.mul continuous_id)), ?_⟩
  intro g
  have hg := hS (Set.mem_univ (pi g))
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hg
  obtain ⟨haS, hga⟩ := Set.mem_iUnion.mp ha
  obtain ⟨v, ⟨u, hu, rfl⟩, hv⟩ := hga
  have hgamma : g⁻¹ * (a * u) ∈ Gamma := QuotientGroup.eq.mp hv.symm
  refine ⟨⟨g⁻¹ * (a * u), hgamma⟩, ?_⟩
  have he : g * (⟨g⁻¹ * (a * u), hgamma⟩ : Gamma) = a * u := by simp
  rw [he]
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨haS, ⟨u, interior_subset hu, rfl⟩⟩⟩

end GMZP0
