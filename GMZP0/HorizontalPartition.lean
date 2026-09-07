import GMZP0.VerticalStrips
import GMZP0.FiniteSelection

/-! A uniform finite horizontal partition with the original safe-window mass. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem horizontal_partition_cover (N M : ℕ) (hM : 0 < M) : N < M * (N / M + 1) := by
  have hd := Nat.mod_add_div N M
  have hr := Nat.mod_lt N hM
  rw [Nat.mul_add, Nat.mul_one]
  omega

def horizontalChunkIndex {N M : ℕ} (hM : 0 < M) (x : Fin N) : Fin M :=
  ⟨x.val / (N / M + 1), by
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos (N / M))).2
    exact x.isLt.trans (horizontal_partition_cover N M hM)⟩

def horizontalChunk (N M : ℕ) (hM : 0 < M) (j : Fin M) : Finset (Fin N) :=
  Finset.univ.filter fun x => horizontalChunkIndex hM x = j

def chunkWindow (N M : ℕ) (hM : 0 < M) (j : Fin M) : Finset (Base N) :=
  horizontalChunk N M hM j ×ˢ safeRows N (N / M)

theorem horizontalChunk_interval {N M : ℕ} (hM : 0 < M) (j : Fin M) (x : Fin N)
    (hx : x ∈ horizontalChunk N M hM j) :
    j.val * (N / M + 1) ≤ x.val ∧ x.val ≤ j.val * (N / M + 1) + N / M := by
  have hx' := congrArg Fin.val (Finset.mem_filter.mp hx).2
  change x.val / (N / M + 1) = j.val at hx'
  have hr := Nat.mod_lt x.val (Nat.succ_pos (N / M))
  simp only [Nat.succ_eq_add_one] at hr
  have hd : x.val % (N / M + 1) + j.val * (N / M + 1) = x.val := by
    simpa only [hx', Nat.mul_comm] using Nat.mod_add_div x.val (N / M + 1)
  omega

theorem mem_horizontalChunk_iff {N M : ℕ} (hM : 0 < M) (j : Fin M) (x : Fin N) :
    x ∈ horizontalChunk N M hM j ↔
      j.val * (N / M + 1) ≤ x.val ∧ x.val ≤ j.val * (N / M + 1) + N / M := by
  constructor
  · exact horizontalChunk_interval hM j x
  · intro hbounds
    have hu : x.val / (N / M + 1) < j.val + 1 := by
      apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos (N / M))).2
      calc
        x.val ≤ j.val * (N / M + 1) + N / M := hbounds.2
        _ < (j.val + 1) * (N / M + 1) := by nlinarith
    have hl : ¬ x.val / (N / M + 1) < j.val := by
      intro hlt
      have hbad := (Nat.div_lt_iff_lt_mul (Nat.succ_pos (N / M))).1 hlt
      simp only [Nat.succ_eq_add_one] at hbad
      omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change x.val / (N / M + 1) = j.val
    omega

theorem horizontalChunk_gap {N M : ℕ} (hM : 0 < M) (j : Fin M) (x x' : Fin N)
    (hx : x ∈ horizontalChunk N M hM j) (hx' : x' ∈ horizontalChunk N M hM j) :
    |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ) := by
  have hi := horizontalChunk_interval hM j x hx
  have hi' := horizontalChunk_interval hM j x' hx'
  apply abs_le.mpr
  constructor <;> omega

theorem chunkWindow_geometry {N M : ℕ} (hM : 0 < M) (j : Fin M) (z : Base N)
    (hz : z ∈ chunkWindow N M hM j) :
    z.1 ∈ horizontalChunk N M hM j ∧ SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2 := by
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
  exact ⟨hx, (mem_safeRows_iff N (N / M) z.2).1 hy⟩

/-- Summing over all chunks gives exactly the retained original mass, with no duplication. -/
theorem chunkWindow_mass_partition {N M : ℕ} (hM : 0 < M) (μ : Base N → ℝ) :
    (∑ j : Fin M, ∑ z ∈ chunkWindow N M hM j, μ z) =
      ∑ z ∈ safeBaseSet N (N / M), μ z := by
  simp only [chunkWindow, safeBaseSet, horizontalChunk, Finset.sum_product, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq]

theorem exists_mean_chunk {N M : ℕ} (hM : 0 < M) (μ : Base N → ℝ) :
    ∃ j : Fin M, (∑ z ∈ safeBaseSet N (N / M), μ z) / (M : ℝ) ≤
      ∑ z ∈ chunkWindow N M hM j, μ z := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have h := exists_ge_mean (fun j : Fin M => ∑ z ∈ chunkWindow N M hM j, μ z)
  simpa only [Fintype.card_fin, chunkWindow_mass_partition] using h

/-- The chosen horizontal window retains a fixed fraction of the actual original mass. -/
theorem exists_heavy_chunk {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (μ : Base N → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hμ : ∀ z, μ z ≤ (N : ℝ)⁻¹ ^ 3) (hmass : κ ≤ ∑ z, μ z)
    (hbudget : 6 * ((N / M : ℕ) : ℝ) / (N : ℝ) ≤ κ / 2) :
    ∃ j : Fin M, κ / (4 * (M : ℝ)) ≤ ∑ z ∈ chunkWindow N M hM j, μ z := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsafe := safe_original_mass_lower hN (N / M) μ κ hμ hmass
  have hret : κ / 4 ≤ ∑ z ∈ safeBaseSet N (N / M), μ z := by
    linarith only [hsafe, hbudget, hκ]
  obtain ⟨j, hj⟩ := exists_mean_chunk hM μ
  refine ⟨j, ?_⟩
  have heq : κ / (4 * (M : ℝ)) = (κ / 4) / (M : ℝ) := by field_simp
  rw [heq]
  exact (div_le_div_of_nonneg_right hret hMr.le).trans hj

end GMZP0
