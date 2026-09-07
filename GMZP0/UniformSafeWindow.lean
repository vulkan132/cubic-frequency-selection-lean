import GMZP0.HorizontalPartition

/-! The safe window is selected with constants fixed before N and all original data. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def windowModulus (κ : ℝ) : ℕ := Nat.ceil (64 / κ)

def safeWindowMass (κ : ℝ) : ℝ := κ / (4 * (windowModulus κ : ℝ))

theorem windowModulus_pos (κ : ℝ) (hκ : 0 < κ) : 0 < windowModulus κ := by
  have hp : (0 : ℝ) < 64 / κ := div_pos (by norm_num) hκ
  have hc := Nat.le_ceil (64 / κ)
  have hm : (0 : ℝ) < windowModulus κ := hp.trans_le hc
  exact_mod_cast hm

theorem safeWindowMass_pos (κ : ℝ) (hκ : 0 < κ) : 0 < safeWindowMass κ := by
  have hm : (0 : ℝ) < windowModulus κ := by exact_mod_cast windowModulus_pos κ hκ
  exact div_pos hκ (mul_pos (by norm_num) hm)

/-- The manuscript's strip budget with M=ceil(64/kappa), valid at every positive scale. -/
theorem window_boundary_budget {N : ℕ} (hN : 0 < N) (κ : ℝ) (hκ : 0 < κ) :
    6 * ((N / windowModulus κ : ℕ) : ℝ) / (N : ℝ) ≤ κ / 8 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : (64 : ℝ) ≤ (windowModulus κ : ℝ) * κ :=
    (div_le_iff₀ hκ).1 (Nat.le_ceil (64 / κ))
  have hd : ((N / windowModulus κ : ℕ) : ℝ) * (windowModulus κ : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (windowModulus κ)
  have hprod1 := mul_le_mul_of_nonneg_left hd hκ.le
  have hprod2 := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg (N / windowModulus κ) :
    (0 : ℝ) ≤ (N / windowModulus κ : ℕ))
  apply (div_le_iff₀ hNr).2
  nlinarith [Nat.cast_nonneg (N / windowModulus κ) (α := ℝ)]

theorem exists_original_safe_chunk {N : ℕ} (hN : 0 < N) (κ : ℝ) (hκ : 0 < κ)
    (μ : Base N → ℝ) (hμ : ∀ z, μ z ≤ (N : ℝ)⁻¹ ^ 3) (hmass : κ ≤ ∑ z, μ z) :
    ∃ j : Fin (windowModulus κ), safeWindowMass κ ≤
      ∑ z ∈ chunkWindow N (windowModulus κ) (windowModulus_pos κ hκ) j, μ z := by
  have hbudget := window_boundary_budget hN κ hκ
  have hhalf : 6 * ((N / windowModulus κ : ℕ) : ℝ) / (N : ℝ) ≤ κ / 2 := by
    linarith only [hbudget, hκ]
  exact exists_heavy_chunk hN (windowModulus_pos κ hκ) μ κ hκ hμ hmass hhalf

/-- The uniform constants precede the scale, weight and selected interval. -/
theorem uniform_safe_window (κ : ℝ) (hκ : 0 < κ) :
    ∃ M : ℕ, ∃ c : ℝ, 0 < M ∧ 0 < c ∧ c = κ / (4 * (M : ℝ)) ∧
      ∀ N : ℕ, 0 < N → ∀ μ : Base N → ℝ,
        (∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) → κ ≤ ∑ z, μ z →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ a : ℕ,
          D = X ×ˢ safeRows N (N / M) ∧
          (∀ x : Fin N, x ∈ X ↔ a ≤ x.val ∧ x.val ≤ a + N / M) ∧
          c ≤ ∑ z ∈ D, μ z ∧
          (∀ x ∈ X, ∀ x' ∈ X, |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ)) ∧
          (∀ z ∈ D, SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2) := by
  refine ⟨windowModulus κ, safeWindowMass κ, windowModulus_pos κ hκ, safeWindowMass_pos κ hκ,
    rfl, ?_⟩
  intro N hN μ hμ hmass
  obtain ⟨j, hj⟩ := exists_original_safe_chunk hN κ hκ μ (fun z => (hμ z).2) hmass
  refine ⟨horizontalChunk N (windowModulus κ) (windowModulus_pos κ hκ) j,
    chunkWindow N (windowModulus κ) (windowModulus_pos κ hκ) j,
    j.val * (N / windowModulus κ + 1), rfl, ?_, hj, ?_, ?_⟩
  · exact fun x => mem_horizontalChunk_iff (windowModulus_pos κ hκ) j x
  · exact fun x hx x' hx' => horizontalChunk_gap (windowModulus_pos κ hκ) j x x' hx hx'
  · exact fun z hz => (chunkWindow_geometry (windowModulus_pos κ hκ) j z hz).2

/-- Every label target between two fibers of a selected chunk has an actual original base index. -/
theorem safe_chunk_target_exists {N M : ℕ} (hM : 0 < M) (j : Fin M)
    (z : Base N) (hz : z ∈ chunkWindow N M hM j) (x' : Fin N)
    (hx' : x' ∈ horizontalChunk N M hM j) (r : Fin N) :
    ∃ w : Base N, w.1 = x' ∧ basePoint w =
      ((x'.val : ℤ) + 1, (basePoint z).2 +
        2 * (((x'.val : ℤ) + 1) - (basePoint z).1) * (label r : ℤ) -
          (((x'.val : ℤ) + 1) - (basePoint z).1) ^ 2) := by
  have hg := chunkWindow_geometry hM j z hz
  have hh : |((x'.val : ℤ) + 1) - (basePoint z).1| ≤ (N / M : ℕ) := by
    simpa only [basePoint, add_sub_add_right_eq_sub] using horizontalChunk_gap hM j z.1 x' hg.1 hx'
  have hHN : ((N / M : ℕ) : ℤ) ≤ N := by exact_mod_cast Nat.div_le_self N M
  have hrN : (label r : ℤ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt r.isLt
  exact safe_original_target_exists x' (N / M : ℕ) (basePoint z).2
    (((x'.val : ℤ) + 1) - (basePoint z).1) (label r) hg.2
    (Nat.cast_nonneg _) hHN hh (Nat.cast_nonneg _) hrN

end GMZP0
