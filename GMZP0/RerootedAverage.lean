import GMZP0.RerootedBounds
import GMZP0.PositiveLagStatistic

/-! The weighted modulus average over all finite original x,x',y,t indices. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem sum_original_integer_labels (N : ℕ) (F : ℤ → ℝ) :
    (∑ r : Fin N, F (label r)) = ∑ i ∈ Finset.Icc 1 (N : ℤ), F i := by
  classical
  apply Finset.sum_bij (fun r _ => (label r : ℤ))
  · intro r _
    exact Finset.mem_Icc.mpr (integer_label_bounds r)
  · intro r hr s hs he
    apply Fin.ext
    simp only [label, Nat.cast_add, Nat.cast_one] at he
    omega
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    exact ⟨oneBasedIndex N i hi'.1 hi'.2, Finset.mem_univ _, oneBasedIndex_label N i hi'.1 hi'.2⟩
  · intro r _
    rfl

theorem sum_rerootLabels (N : ℕ) (h : ℤ) (F : ℤ → ℝ) :
    (∑ t ∈ rerootLabels N h, F t) =
      ∑ t : Fin N, if 1 ≤ (label t : ℤ) + h ∧ (label t : ℤ) + h ≤ N then F (label t) else 0 := by
  rw [rerootLabels, Finset.sum_filter]
  exact (sum_original_integer_labels N (fun t => if 1 ≤ t + h ∧ t + h ≤ N then F t else 0)).symm

def finiteRerootedNormAverage (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  (∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ∑ y : Fin (N ^ 2), ∑ t : Fin N,
      if 1 ≤ (label t : ℤ) + horizontalGap x x' ∧ (label t : ℤ) + horizontalGap x x' ≤ N then
        σ (x, y) * ‖rerootedLagB N p σ lam x x' y (label t)‖ else 0
    else 0) / (N : ℝ) ^ 5

theorem finiteRerootedNormAverage_eq (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    finiteRerootedNormAverage N p X σ lam = rerootedNormSum N p X σ lam / (N : ℝ) ^ 5 := by
  unfold finiteRerootedNormAverage rerootedNormSum
  simp_rw [sum_rerootLabels]

/-- Same uniform constants, same original response, now a positive weighted modulus average. -/
theorem uniform_positive_rerooted_average (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c ζ : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < ζ ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency)
        (lam : Base N → ℂ) (μ : Base N → ℝ), Admissible N κ η f θ lam μ →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ a : ℕ,
          D = X ×ˢ safeRows N (N / M) ∧
          (∀ x : Fin N, x ∈ X ↔ a ≤ x.val ∧ x.val ≤ a + N / M) ∧
          c ≤ ∑ z ∈ D, μ z ∧
          (∀ x ∈ X, ∀ x' ∈ X, |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ)) ∧
          (∀ z ∈ D, SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2) ∧
          η * (∑ z ∈ D, μ z) ≤ ‖weightedOriginalResponse N f θ (originalScaledWeight N μ D) lam‖ ∧
          2 * ζ ≤ finiteRerootedNormAverage N θ X (originalScaledWeight N μ D) lam ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, ζ, N₀, hM, hc, hζ, hN₀, hwindow⟩ := uniform_positive_safe_lag_statistic κ η hκ hη hη1
  refine ⟨M, c, ζ, N₀, hM, hc, hζ, hN₀, ?_⟩
  intro N hNth f θ lam μ hdata
  have hN : 0 < N := hN₀.trans_le hNth
  obtain ⟨X, D, a, hDX, hinterval, hmass, hgap, hsafe, hR, hS, hresponse⟩ :=
    hwindow N hNth f θ lam μ hdata
  refine ⟨X, D, a, hDX, hinterval, hmass, hgap, hsafe, hR, ?_, hresponse⟩
  rw [finiteRerootedNormAverage_eq]
  exact hS.trans (lagSigned_le_rerootedNormSum hN θ X (originalScaledWeight N μ D) lam
    (fun z => (originalScaledWeight_bounds hN μ D hdata.2.2.1 z).1) hdata.2.1)

end GMZP0
