import GMZP0.WeylLargeCorrelations

/-! A bounded nonzero denominator from two nearby affine circle returns. -/

noncomputable section
namespace GMZP0

theorem close_integer_pair {N Q : ℕ} (hQ : 0 < Q) (s : Finset ℤ)
    (hs : s ⊆ Finset.Icc (-(N : ℤ)) N) (hcard : 2 * N / Q + 1 < s.card) :
    ∃ u ∈ s, ∃ v ∈ s, u < v ∧ v - u < Q := by
  let bucket (h : ℤ) : ℕ := (h + N).toNat / Q
  have hm : ∀ h ∈ s, bucket h ∈ Finset.range (2 * N / Q + 1) := by
    intro h hh
    have hi := Finset.mem_Icc.mp (hs hh)
    have hb : (h + (N : ℤ)).toNat ≤ 2 * N := by omega
    have hd := Nat.div_le_div_right (c := Q) hb
    simp only [bucket, Finset.mem_range]
    omega
  have hc : (Finset.range (2 * N / Q + 1)).card < s.card := by simpa using hcard
  obtain ⟨u, hu, v, hv, huv, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hm
  have huI := Finset.mem_Icc.mp (hs hu)
  have hvI := Finset.mem_Icc.mp (hs hv)
  have hmu := Nat.mod_lt (u + (N : ℤ)).toNat hQ
  have hmv := Nat.mod_lt (v + (N : ℤ)).toNat hQ
  have heu := Nat.mod_add_div (u + (N : ℤ)).toNat Q
  have hev := Nat.mod_add_div (v + (N : ℤ)).toNat Q
  dsimp [bucket] at he
  rw [he] at heu
  rcases lt_or_gt_of_ne huv with huv' | hvu'
  · exact ⟨u, hu, v, hv, huv', by omega⟩
  · exact ⟨v, hv, u, hu, hvu', by omega⟩

/-- The intercept cancels only by subtracting two actual retained returns. -/
theorem affine_return_small_multiple {N Q : ℕ} (hQ : 0 < Q) (s : Finset ℤ)
    (hs : s ⊆ Finset.Icc (-(N : ℤ)) N) (hcard : 2 * N / Q + 1 < s.card)
    (a b : Frequency) {ε : ℝ} (hreturn : ∀ h ∈ s, ‖h • a + b‖ ≤ ε) :
    ∃ q : ℤ, 0 < q ∧ q < Q ∧ ‖q • a‖ ≤ 2 * ε := by
  obtain ⟨u, hu, v, hv, huv, hgap⟩ := close_integer_pair hQ s hs hcard
  refine ⟨v - u, by omega, hgap, ?_⟩
  have he : (v - u) • a = (v • a + b) - (u • a + b) := by
    rw [sub_zsmul]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [hreturn u hu, hreturn v hv])

end GMZP0
