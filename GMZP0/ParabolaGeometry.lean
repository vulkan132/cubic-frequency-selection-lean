import GMZP0.FiniteOperator

/-! Exact endpoint collisions for the original finite parabola. -/

noncomputable section
namespace GMZP0

theorem inputPoint_injective {N : ℕ} : Function.Injective (@inputPoint N) := by
  intro u v h
  have hx := congrArg (fun w : ℤ × ℤ => w.1) h
  have hy := congrArg (fun w : ℤ × ℤ => w.2) h
  apply Prod.ext <;> apply Fin.ext <;> simp only [inputPoint] at hx hy <;> omega

theorem endpointIndex_label_injective {N : ℕ} (z : Base N) :
    Function.Injective (endpointIndex z) := by
  intro r s h
  have hx := congrArg (fun u : InputBox N => u.1.val) h
  simp only [endpointIndex] at hx
  apply Fin.ext
  omega

theorem endpointIndex_base_injective {N : ℕ} (r : Fin N) :
    Function.Injective (fun z : Base N => endpointIndex z r) := by
  intro z w h
  have hx := congrArg (fun u : InputBox N => u.1.val) h
  have hy := congrArg (fun u : InputBox N => u.2.val) h
  simp only [endpointIndex] at hx hy
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- On one horizontal fiber, a shared endpoint forces both labels and base points to agree. -/
theorem endpointIndex_same_horizontal {N : ℕ} (z w : Base N) (r s : Fin N)
    (hx : z.1 = w.1) (he : endpointIndex z r = endpointIndex w s) :
    z = w ∧ r = s := by
  have hxv := congrArg Fin.val hx
  have he1 := congrArg (fun u : InputBox N => u.1.val) he
  simp only [endpointIndex] at he1
  have hrs : r = s := Fin.ext (by omega)
  subst s
  exact ⟨endpointIndex_base_injective r he, rfl⟩

/-- Integer collision coordinates, with signed horizontal displacement h = x' - x. -/
theorem integer_parabola_collision (x y x' y' r s : ℤ) :
    (x + r = x' + s ∧ y + r ^ 2 = y' + s ^ 2) ↔
      (s = r - (x' - x) ∧ y' = y + 2 * (x' - x) * r - (x' - x) ^ 2) := by
  constructor
  · rintro ⟨hx, hy⟩
    have hs : s = r - (x' - x) := by omega
    refine ⟨hs, ?_⟩
    rw [hs] at hy
    nlinarith only [hy]
  · rintro ⟨hs, hy⟩
    subst s
    subst y'
    constructor <;> ring

/-- Two collisions with labels r+k and r have vertical displacement 2hk. -/
theorem collision_lag_displacement (y h r k : ℤ) :
    (y + 2 * h * (r + k) - h ^ 2) - (y + 2 * h * r - h ^ 2) = 2 * h * k := by
  ring

end GMZP0
