import OrderedPartitions.ReciprocalEdgeRowLimit
import Mathlib.Data.Nat.Factorial.BigOperators

/-! First-order control of the shifted binomial coefficient. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open Filter Finset
open scoped Topology

/-- Sum of the shifts in the falling factorial. -/
def shiftCost (h m : ℕ) : ℝ := ∑ i ∈ range m, ((h+i:ℕ):ℝ)

theorem shiftCost_formula (h m : ℕ) :
    shiftCost h m = (m:ℝ)*h+(m:ℝ)*((m:ℝ)-1)/2 := by
  induction m with
  | zero => simp [shiftCost]
  | succ m ih =>
    rw [shiftCost, sum_range_succ, ← shiftCost, ih]
    push_cast
    ring

theorem shiftCost_nonneg (h m : ℕ) : 0 ≤ shiftCost h m :=
  sum_nonneg (fun i _ ↦ Nat.cast_nonneg (α := ℝ) (h+i))

private theorem shiftCost_succ (h m : ℕ) : shiftCost h (m+1) = shiftCost h m+((h:ℝ)+m) := by
  simp only [shiftCost, sum_range_succ, Nat.cast_add]

/-- Shifted falling factorial normalized by the unshifted power. -/
def shiftedFalling (h m d : ℕ) : ℝ := ((d-h).descFactorial m : ℝ)/(d:ℝ)^m

private theorem shiftedFalling_succ (h m d : ℕ) :
    shiftedFalling h (m+1) d =
      shiftedFalling h m d * ((d-h-m:ℕ):ℝ)/(d:ℝ) := by
  unfold shiftedFalling
  rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
  ring

theorem shiftedFalling_bounds (h m : ℕ) {d : ℕ} (hd : 0 < d) :
    0 ≤ shiftedFalling h m d ∧ shiftedFalling h m d ≤ 1 ∧
      (d:ℝ)*(1-shiftedFalling h m d) ≤ shiftCost h m := by
  have dpos : (0:ℝ) < d := by exact_mod_cast hd
  induction m with
  | zero =>
    simp [shiftedFalling, shiftCost]
  | succ m ih =>
    let y : ℝ := ((d-h-m:ℕ):ℝ)
    let F := shiftedFalling h m d
    have yp : 0 ≤ y := by dsimp [y]; positivity
    have yb : y ≤ d := by
      dsimp [y]
      exact_mod_cast (by omega : d-h-m ≤ d)
    have sc : (d:ℝ)-y ≤ (h:ℝ)+m := by
      have t : d ≤ d-h-m+(h+m) := by omega
      have t' : (d:ℝ) ≤ ((d-h-m+(h+m):ℕ):ℝ) := by exact_mod_cast t
      push_cast at t'
      dsimp [y]
      linarith only [t']
    rw [shiftedFalling_succ h m d]
    change 0 ≤ F*y/d ∧ F*y/d ≤ 1 ∧ (d:ℝ)*(1-F*y/d) ≤ shiftCost h (m+1)
    refine ⟨div_nonneg (mul_nonneg ih.1 yp) dpos.le, (div_le_one dpos).mpr ?_, ?_⟩
    · exact (mul_le_of_le_one_left yp ih.2.1).trans yb
    · have exact_change : (d:ℝ)*(1-F*y/d) = (d:ℝ)*(1-F)+F*((d:ℝ)-y) := by
        field_simp [dpos.ne']
        ring
      rw [exact_change, shiftCost_succ]
      have lost : F*((d:ℝ)-y) ≤ (h:ℝ)+m :=
        (mul_le_of_le_one_left (sub_nonneg.mpr yb) ih.2.1).trans sc
      exact add_le_add ih.2.2 lost

private theorem ratio_step_atTop (h m : ℕ) :
    (fun d : ℕ ↦ shiftedFalling h (m+1) d) =ᶠ[atTop]
      fun d ↦ shiftedFalling h m d * (1-((h:ℝ)+m)*(d:ℝ)⁻¹) := by
  filter_upwards [eventually_ge_atTop (h+m+1)] with d hd
  have dp : 0 < d := by omega
  have dR : (d:ℝ) ≠ 0 := by exact_mod_cast dp.ne'
  have hs : h ≤ d := by omega
  have hsm : m ≤ d-h := by omega
  rw [shiftedFalling_succ h m d, Nat.cast_sub hsm, Nat.cast_sub hs]
  field_simp [dR]
  ring

theorem shiftedFalling_limit (h m : ℕ) :
    Tendsto (shiftedFalling h m) atTop (𝓝 1) := by
  induction m with
  | zero =>
    change Tendsto (fun d ↦ shiftedFalling h 0 d) atTop (𝓝 1)
    simp [shiftedFalling]
  | succ m ih =>
    have dec := (Kernel.cutoff_inv_limit (J := id) tendsto_id).const_mul ((h:ℝ)+m)
    have v := (tendsto_const_nhds (x := (1:ℝ))).sub dec
    simp only [id_eq, mul_zero, sub_zero] at v
    simpa only [mul_one] using (ih.mul v).congr' (ratio_step_atTop h m).symm

/-- The first-order term of a shifted falling factorial. -/
theorem shiftedFalling_correction (h m : ℕ) :
    Tendsto (fun d : ℕ ↦ (d:ℝ)*(shiftedFalling h m d-1)) atTop
      (𝓝 (-shiftCost h m)) := by
  induction m with
  | zero => simp [shiftedFalling, shiftCost]
  | succ m ih =>
    have bound := ih.sub ((shiftedFalling_limit h m).mul_const ((h:ℝ)+m))
    simp only [one_mul] at bound
    rw [show -shiftCost h m-((h:ℝ)+m) = -shiftCost h (m+1) by
      rw [shiftCost_succ]
      ring] at bound
    apply bound.congr'
    filter_upwards [ratio_step_atTop h m, eventually_ge_atTop 1] with d step hd
    have dR : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    change (d:ℝ)*(shiftedFalling h m d-1)-shiftedFalling h m d*((h:ℝ)+m) =
      (d:ℝ)*(shiftedFalling h (m+1) d-1)
    rw [show shiftedFalling h (m+1) d = _ from step]
    field_simp [dR]
    ring

theorem shifted_choose_ratio (h m d : ℕ) :
    ((d-h).choose m : ℝ)/(d:ℝ)^m = shiftedFalling h m d/(m.factorial:ℝ) := by
  rw [shiftedFalling, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

theorem shiftedChoose_limit (h m : ℕ) :
    Tendsto (fun d : ℕ ↦ ((d-h).choose m : ℝ)/(d:ℝ)^m) atTop
      (𝓝 (1/(m.factorial:ℝ))) := by
  simpa only [shifted_choose_ratio] using (shiftedFalling_limit h m).div_const (m.factorial:ℝ)

theorem shiftedChoose_correction (h m : ℕ) :
    Tendsto (fun d : ℕ ↦ (d:ℝ)*(((d-h).choose m : ℝ)/(d:ℝ)^m-1/(m.factorial:ℝ)))
      atTop (𝓝 (-shiftCost h m/(m.factorial:ℝ))) := by
  have lim := (shiftedFalling_correction h m).div_const (m.factorial:ℝ)
  apply lim.congr'
  refine .of_forall fun d ↦ ?_
  simp only [shifted_choose_ratio]
  ring

#print axioms shiftCost_formula
#print axioms shiftedFalling_bounds
#print axioms shiftedChoose_limit
#print axioms shiftedChoose_correction

end OrderedPartitions.ReciprocalEdge
