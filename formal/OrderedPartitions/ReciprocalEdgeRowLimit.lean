import OrderedPartitions.ReciprocalEdgeOriginal
import OrderedPartitions.ReciprocalEdgeLimit

/-! Fixed-coefficient convergence for the scaled reciprocals of the original rows. -/

noncomputable section
open Filter PowerSeries
open scoped Topology

namespace OrderedPartitions.ReciprocalEdge

/-- The slope of the series `H` at the origin. -/
def edgeScale (j : ℕ) : ℝ := 1 + 1 / ((j : ℝ) + 1)

theorem edgeScale_pos (j : ℕ) : 0 < edgeScale j := by
  unfold edgeScale
  positivity

/-- The coefficient in the scaled reciprocal row, indexed by the reversed degree. -/
def scaledReciprocalCoeff (j r d h : ℕ) : ℝ :=
  if h ≤ d then (j.factorial : ℝ)^(d-h) *
    ((row (j*d+r) j).coeff (d-h) / ((j*d+r).factorial : ℝ)) /
    (edgeScale j * (d : ℝ))^(r+j*h) else 0

/-- The polynomial extension of the scaled reciprocal row across the origin. -/
def reciprocalRow (j r d : ℕ) : Polynomial ℝ :=
  ∑ h ∈ Finset.range (d+1), Polynomial.monomial h (scaledReciprocalCoeff j r d h)

theorem reciprocalRow_coeff (j r d h : ℕ) :
    (reciprocalRow j r d).coeff h = scaledReciprocalCoeff j r d h := by
  rw [reciprocalRow, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hd : h ≤ d
  · rw [Finset.sum_eq_single h]
    · simp
    · intro i _ ne
      simp [ne]
    · intro outside
      exact (outside (Finset.mem_range.mpr (Nat.lt_succ_of_le hd))).elim
  · rw [Finset.sum_eq_zero]
    · simp [scaledReciprocalCoeff, hd]
    · intro i hi
      have ne : h ≠ i := fun eq ↦ hd (eq ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      simp [Ne.symm ne]

theorem scaled_coeff_of_offset {j : ℕ} (hj : 2 ≤ j) (r : ℕ) {d h : ℕ} (hh : h ≤ d) :
    scaledReciprocalCoeff j r d h =
      coeff (r+j*h) (V j * H j ^ (d-h)) / (edgeScale j * (d : ℝ))^(r+j*h) := by
  rw [scaledReciprocalCoeff, if_pos hh, edge_coefficient hj d r h hh, ← mul_assoc, ← mul_pow]
  rw [mul_inv_cancel₀ (by positivity : (j.factorial : ℝ) ≠ 0), one_pow, one_mul]

private theorem shifted_ratio (h : ℕ) :
    Tendsto (fun d : ℕ ↦ ((d-h : ℕ) : ℝ) / (d : ℝ)) atTop (𝓝 1) := by
  have vanishes := (Kernel.cutoff_inv_limit (J := id) tendsto_id).const_mul (h : ℝ)
  have near := (tendsto_const_nhds (x := (1 : ℝ))).sub vanishes
  simp only [mul_zero, sub_zero] at near
  apply near.congr'
  filter_upwards [eventually_ge_atTop (h+1)] with d hd
  have lower : h ≤ d := by omega
  have dn : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  change 1 - (h : ℝ)*(d : ℝ)⁻¹ = ((d-h : ℕ) : ℝ) / (d : ℝ)
  rw [Nat.cast_sub lower]
  field_simp

/-- Every fixed reversed coefficient of the true row tends to its factorial limit. -/
theorem original_fixed_coefficient_limit {j : ℕ} (hj : 2 ≤ j) (r h : ℕ) :
    Tendsto (fun d : ℕ ↦ scaledReciprocalCoeff j r d h) atTop
      (𝓝 (1 / ((r+j*h).factorial : ℝ))) := by
  let m := r+j*h
  have nz := (edgeScale_pos j).ne'
  have seed : Tendsto (fun d : ℕ ↦ coeff m (V j * H j ^ (d-h)) / ((d-h : ℕ) : ℝ)^m)
        atTop (𝓝 ((edgeScale j)^m / (m.factorial : ℝ))) := by
    have kernel := (fixed_coefficient_limit (V j) (L j) m).comp (tendsto_sub_atTop_nat h)
    simpa only [Function.comp_def, ← H_eq_one_add_X_mul hj, ← coeff_zero_eq_constantCoeff_apply,
      V_zero hj, L_zero hj, one_mul, edgeScale] using kernel
  have correction : Tendsto (fun d : ℕ ↦ ((d-h : ℕ) : ℝ) / (edgeScale j * (d : ℝ)))
      atTop (𝓝 (edgeScale j)⁻¹) := by
    simpa [div_div, mul_comm, one_div] using (shifted_ratio h).div_const (edgeScale j)
  have total := seed.mul (correction.pow m)
  have limit : (edgeScale j)^m / (m.factorial : ℝ) * ((edgeScale j)⁻¹)^m =
      1 / (m.factorial : ℝ) := by
    rw [div_mul_eq_mul_div, ← mul_pow, mul_inv_cancel₀ nz, one_pow]
  rw [limit] at total
  apply total.congr'
  filter_upwards [eventually_ge_atTop (h+1)] with d hd
  have lower : h ≤ d := by omega
  have dn : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hn : ((d-h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : d-h ≠ 0)
  simp only [scaled_coeff_of_offset hj r lower, m, div_pow]
  field_simp

theorem reciprocal_row_coefficient_limit {j : ℕ} (hj : 2 ≤ j) (r h : ℕ) :
    Tendsto (fun d : ℕ ↦ (reciprocalRow j r d).coeff h) atTop
      (𝓝 (1 / ((r+j*h).factorial : ℝ))) := by
  simpa only [reciprocalRow_coeff] using original_fixed_coefficient_limit hj r h

#print axioms reciprocalRow_coeff
#print axioms scaled_coeff_of_offset
#print axioms original_fixed_coefficient_limit
#print axioms reciprocal_row_coefficient_limit

end OrderedPartitions.ReciprocalEdge
