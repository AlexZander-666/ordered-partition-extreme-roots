import OrderedPartitions.ReciprocalEdgeFirstCorrectionBinomial

/-! Read the two highest binomial terms of each original reciprocal coefficient. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open Finset Filter PowerSeries
open scoped Topology

/-- First correction for a fixed coefficient of a binomial power series.
The second term is absent at coefficient index zero. -/
def seriesFirstCorrection (V L : PowerSeries ℝ) (h m : ℕ) : ℝ :=
  -shiftCost h m / (m.factorial:ℝ) * coeff 0 (V*L^m) +
    if m=0 then 0 else coeff 1 (V*L^(m-1)) / ((m-1).factorial:ℝ)

private theorem lower_weighted_binomial (h : ℕ) {i m : ℕ} (lower : i+1 < m) :
    Tendsto (fun d : ℕ ↦ (d:ℝ)*((d-h).choose i:ℝ)/(d:ℝ)^m) atTop (𝓝 0) := by
  let k := m-i-1
  have positive : k ≠ 0 := by dsimp [k]; omega
  have decay := Kernel.inv_power_limit (J := id) tendsto_id k
  simp only [id_eq, zero_pow positive] at decay
  have combined := (shiftedChoose_limit h i).mul decay
  simp only [mul_zero] at combined
  apply combined.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have dn : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d≠0)
  rw [show m=i+k+1 by dsimp [k]; omega, pow_succ, pow_add]
  field_simp [dn]

/-- The top two summands of the exact binomial expansion give the first
correction, and every lower summand tends to zero after multiplication by d. -/
theorem fixed_series_first_correction (V L : PowerSeries ℝ) (h m : ℕ) :
    Tendsto (fun d : ℕ ↦ (d:ℝ)*(coeff m (V*(1+X*L)^(d-h))/(d:ℝ)^m -
      coeff 0 (V*L^m)/(m.factorial:ℝ))) atTop (𝓝 (seriesFirstCorrection V L h m)) := by
  cases m with
  | zero =>
    simp [fixed_coeff, seriesFirstCorrection, shiftCost]
  | succ k =>
    let a (i : ℕ) := coeff (k+1-i) (V*L^i)
    let small (d : ℕ) :=
      ∑ i ∈ range k, ((d:ℝ)*((d-h).choose i:ℝ)/(d:ℝ)^(k+1))*a i
    have term (i : ℕ) (hi : i ∈ range k) :
        Tendsto (fun d : ℕ ↦ ((d:ℝ)*((d-h).choose i:ℝ)/(d:ℝ)^(k+1))*a i)
          atTop (𝓝 0) := by
      have bound : i+1 < k+1 := by have := mem_range.mp hi; omega
      simpa only [zero_mul] using (lower_weighted_binomial h bound).mul_const (a i)
    have low : Tendsto small atTop (𝓝 0) := by
      simpa only [sum_const_zero] using tendsto_finsetSum (range k) term
    have second := (shiftedChoose_limit h k).mul_const (a k)
    have highest := (shiftedChoose_correction h (k+1)).mul_const (a (k+1))
    have combine := (low.add second).add highest
    have result : 0+1/(k.factorial:ℝ)*a k+
        (-shiftCost h (k+1)/(Nat.factorial (k+1):ℝ))*a (k+1) =
        seriesFirstCorrection V L h (k+1) := by
      simp only [seriesFirstCorrection, a, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel,
        Nat.sub_self, zero_add, show k+1-k=1 by omega]
      ring
    rw [result] at combine
    apply combine.congr'
    filter_upwards [eventually_ge_atTop 1] with d hd
    have dn : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d≠0)
    rw [fixed_coeff, sum_range_succ, sum_range_succ]
    rw [← show a (k+1) = coeff 0 (V*L^(k+1)) by simp [a]]
    change small d + (((d-h).choose k:ℝ)/(d:ℝ)^k)*a k +
      ((d:ℝ)*(((d-h).choose (k+1):ℝ)/(d:ℝ)^(k+1)-1/(Nat.factorial (k+1):ℝ)))*a (k+1) =
      (d:ℝ)*(((∑ i ∈ range k, ((d-h).choose i:ℝ)*a i) +
        ((d-h).choose k:ℝ)*a k + ((d-h).choose (k+1):ℝ)*a (k+1))/(d:ℝ)^(k+1) -
        a (k+1)/(Nat.factorial (k+1):ℝ))
    have lower_eq : small d = (d:ℝ)*(∑ i ∈ range k, ((d-h).choose i:ℝ)*a i)/(d:ℝ)^(k+1) := by
      dsimp only [small]
      rw [mul_sum, sum_div]
      exact sum_congr rfl fun i _ ↦ by ring
    rw [lower_eq, pow_succ]
    field_simp [dn]
    ring

/-- The coefficient of the first correction to the normalized original reciprocal row. -/
def reciprocalCorrectionCoeff (j r h : ℕ) : ℝ :=
  seriesFirstCorrection (V j) (L j) h (r+j*h) / (edgeScale j)^(r+j*h)

/-- The first correction holds for every fixed reversed coefficient of the original row. -/
theorem original_coefficient_first_correction {j : ℕ} (hj : 2 ≤ j) (r h : ℕ) :
    Tendsto (fun d : ℕ ↦ (d:ℝ)*(scaledReciprocalCoeff j r d h -
      1/((r+j*h).factorial:ℝ))) atTop (𝓝 (reciprocalCorrectionCoeff j r h)) := by
  let m := r+j*h
  let b := edgeScale j
  have bp : 0 < b := edgeScale_pos j
  have top : coeff 0 (V j*L j^m) = b^m := by
    rw [coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
      ← coeff_zero_eq_constantCoeff_apply (V j), ← coeff_zero_eq_constantCoeff_apply (L j),
      V_zero hj, L_zero hj, one_mul]
    rfl
  have lim := (fixed_series_first_correction (V j) (L j) h m).div_const (b^m)
  change Tendsto _ atTop (𝓝 (seriesFirstCorrection (V j) (L j) h m / b^m))
  rw [top] at lim
  apply lim.congr'
  filter_upwards [eventually_ge_atTop (h+1)] with d hd
  have dn : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d≠0)
  have hh : h≤d := by omega
  rw [← H_eq_one_add_X_mul hj, scaled_coeff_of_offset hj r hh]
  change (d:ℝ)*(coeff m (V j*H j^(d-h))/(d:ℝ)^m-b^m/(m.factorial:ℝ))/b^m =
    (d:ℝ)*(coeff m (V j*H j^(d-h))/(b*(d:ℝ))^m-1/(m.factorial:ℝ))
  rw [mul_pow]
  field_simp [dn, bp.ne']

#print axioms fixed_series_first_correction
#print axioms original_coefficient_first_correction

end OrderedPartitions.ReciprocalEdge
