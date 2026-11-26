import OrderedPartitions.ReciprocalEdgeFirstCorrectionCoefficient

/-! The explicit coefficient of the first correction, with truncated factorials. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open PowerSeries

/-- The correction is the fallen-binomial contribution plus the linear term of
the factor V and the quadratic term of H. Terms below their support vanish. -/
theorem reciprocalCorrectionCoeff_formula {j : ℕ} (hj : 2 ≤ j) (r h : ℕ) :
    let m := r+j*h
    let b := edgeScale j
    let c := coeff 2 (H j)
    reciprocalCorrectionCoeff j r h =
      -((m:ℝ)*h+(m:ℝ)*((m:ℝ)-1)/2)/(m.factorial:ℝ) +
      (if m=0 then 0 else (1/b)/((m-1).factorial:ℝ)) +
      (if m≤1 then 0 else (c/b^2)/((m-2).factorial:ℝ)) := by
  dsimp only [reciprocalCorrectionCoeff]
  generalize r+j*h = m
  have v0 : constantCoeff (V j) = 1 := by simpa only [coeff_zero_eq_constantCoeff_apply] using V_zero hj
  have l0 : constantCoeff (L j) = edgeScale j := by
    simpa only [coeff_zero_eq_constantCoeff_apply, edgeScale] using L_zero hj
  have l1 : coeff 1 (L j) = coeff 2 (H j) := by simp [L]
  have bn := (edgeScale_pos j).ne'
  rw [seriesFirstCorrection, shiftCost_formula, coeff_zero_eq_constantCoeff_apply,
    map_mul, map_pow, v0, l0, one_mul]
  cases m with
  | zero => norm_num
  | succ m =>
    simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one, coeff_one_mul,
      coeff_one_pow, map_pow, v0, l0, l1, V_one hj, one_mul, mul_one]
    cases m with
    | zero =>
      norm_num
      field_simp [bn]
    | succ k =>
      simp only [show ¬ k.succ.succ ≤ 1 by omega, if_false, Nat.succ_sub_one,
        show k.succ.succ-2=k by omega, Nat.factorial_succ k,
        Nat.cast_mul]
      rw [pow_succ (edgeScale j) k.succ, pow_succ (edgeScale j) k]
      field_simp [bn]
      ring

#print axioms reciprocalCorrectionCoeff_formula

end OrderedPartitions.ReciprocalEdge
