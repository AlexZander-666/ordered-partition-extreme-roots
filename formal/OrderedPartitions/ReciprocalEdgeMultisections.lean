import OrderedPartitions.ReciprocalEdgeUniform
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Differentiation identities for the exponential multisections in the reciprocal limit. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace OrderedPartitions.ReciprocalEdge

private def scaleCoeff (j r n : ℕ) : ℂ := ((r+j*n).factorial : ℂ)⁻¹

private theorem coeff_norm (j r n : ℕ) :
    ‖scaleCoeff j r n‖ = ((r+j*n).factorial : ℝ)⁻¹ := by
  simp [scaleCoeff]

private theorem index_le {j : ℕ} (hj : 1≤j) (r n : ℕ) : n≤r+j*n := by
  have h := Nat.mul_le_mul_right n hj
  simpa using h.trans (Nat.le_add_left _ _)

private theorem coeff_sum {j : ℕ} (hj : 1≤j) (r : ℕ) (z : ℂ) :
    Summable (fun n ↦ scaleCoeff j r n*z^n) := by
  apply (Real.summable_pow_div_factorial ‖z‖).of_norm_bounded
  intro n
  rw [norm_mul, coeff_norm, norm_pow, inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (by exact_mod_cast Nat.factorial_le (index_le hj r n))

private theorem derivative_majorant {j : ℕ} (hj : 1≤j) (r n : ℕ) {R : ℝ} {z : ℂ}
    (hr : ‖z‖≤R) :
    ‖scaleCoeff j r (n+1)*((n+1:ℕ):ℂ)*z^n‖ ≤ R^n/(n.factorial:ℝ) := by
  have den : ((n+1).factorial:ℝ) ≤ ((r+j*(n+1)).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le (index_le hj r (n+1))
  simp only [norm_mul,coeff_norm,Complex.norm_natCast,norm_pow]
  calc
    _ ≤ ((n+1).factorial:ℝ)⁻¹ * (n+1:ℕ) * R^n := by
      gcongr
    _ = _ := by rw [Nat.factorial_succ,Nat.cast_mul];field_simp

theorem multisection_derivative {j : ℕ} (hj : 1≤j) (r : ℕ) (w : ℂ) :
    HasDerivAt (reciprocalLimit j r)
      (∑' n, scaleCoeff j r (n+1)*((n+1:ℕ):ℂ)*w^n) w := by
  let R := ‖w‖+1
  let g := fun (n : ℕ) (z : ℂ) ↦ scaleCoeff j r (n+1)*z^(n+1)
  let D := fun (n : ℕ) (z : ℂ) ↦ scaleCoeff j r (n+1)*((n+1:ℕ):ℂ)*z^n
  have der := hasDerivAt_tsum_of_isPreconnected (g:=g) (g':=D)
    (Real.summable_pow_div_factorial R) (isOpen_ball (x:=(0:ℂ)) (ε:=R))
    (convex_ball (0:ℂ) R).isPreconnected (fun n z _ ↦ by
      simpa [g,D,mul_assoc] using (hasDerivAt_pow (n+1) z).const_mul (scaleCoeff j r (n+1)))
    (fun n z h ↦ derivative_majorant hj r n (by simpa using (mem_ball.mp h).le))
    (show (0:ℂ)∈ball 0 R from mem_ball_self (by dsimp [R];positivity))
    ((summable_nat_add_iff 1).2 (coeff_sum hj r 0)) (show w∈ball 0 R from by simp [R])
  have add := der.const_add (scaleCoeff j r 0)
  apply add.congr_of_eventuallyEq
  filter_upwards with z
  rw [reciprocalLimit]
  simp only [one_div,Complex.ofReal_inv,Complex.ofReal_natCast]
  change (∑' n, scaleCoeff j r n*z^n) = _
  rw [(coeff_sum hj r z).tsum_eq_zero_add]
  simp [g]


private theorem series_eq (j r : ℕ) (z : ℂ) :
    reciprocalLimit j r z = ∑' n, scaleCoeff j r n*z^n := by
  simp only [reciprocalLimit,scaleCoeff,one_div,Complex.ofReal_inv,Complex.ofReal_natCast]

private theorem summable_deriv {j : ℕ} (hj : 1≤j) (r : ℕ) (z : ℂ) :
    Summable (fun n ↦ scaleCoeff j r (n+1)*((n+1:ℕ):ℂ)*z^n) :=
  (Real.summable_pow_div_factorial ‖z‖).of_norm_bounded (fun n ↦ derivative_majorant hj r n le_rfl)

private theorem factorial_step (m : ℕ) :
    ((m.factorial:ℂ))⁻¹=((m+1:ℕ):ℂ)*(((m+1).factorial:ℂ))⁻¹ := by
  rw [Nat.factorial_succ,Nat.cast_mul]
  field_simp

/-- The last residue is the derivative of the first, scaled by the threshold. -/
theorem last_multisection {j : ℕ} (hj : 1≤j) (w : ℂ) :
    reciprocalLimit j (j-1) w = (j:ℂ)*deriv (reciprocalLimit j 0) w := by
  rw [(multisection_derivative hj 0 w).deriv,series_eq,←tsum_mul_left]
  apply tsum_congr
  intro n
  have eq : j*(n+1)=(j-1+j*n)+1 := by rw [Nat.mul_add];omega
  have coef := factorial_step (j-1+j*n)
  rw [←eq,Nat.cast_mul] at coef
  simp only [scaleCoeff,Nat.zero_add]
  rw [coef]
  ring

/-- The adjacent multisections obey the first-order differential recurrence at every complex point. -/
theorem previous_multisection {j : ℕ} (hj : 1≤j) (r : ℕ) (w : ℂ) :
    reciprocalLimit j r w=(r+1:ℕ)*reciprocalLimit j (r+1) w+
      (j:ℂ)*w*deriv (reciprocalLimit j (r+1)) w := by
  rw [(multisection_derivative hj (r+1) w).deriv]
  simp only [series_eq]
  rw [←tsum_mul_left,←tsum_mul_left]
  rw [(coeff_sum hj r w).tsum_eq_zero_add,((coeff_sum hj (r+1) w).mul_left (↑(r+1):ℂ)).tsum_eq_zero_add]
  rw [add_assoc,←Summable.tsum_add ((summable_nat_add_iff 1).2 ((coeff_sum hj (r+1) w).mul_left (↑(r+1):ℂ)))
    ((summable_deriv hj (r+1) w).mul_left ((j:ℂ)*w))]
  congr 1
  · simp [scaleCoeff,Nat.factorial_succ];field_simp
  · apply tsum_congr
    intro n
    have e : r+1+j*(n+1)=(r+j*(n+1))+1 := by omega
    have coef := factorial_step (r+j*(n+1))
    rw [←e] at coef
    simp only [scaleCoeff]
    rw [coef,pow_succ]
    push_cast
    ring


/-- The exponential is recovered exactly by collecting its Taylor series into
residue classes. In particular, the vector of all sections never vanishes. -/
theorem regroup_exponential {j : ℕ} (hj : 1≤j) (t : ℂ) :
    ∑ r : Fin j, t^(r:ℕ)*reciprocalLimit j r (t^j)=Complex.exp t := by
  let _ : NeZero j := ⟨by omega⟩
  let e := (Nat.divModEquiv j).trans (Equiv.prodComm ℕ (Fin j))
  have orig : HasSum (fun m : ℕ ↦ t^m/(m.factorial:ℂ)) (Complex.exp t) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp t
  have full := e.symm.hasSum_iff.mpr orig
  have per (r : Fin j) : HasSum (fun n : ℕ ↦ t^(e.symm (r,n))/((e.symm (r,n)).factorial:ℂ))
      (t^(r:ℕ)*reciprocalLimit j r (t^j)) := by
    rw [series_eq]
    apply HasSum.congr_fun ((coeff_sum hj r (t^j)).hasSum.mul_left (t^(r:ℕ)))
    intro n
    change t^(n*j+r.val)/((n*j+r.val).factorial:ℂ)=_
    rw [Nat.mul_comm n j,Nat.add_comm (j*n) r.val,pow_add,pow_mul]
    simp [scaleCoeff,div_eq_mul_inv]
    ring
  have grouped := full.prod_fiberwise per
  simpa using grouped.tsum_eq

theorem sections_have_no_common_zero {j : ℕ} (hj : 1≤j) (w : ℂ) :
    ∃ r : Fin j, reciprocalLimit j r w≠0 := by
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq w (show 0<j by omega)
  by_contra! allZero
  have eq := regroup_exponential hj t
  simp only [ht,allZero,mul_zero,Finset.sum_const_zero] at eq
  exact Complex.exp_ne_zero t eq.symm

#print axioms regroup_exponential
#print axioms sections_have_no_common_zero
#print axioms last_multisection
#print axioms previous_multisection

#print axioms multisection_derivative
end OrderedPartitions.ReciprocalEdge
