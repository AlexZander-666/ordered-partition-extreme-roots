import OrderedPartitions.ReciprocalEdgeFirstCorrectionRoot

/-! The original root drift when two rows have the same residue modulo j. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open Filter
open scoped Topology

def originalScaleConstant (j : ℕ) : ℝ := (j.factorial:ℝ)*(edgeScale j)^j

theorem reciprocalArgumentScale_factor (j d : ℕ) :
    reciprocalArgumentScale j d = originalScaleConstant j*(d:ℝ)^j := by
  simp only [reciprocalArgumentScale, originalScaleConstant, mul_pow, mul_assoc]

private theorem originalScaleConstant_pos (j : ℕ) : 0 < originalScaleConstant j := by
  have b := edgeScale_pos j
  unfold originalScaleConstant
  positivity

private theorem succ_ratio_limit :
    Tendsto (fun d : ℕ ↦ ((d:ℝ)+1)/(d:ℝ)) atTop (𝓝 1) := by
  have v := (tendsto_const_nhds (x := (1:ℝ))).add
    (Kernel.cutoff_inv_limit (J := id) tendsto_id)
  simp only [id_eq, add_zero] at v
  apply v.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have dn : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d≠0)
  field_simp [dn]

private theorem power_increment_limit {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun d : ℕ ↦ (((d:ℝ)+1)^j-(d:ℝ)^j)/(d:ℝ)^(j-1)) atTop (𝓝 (j:ℝ)) := by
  let P := fun u : ℝ ↦ u^j
  have cont : ContinuousAt (dslope P 1) 1 :=
    continuousAt_dslope_same.mpr (hasDerivAt_pow j (1:ℝ)).differentiableAt
  have out := cont.tendsto.comp succ_ratio_limit
  have val : dslope P 1 1 = (j:ℝ) := by simp [dslope_same, P]
  rw [val] at out
  apply out.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have dn : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d≠0)
  let x := ((d:ℝ)+1)/(d:ℝ)
  have offset : x-1 = (d:ℝ)⁻¹ := by dsimp [x]; field_simp [dn]; ring
  have ds := sub_smul_dslope P 1 x
  rw [offset, smul_eq_mul] at ds
  have val : dslope P 1 x = (d:ℝ)*(x^j-1) := by
    calc
      _ = (d:ℝ)*((d:ℝ)⁻¹*dslope P 1 x) := by rw [← mul_assoc, mul_inv_cancel₀ dn, one_mul]
      _ = _ := by rw [ds]; simp [P]
  change dslope P 1 x = _
  rw [val]
  dsimp [x]
  rw [div_pow, show (d:ℝ)^j = (d:ℝ)^(j-1)*(d:ℝ) by rw [← pow_succ, Nat.sub_add_cancel hj]]
  field_simp [dn]

theorem increment_of_two_terms {j : ℕ} (hj : 1 ≤ j) {t : ℕ → ℝ} {A B : ℝ}
    (expansion : Tendsto (fun d : ℕ ↦ (t d-A*(d:ℝ)^j)/(d:ℝ)^(j-1)) atTop (𝓝 B)) :
    Tendsto (fun d : ℕ ↦ (t (d+1)-t d)/(d:ℝ)^(j-1)) atTop (𝓝 ((j:ℝ)*A)) := by
  let E (d : ℕ) := (t d-A*(d:ℝ)^j)/(d:ℝ)^(j-1)
  have eshift : Tendsto (fun d ↦ E (d+1)) atTop (𝓝 B) :=
    expansion.comp (tendsto_add_atTop_nat 1)
  have err := (eshift.mul (succ_ratio_limit.pow (j-1))).sub expansion
  simp only [one_pow, mul_one, sub_self] at err
  have total := ((power_increment_limit hj).mul_const A).add err
  simp only [add_zero] at total
  apply total.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have dn : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d≠0)
  have ds : (d:ℝ)+1 ≠ 0 := by positivity
  dsimp only [E]
  push_cast
  rw [div_pow]
  field_simp [dn, ds]
  ring

theorem original_two_term_limit {j r : ℕ} (hj : 2 ≤ j) {c : ℝ} (hc : c < 0)
    (zero : reciprocalLimit j r (c:ℂ) = 0) (simple : deriv (reciprocalLimit j r) (c:ℂ) ≠ 0)
    {x : ℕ → ℝ} (xlim : Tendsto x atTop (𝓝 c))
    (root : ∀ᶠ d in atTop, reciprocalValue j r d (x d:ℂ) = 0) :
    Tendsto (fun d : ℕ ↦
      (reciprocalArgumentScale j d/x d-(originalScaleConstant j/c)*(d:ℝ)^j)/(d:ℝ)^(j-1))
      atTop (𝓝 (originalScaleConstant j *
        (reciprocalCorrection j r (c:ℂ)/deriv (reciprocalLimit j r) (c:ℂ)).re/c^2)) := by
  let G := originalScaleConstant j
  let v := reciprocalCorrection j r (c:ℂ)/deriv (reciprocalLimit j r) (c:ℂ)
  have dx := (Complex.continuous_re.tendsto _).comp
    (simple_zero_first_correction hj zero simple xlim root)
  have real_shift : Tendsto (fun d : ℕ ↦ (d:ℝ)*(x d-c)) atTop (𝓝 (-v.re)) := by
    simpa [Function.comp_def, Complex.mul_re, Complex.sub_re, v, neg_div] using dx
  have out := ((real_shift.const_mul (-G)).div (xlim.mul_const c) (mul_ne_zero hc.ne hc.ne))
  have target : (-G)*(-v.re)/(c*c) = G*v.re/c^2 := by ring
  rw [target] at out
  apply out.congr'
  filter_upwards [eventually_ge_atTop 1, xlim.eventually (eventually_ne_nhds hc.ne)] with d hd xn
  have dn : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d≠0)
  change (-G)*((d:ℝ)*(x d-c))/(x d*c) =
    (reciprocalArgumentScale j d/x d-(G/c)*(d:ℝ)^j)/(d:ℝ)^(j-1)
  rw [reciprocalArgumentScale_factor]
  change (-G)*((d:ℝ)*(x d-c))/(x d*c) =
    (G*(d:ℝ)^j/x d-(G/c)*(d:ℝ)^j)/(d:ℝ)^(j-1)
  rw [show (d:ℝ)^j = (d:ℝ)^(j-1)*(d:ℝ) by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1≤j)]]
  field_simp [dn, xn, hc.ne]
  ring

/-- A simple negative zero in the limit yields original simple roots with an
explicit two-term expansion and a strictly negative same-residue drift. -/
theorem original_same_residue_drift {j r : ℕ} (hj : 2 ≤ j) (hr : r < j) {c : ℝ}
    (hc : c < 0) (zero : reciprocalLimit j r (c:ℂ) = 0)
    (simple : deriv (reciprocalLimit j r) (c:ℂ) ≠ 0) :
    ∃ t : ℕ → ℝ,
      (∀ᶠ d : ℕ in atTop, t d < 0 ∧ originalValue j r d (t d:ℂ) = 0 ∧
        deriv (originalValue j r d) (t d:ℂ) ≠ 0) ∧
      Tendsto (fun d : ℕ ↦ (t d-(originalScaleConstant j/c)*(d:ℝ)^j)/(d:ℝ)^(j-1))
        atTop (𝓝 (originalScaleConstant j *
          (reciprocalCorrection j r (c:ℂ)/deriv (reciprocalLimit j r) (c:ℂ)).re/c^2)) ∧
      Tendsto (fun d : ℕ ↦ (t (d+1)-t d)/(d:ℝ)^(j-1))
        atTop (𝓝 ((j:ℝ)*(originalScaleConstant j/c))) ∧
      (∀ᶠ d : ℕ in atTop, t (d+1) < t d) := by
  obtain ⟨x, xlim, rows⟩ := reciprocal_real_zero_sequence hj hc zero simple
  let t (d : ℕ) := reciprocalArgumentScale j d/x d
  have expansion := original_two_term_limit hj hc zero simple xlim (rows.mono fun _ p ↦ p.2.1)
  have drift := increment_of_two_terms (by omega : 1≤j) expansion
  refine ⟨t, ?_, expansion, drift, ?_⟩
  · filter_upwards [rows, eventually_ge_atTop 1] with d p hd
    refine ⟨div_neg_of_pos_of_neg (reciprocalArgumentScale_pos j hd) p.1, ?_⟩
    rw [show (t d:ℂ) = (reciprocalArgumentScale j d:ℂ)/(x d:ℂ) from Complex.ofReal_div _ _]
    exact original_simple_of_reciprocal hj hr hd (Complex.ofReal_ne_zero.mpr p.1.ne)
      p.2.1 p.2.2
  · have neg : (j:ℝ)*(originalScaleConstant j/c) < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast (by omega : 0<j))
        (div_neg_of_pos_of_neg (originalScaleConstant_pos j) hc)
    filter_upwards [drift.eventually_lt_const neg, eventually_ge_atTop 1] with d v hd
    have dp : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
    have sd := (div_lt_iff₀ (pow_pos dp (j-1))).mp v
    exact sub_neg.mp (by simpa only [zero_mul] using sd)

#print axioms reciprocalArgumentScale_factor
#print axioms original_two_term_limit
#print axioms increment_of_two_terms
#print axioms original_same_residue_drift

end OrderedPartitions.ReciprocalEdge
