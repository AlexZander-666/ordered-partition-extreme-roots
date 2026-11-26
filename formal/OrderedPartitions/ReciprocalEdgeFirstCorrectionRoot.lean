import OrderedPartitions.ReciprocalEdgeFirstCorrectionUniform
import OrderedPartitions.ReciprocalEdgeOuterPrefixInverse
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.Calculus.DSlope

/-! First-order motion of a simple negative zero of the reciprocal rows. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open Filter Metric Set
open scoped Topology

/-- A fixed simple real limiting zero gives a convergent sequence of real row zeros. -/
theorem reciprocal_real_zero_sequence {j r : ℕ} (hj : 2 ≤ j) {c : ℝ} (hc : c < 0)
    (zero : reciprocalLimit j r (c:ℂ) = 0) (simple : deriv (reciprocalLimit j r) (c:ℂ) ≠ 0) :
    ∃ x : ℕ → ℝ, Tendsto x atTop (𝓝 c) ∧ ∀ᶠ d in atTop,
      x d < 0 ∧ reciprocalValue j r d (x d:ℂ) = 0 ∧ deriv (reciprocalValue j r d) (x d:ℂ) ≠ 0 := by
  classical
  obtain ⟨R, Rbound, evt⟩ := reciprocal_real_simple_isolation hj zero simple (neg_pos.mpr hc)
  let good (d : ℕ) (x : ℝ) : Prop :=
    (x:ℂ) ∈ closedBall (c:ℂ) R ∧ reciprocalValue j r d (x:ℂ) = 0 ∧
    deriv (reciprocalValue j r d) (x:ℂ) ≠ 0 ∧
    ∀ y ∈ closedBall (c:ℂ) R, reciprocalValue j r d y = 0 → y = (x:ℂ)
  let x (d : ℕ) : ℝ := if h : ∃ y, good d y then h.choose else c
  have chosen : ∀ᶠ d in atTop, good d (x d) := by
    filter_upwards [evt] with d evt_d
    have e : ∃ y, good d y := evt_d
    simpa only [x, dif_pos e] using e.choose_spec
  have cast_distance (y : ℝ) : dist (y:ℂ) (c:ℂ) = dist y c := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]
  refine ⟨x, Metric.tendsto_nhds.mpr ?_, ?_⟩
  · intro ε ep
    obtain ⟨s, hs, near⟩ := reciprocal_real_simple_isolation hj zero simple (lt_min ep Rbound.1)
    filter_upwards [chosen, near] with d cert exists_near
    obtain ⟨y, hy, zy, _, _⟩ := exists_near
    have within : (y:ℂ) ∈ closedBall (c:ℂ) R := by
      exact mem_closedBall.mpr ((mem_closedBall.mp hy).trans
        (hs.2.trans_le (min_le_right _ _)).le)
    have same := Complex.ofReal_inj.mp (cert.2.2.2 _ within zy)
    rw [← same, ← cast_distance]
    exact (mem_closedBall.mp hy).trans_lt (hs.2.trans_le (min_le_left _ _))
  · filter_upwards [chosen] with d cert
    have bound := (mem_closedBall.mp cert.1).trans_lt Rbound.2
    rw [cast_distance, Real.dist_eq, abs_lt] at bound
    exact ⟨by linarith only [bound.2], cert.2.1, cert.2.2.1⟩

/-- The first correction of any convergent branch of reciprocal zeros at a simple limit. -/
theorem simple_zero_first_correction {j r : ℕ} (hj : 2 ≤ j) {c : ℝ}
    (zero : reciprocalLimit j r (c:ℂ) = 0) (simple : deriv (reciprocalLimit j r) (c:ℂ) ≠ 0)
    {x : ℕ → ℝ} (xlim : Tendsto x atTop (𝓝 c))
    (isroot : ∀ᶠ d in atTop, reciprocalValue j r d (x d:ℂ) = 0) :
    Tendsto (fun d : ℕ ↦ (d:ℂ)*((x d:ℂ)-(c:ℂ))) atTop
      (𝓝 (-(reciprocalCorrection j r (c:ℂ))/deriv (reciprocalLimit j r) (c:ℂ))) := by
  let rad := ‖(c:ℂ)‖+1
  let disk := closedBall (0:ℂ) rad
  have cball : (c:ℂ) ∈ ball (0:ℂ) rad := by
    rw [mem_ball, dist_zero_right]
    dsimp [rad]
    linarith
  have complexLimit : Tendsto (fun d ↦ (x d:ℂ)) atTop (𝓝 (c:ℂ)) :=
    (Complex.continuous_ofReal.tendsto c).comp xlim
  have domain : Tendsto (fun d ↦ (x d:ℂ)) atTop (𝓝[disk] (c:ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ complexLimit
    exact (complexLimit.eventually (isOpen_ball.mem_nhds cball)).mono (fun _ h ↦ ball_subset_closedBall h)
  have uniform := reciprocal_uniform_first_correction hj r rad
  have pc (d : ℕ) : Continuous (reciprocalValue j r d) := by
    change Continuous (fun w ↦ (reciprocalRow j r d).eval₂ Complex.ofRealHom w)
    simp_rw [Polynomial.eval₂_eq_eval_map]
    exact Polynomial.continuous _
  have correction_cont : ContinuousOn (reciprocalCorrection j r) disk :=
    uniform.continuousOn (Frequently.of_forall (fun d ↦
      (continuous_const.mul ((pc d).sub (reciprocal_limit_holomorphic hj r).continuous)).continuousOn))
  have correction_val := uniform.tendsto_comp
    (correction_cont _ (ball_subset_closedBall cball)) domain
  have slope_cont : ContinuousAt (dslope (reciprocalLimit j r) (c:ℂ)) (c:ℂ) :=
    continuousAt_dslope_same.mpr ((reciprocal_limit_holomorphic hj r) _)
  have slope_limit : Tendsto (fun d ↦ dslope (reciprocalLimit j r) (c:ℂ) (x d:ℂ)) atTop
      (𝓝 (deriv (reciprocalLimit j r) (c:ℂ))) := by
    simpa only [Function.comp_def, dslope_same] using slope_cont.tendsto.comp complexLimit
  have quotient := correction_val.neg.div slope_limit simple
  apply quotient.congr'
  filter_upwards [isroot, slope_limit.eventually (eventually_ne_nhds simple)] with d z nz
  apply (div_eq_iff nz).mpr
  have slope_identity := sub_smul_dslope (reciprocalLimit j r) (c:ℂ) (x d:ℂ)
  rw [zero, sub_zero, smul_eq_mul] at slope_identity
  change -((d:ℂ)*(reciprocalValue j r d (x d:ℂ)-reciprocalLimit j r (x d:ℂ))) = _
  rw [z, zero_sub, ← slope_identity]
  ring

#print axioms reciprocal_real_zero_sequence
#print axioms simple_zero_first_correction

end OrderedPartitions.ReciprocalEdge
