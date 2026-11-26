import OrderedPartitions.ReciprocalEdgeUniform
import OrderedPartitions.ReciprocalEdgeEvaluation
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.MetricSpace.Contracting

/-! Root isolation for reciprocal rows near a nondegenerate limiting zero. -/

noncomputable section
open Filter Set Metric
open scoped Topology NNReal
namespace OrderedPartitions.ReciprocalEdge

private theorem disk_fixed {T : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (lip : LipschitzOnWith (1/2 : ℝ≥0) T (closedBall c r))
    (near : dist (T c) c ≤ r/2) :
    ∃! z, z ∈ closedBall c r ∧ T z = z := by
  have center : c ∈ closedBall c r := mem_closedBall_self hr
  have stable : MapsTo T (closedBall c r) (closedBall c r) := by
    intro z hz
    have bound := lip.dist_le_mul z hz c center
    have hzc := mem_closedBall.mp hz
    rw [mem_closedBall]
    calc
      dist (T z) c ≤ dist (T z) (T c) + dist (T c) c := dist_triangle _ _ _
      _ ≤ r := by norm_num at bound; linarith
  have contraction : ContractingWith (1/2 : ℝ≥0) (stable.restrict T _ _) :=
    ⟨by norm_num, fun x y ↦ lip x.property y.property⟩
  obtain ⟨z, hz, fixed, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete stable contraction center (edist_ne_top _ _)
  refine ⟨z, ⟨hz, fixed⟩, ?_⟩
  rintro y ⟨hy, fy⟩
  have bound := lip.dist_le_mul y hy z hz
  rw [fy, fixed.eq] at bound
  apply dist_le_zero.mp
  norm_num at bound
  linarith


/-- A quantitative isolated simple zero for a complex function near an affine map. -/
theorem isolated_zero_of_derivative_bounds {f : ℂ → ℂ} {c a : ℂ} (ha : a ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (hf : Differentiable ℂ f) (near : ‖f c / a‖ ≤ r/2)
    (bound : ∀ z ∈ closedBall c r, ‖1 - deriv f z / a‖ ≤ 1/2) :
    ∃ z ∈ closedBall c r, f z = 0 ∧ deriv f z ≠ 0 ∧
      ∀ y ∈ closedBall c r, f y = 0 → y = z := by
  let T (z : ℂ) := z - f z / a
  have DT (z : ℂ) : HasDerivAt T (1 - deriv f z / a) z :=
    (hasDerivAt_id z).sub ((hf z).hasDerivAt.div_const a)
  have lip : LipschitzOnWith (1/2 : ℝ≥0) T (closedBall c r) := by
    apply (convex_closedBall c r).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z _ ↦ (DT z).differentiableAt)
    intro z hz
    rw [(DT z).deriv]
    exact_mod_cast bound z hz
  have small : dist (T c) c ≤ r/2 := by simpa [T, dist_eq_norm] using near
  obtain ⟨z, ⟨hz, fixed⟩, unique⟩ := disk_fixed hr lip small
  have eqzero (y : ℂ) : T y = y ↔ f y = 0 := by simp [T, div_eq_zero_iff, ha]
  refine ⟨z, hz, (eqzero z).mp fixed, ?_, fun y hy fy ↦ unique y ⟨hy, (eqzero y).mpr fy⟩⟩
  intro zero
  have bad := bound z hz
  norm_num [zero] at bad

#print axioms isolated_zero_of_derivative_bounds


/-- Compact-uniform control of all the original reciprocal rows, with open domain the plane. -/
theorem reciprocal_locally_uniform {j : ℕ} (hj : 2 ≤ j) (r : ℕ) :
    TendstoLocallyUniformlyOn (fun d w ↦ (reciprocalRow j r d).eval₂ Complex.ofRealHom w)
      (reciprocalLimit j r) atTop univ := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
  intro K _ compact
  obtain ⟨R, inside⟩ := compact.isBounded.subset_closedBall (0 : ℂ)
  exact (reciprocal_uniformly_on_closedBall hj r R).mono inside

private theorem reciprocal_holomorphic (j r d : ℕ) :
    Differentiable ℂ (fun w ↦ (reciprocalRow j r d).eval₂ Complex.ofRealHom w) := by
  simp only [Polynomial.eval₂_eq_eval_map]
  exact Polynomial.differentiable _

theorem reciprocal_limit_holomorphic {j : ℕ} (hj : 2 ≤ j) (r : ℕ) :
    Differentiable ℂ (reciprocalLimit j r) :=
  differentiableOn_univ.mp ((reciprocal_locally_uniform hj r).differentiableOn
    (.of_forall fun d ↦ (reciprocal_holomorphic j r d).differentiableOn) isOpen_univ)

theorem reciprocal_derivative_locally_uniform {j : ℕ} (hj : 2 ≤ j) (r : ℕ) :
    TendstoLocallyUniformlyOn
      (fun d ↦ deriv (fun w ↦ (reciprocalRow j r d).eval₂ Complex.ofRealHom w))
      (deriv (reciprocalLimit j r)) atTop univ :=
  (reciprocal_locally_uniform hj r).deriv
    (.of_forall fun d ↦ (reciprocal_holomorphic j r d).differentiableOn) isOpen_univ

#print axioms reciprocal_derivative_locally_uniform


/-- A simple limiting zero attracts precisely one simple complex zero in arbitrarily
small fixed disks for every sufficiently high reciprocal row. -/
theorem reciprocal_simple_zero_isolation {j r : ℕ} (hj : 2 ≤ j) {c : ℂ}
    (zero : reciprocalLimit j r c = 0) (simple : deriv (reciprocalLimit j r) c ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R ∈ Ioo 0 ε, ∀ᶠ d : ℕ in atTop,
      ∃ z ∈ closedBall c R, (reciprocalRow j r d).eval₂ Complex.ofRealHom z = 0 ∧
        deriv (fun w ↦ (reciprocalRow j r d).eval₂ Complex.ofRealHom w) z ≠ 0 ∧
        ∀ y ∈ closedBall c R, (reciprocalRow j r d).eval₂ Complex.ofRealHom y = 0 → y = z := by
  let a := deriv (reciprocalLimit j r) c
  have pos : 0 < ‖a‖ := norm_pos_iff.mpr simple
  have continuousD := (reciprocal_limit_holomorphic hj r).deriv.continuous.continuousAt (x := c)
  obtain ⟨δ, hδ, hh⟩ := Metric.continuousAt_iff.mp continuousD (‖a‖/4) (by positivity)
  let R := min ε δ / 2
  have hmin : 0 < min ε δ := lt_min hε hδ
  have hR : 0 < R := half_pos hmin
  have Rδ : R < δ := (half_lt_self hmin).trans_le (min_le_right _ _)
  refine ⟨R, ⟨hR, (half_lt_self hmin).trans_le (min_le_left _ _)⟩, ?_⟩
  have at_center := (reciprocal_locally_uniform hj r).tendsto_at (mem_univ c)
  rw [zero] at at_center
  have small : ∀ᶠ d : ℕ in atTop,
      ‖(reciprocalRow j r d).eval₂ Complex.ofRealHom c / a‖ < R/2 := by
    have cv := (at_center.div_const a).norm
    simp only [zero_div, norm_zero] at cv
    exact cv.eventually_lt_const (half_pos hR)
  have uniform := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
    (reciprocal_derivative_locally_uniform hj r) (closedBall c R) (subset_univ _)
      (isCompact_closedBall c R)
  filter_upwards [small, Metric.tendstoUniformlyOn_iff.mp uniform (‖a‖/4) (by positivity)]
    with d hc hD
  apply isolated_zero_of_derivative_bounds simple hR.le (reciprocal_holomorphic j r d) hc.le
  intro w hw
  let v := deriv (fun z ↦ (reciprocalRow j r d).eval₂ Complex.ofRealHom z) w
  have e1 := hh ((mem_closedBall.mp hw).trans_lt Rδ)
  have e2 := hD w hw
  have step : dist a v ≤ ‖a‖/2 := by
    have tri := dist_triangle a (deriv (reciprocalLimit j r) w) v
    rw [dist_comm (deriv _ w) a] at e1
    linarith
  have identity : 1 - v/a = (a-v)/a := by field_simp [a, simple]
  rw [show deriv (fun z ↦ (reciprocalRow j r d).eval₂ Complex.ofRealHom z) w = v from rfl,
    identity, norm_div]
  apply (div_le_iff₀ pos).mpr
  simpa only [dist_eq_norm, one_div_mul_eq_div] using step

#print axioms reciprocal_simple_zero_isolation


/-- Compact regions disjoint from the limiting zero set eventually contain no row zero. -/
theorem reciprocal_eventually_zero_free {j r : ℕ} (hj : 2 ≤ j) {K : Set ℂ}
    (compact : IsCompact K) (free : ∀ z ∈ K, reciprocalLimit j r z ≠ 0) :
    ∀ᶠ d : ℕ in atTop, ∀ z ∈ K, (reciprocalRow j r d).eval₂ Complex.ofRealHom z ≠ 0 := by
  rcases K.eq_empty_or_nonempty with empty | nonempty
  · simp [empty]
  obtain ⟨x, hx, minimal⟩ := compact.exists_isMinOn nonempty
    (reciprocal_limit_holomorphic hj r).continuous.norm.continuousOn
  have positive := norm_pos_iff.mpr (free x hx)
  have uniform := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
    (reciprocal_locally_uniform hj r) K (subset_univ _) compact
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp uniform _ positive] with d hd
  intro y hy bad
  have close := hd y hy
  rw [bad, dist_zero_right] at close
  exact (not_lt_of_ge (minimal hy)) close

private theorem eval_conj_real (p : Polynomial ℝ) (w : ℂ) :
    p.eval₂ Complex.ofRealHom (star w) = star (p.eval₂ Complex.ofRealHom w) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add, star_add, hp, hq]
  | monomial n a => simp [Polynomial.eval₂_monomial]

/-- Each isolated reciprocal zero at a simple real limiting zero is itself real, and
is the only complex zero in its isolating disk. -/
theorem reciprocal_real_simple_isolation {j r : ℕ} (hj : 2 ≤ j) {c : ℝ}
    (zero : reciprocalLimit j r c = 0) (simple : deriv (reciprocalLimit j r) c ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R ∈ Ioo 0 ε, ∀ᶠ d : ℕ in atTop, ∃ x : ℝ,
      (x : ℂ) ∈ closedBall (c : ℂ) R ∧ (reciprocalRow j r d).eval₂ Complex.ofRealHom x = 0 ∧
      deriv (fun w ↦ (reciprocalRow j r d).eval₂ Complex.ofRealHom w) x ≠ 0 ∧
      ∀ y ∈ closedBall (c : ℂ) R, (reciprocalRow j r d).eval₂ Complex.ofRealHom y = 0 →
        y = (x : ℂ) := by
  obtain ⟨R, hR, eventual⟩ := reciprocal_simple_zero_isolation hj zero simple hε
  refine ⟨R, hR, ?_⟩
  filter_upwards [eventual] with d hd
  obtain ⟨z, hz, fz, dz, unique⟩ := hd
  have conjmem : star z ∈ closedBall (c : ℂ) R := by
    rw [mem_closedBall, show dist (star z) (c : ℂ) = dist z (c : ℂ) by
      simpa using Complex.dist_conj_conj z (c : ℂ)]
    exact mem_closedBall.mp hz
  have root : (reciprocalRow j r d).eval₂ Complex.ofRealHom (star z) = 0 := by
    rw [eval_conj_real, fz, star_zero]
  obtain ⟨x, rfl⟩ := Complex.conj_eq_iff_real.mp (unique _ conjmem root)
  exact ⟨x, hz, fz, dz, unique⟩

#print axioms reciprocal_eventually_zero_free
#print axioms reciprocal_real_simple_isolation


/-- The reciprocal parametrization preserves the zero condition for the original
rank polynomial at every nonzero real parameter. -/
theorem reciprocal_zero_iff_original {j r d : ℕ} (hj : 2 ≤ j) (hr : r < j) (hd : 1 ≤ d)
    (x : ℝ) (nx : x ≠ 0) :
    (reciprocalRow j r d).eval₂ Complex.ofRealHom (x : ℂ) = 0 ↔
      (row (j*d+r) j).eval (reciprocalArgumentScale j d / x) = 0 := by
  have original := eval₂_reciprocalRow (S := ℝ) hj hr hd x nx
  have pos := reciprocalArgumentScale_pos j hd
  have pref : 0 < reciprocalPrefactor j r d := by
    have pd : 0 < (d : ℝ) := by exact_mod_cast hd
    have slope := edgeScale_pos j
    unfold reciprocalPrefactor
    positivity
  have cast : (reciprocalRow j r d).eval₂ Complex.ofRealHom (x : ℂ) =
      ((reciprocalRow j r d).eval x : ℝ) := by
    exact Polynomial.eval₂_at_apply (p := reciprocalRow j r d) Complex.ofRealHom x
  rw [cast, Complex.ofReal_eq_zero]
  simpa [Algebra.algebraMap_self, Polynomial.eval₂_id, pref.ne', nx, pos.ne'] using
    congrArg (fun v : ℝ ↦ v = 0) original |>.to_iff

/-- Every simple negative zero of the limiting function yields negative roots of
the original rows, arbitrarily close in the normalized reciprocal coordinate. -/
theorem original_negative_root_near_reciprocal_zero {j r : ℕ} (hj : 2 ≤ j) (hr : r < j)
    {c : ℝ} (hc : c < 0) (zero : reciprocalLimit j r c = 0)
    (simple : deriv (reciprocalLimit j r) c ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∃ x : ℝ, x < 0 ∧ dist x c < ε ∧
      (row (j*d+r) j).eval (reciprocalArgumentScale j d / x) = 0 := by
  obtain ⟨R, hR, event⟩ := reciprocal_real_simple_isolation hj zero simple
    (lt_min hε (neg_pos.mpr hc))
  filter_upwards [event, eventually_ge_atTop 1] with d ex hd
  obtain ⟨x, member, root, _⟩ := ex
  have near : dist x c < min ε (-c) := by
    have lift := (mem_closedBall.mp member).trans_lt hR.2
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at lift
    exact lift
  have neg : x < 0 := by
    have negdist := near.trans_le (min_le_right _ _)
    rw [Real.dist_eq, abs_lt] at negdist
    linarith [negdist.2]
  exact ⟨x, neg, near.trans_le (min_le_left _ _),
    (reciprocal_zero_iff_original hj hr hd x neg.ne).mp root⟩

#print axioms original_negative_root_near_reciprocal_zero

end OrderedPartitions.ReciprocalEdge
