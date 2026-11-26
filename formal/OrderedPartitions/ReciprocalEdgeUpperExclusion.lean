import OrderedPartitions.ReciprocalEdgeMultisections
import OrderedPartitions.ReciprocalEdgeRootTransfer
import Mathlib.Analysis.Complex.OpenMapping

/-! Passage from pairwise sector inequalities to reality of the zeros. -/
noncomputable section
namespace OrderedPartitions.ReciprocalEdge
open Filter Set Metric Complex
open scoped Topology

/-- A holomorphic germ taking values in the closed upper half-plane is locally zero
if it takes the value zero at an interior point. -/
private theorem flat_at_zero {g : ℂ→ℂ} {a : ℂ} (ha : AnalyticAt ℂ g a) (atA : g a=0)
    (half : ∀ᶠ w in 𝓝 a,0≤(g w).im) : ∀ᶠ w in 𝓝 a,g w=0 := by
  rcases ha.eventually_constant_or_nhds_le_map_nhds with constant|onto
  · simpa only [atA] using constant
  · have hh : {z : ℂ | 0≤z.im} ∈ map g (𝓝 a) := half
    have neigh := onto hh
    rw [atA] at neigh
    obtain ⟨r,rp,inside⟩ := Metric.mem_nhds_iff.mp neigh
    let z : ℂ := -((r/2:ℝ):ℂ)*I
    have rz : z∈ball (0:ℂ) r := by
      simpa [z,abs_of_pos rp] using half_lt_self rp
    have bad : 0≤z.im := inside rz
    simp [z] at bad
    linarith

private theorem section_nonzero_origin (j r : ℕ) : reciprocalLimit j r 0 ≠ 0 := by
  rw [reciprocalLimit,tsum_eq_single 0]
  · simp [Nat.factorial_ne_zero]
  · intro n hn
    simp [zero_pow hn]

private theorem ratio_im_nonneg {a b : ℂ} (h : 0≤(a*star b).im) :
    0≤(a/b).im := by
  rw [Complex.div_im]
  simp [Complex.mul_im] at h
  have n := Complex.normSq_nonneg b
  exact sub_nonneg.mpr (div_le_div_of_nonneg_right h n)

private theorem exclude_by_ratio {f g m : ℂ→ℂ} {a : ℂ} (hf : Differentiable ℂ f)
    (f0 : f 0≠0) (hg : AnalyticAt ℂ g a) (ga : g a≠0) (hm : AnalyticAt ℂ m a) (ma : m a≠0)
    (half : ∀ᶠ w in 𝓝 a,0≤((m w*f w)/g w).im) : f a≠0 := by
  intro zero
  have fa := hf.analyticAt a
  have ratio := (hm.mul fa).div hg ga
  have flat := flat_at_zero ratio (by simp [zero]) half
  have localEq : f =ᶠ[𝓝 a] (fun _ ↦ 0) := by
    filter_upwards [flat,hg.continuousAt.eventually_ne ga,hm.continuousAt.eventually_ne ma] with w hw gn mn
    change m w*f w/g w=0 at hw
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hw).resolve_right gn)).resolve_left mn
  have ident : f = fun _ ↦ 0 :=
    AnalyticOnNhd.eq_of_eventuallyEq (fun z _ ↦ hf.analyticAt z) (fun _ _ ↦ analyticAt_const) localEq
  exact f0 (congrFun ident 0)

/-- Any weakly preserving pairwise sector system for the limiting sections already
excludes every upper-half-plane zero of every section, including boundary rays of that system. -/
theorem no_upper_zeros_of_sectors {j : ℕ} (hj : 2≤j)
    (angles : ∀ w : ℂ, 0<w.im → ∀ i k : Fin j, i<k →
      0≤(reciprocalLimit j i w*star (reciprocalLimit j k w)).im ∧
      0≤(w*reciprocalLimit j k w*star (reciprocalLimit j i w)).im)
    (r : Fin j) {a : ℂ} (up : 0<a.im) : reciprocalLimit j r a≠0 := by
  obtain ⟨k,kn⟩ := sections_have_no_common_zero (by omega : 1≤j) a
  have hu : ∀ᶠ w in 𝓝 a,0<w.im := Complex.continuous_im.continuousAt.eventually_const_lt up
  rcases lt_trichotomy r k with lt|eq|gt
  · apply exclude_by_ratio (m:=fun _ ↦ 1) (reciprocal_limit_holomorphic hj r) (section_nonzero_origin j r)
      ((reciprocal_limit_holomorphic hj k).analyticAt a) kn analyticAt_const one_ne_zero
    exact hu.mono (fun w wu ↦ by simpa using ratio_im_nonneg (angles w wu r k lt).1)
  · simpa only [eq] using kn
  · have an : a≠0 := fun h ↦ up.ne' (by simp [h])
    apply exclude_by_ratio (m:=id) (reciprocal_limit_holomorphic hj r) (section_nonzero_origin j r)
      ((reciprocal_limit_holomorphic hj k).analyticAt a) kn analyticAt_id an
    exact hu.mono (fun w wu ↦ ratio_im_nonneg (angles w wu k r gt).2)


theorem section_conj (j r : ℕ) (w : ℂ) : reciprocalLimit j r (star w)=star (reciprocalLimit j r w) := by
  simp [reciprocalLimit,tsum_star]

theorem section_positive {j : ℕ} (hj : 1≤j) (r : ℕ) {x : ℝ} (hx : 0≤x) :
    0<(reciprocalLimit j r x).re := by
  let term := fun n : ℕ ↦ x^n/((r+j*n).factorial:ℝ)
  have sum : Summable term := by
    refine (Real.summable_pow_div_factorial x).of_nonneg_of_le (fun n ↦ by dsimp [term];positivity) ?_
    intro n
    have le : n≤r+j*n := by have h := Nat.mul_le_mul_right n hj; simpa using h.trans (Nat.le_add_left _ _)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast Nat.factorial_le le)
  have v : reciprocalLimit j r x=((∑' n,term n):ℝ) := by
    rw [reciprocalLimit,Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simp [term,div_eq_mul_inv,mul_comm]
  rw [v,Complex.ofReal_re]
  have low := sum.le_tsum 0 (fun n _ ↦ by dsimp [term];positivity)
  have z : 0<term 0 := by dsimp [term];positivity
  exact z.trans_le low

/-- The sector inequalities force every limiting zero to be a strictly negative real. -/
theorem negative_zeros_of_sectors {j : ℕ} (hj : 2≤j)
    (angles : ∀ w : ℂ, 0<w.im → ∀ i k : Fin j, i<k →
      0≤(reciprocalLimit j i w*star (reciprocalLimit j k w)).im ∧
      0≤(w*reciprocalLimit j k w*star (reciprocalLimit j i w)).im)
    (r : Fin j) {w : ℂ} (zero : reciprocalLimit j r w=0) : w.im=0 ∧ w.re<0 := by
  have realw : w.im=0 := by
    rcases lt_trichotomy w.im 0 with neg|eq|pos
    · have bad := no_upper_zeros_of_sectors hj angles r (a:=star w) (by simpa using neg)
      exact (bad (by rw [section_conj,zero,star_zero])).elim
    · exact eq
    · exact (no_upper_zeros_of_sectors hj angles r pos zero).elim
  refine ⟨realw,?_⟩
  by_contra! nonneg
  have eq : (w.re:ℂ)=w := by apply Complex.ext <;> simp [realw]
  have pos := section_positive (by omega : 1≤j) r nonneg
  rw [eq,zero] at pos
  exact (lt_irrefl _ pos)

#print axioms section_positive
#print axioms negative_zeros_of_sectors
#print axioms no_upper_zeros_of_sectors
end OrderedPartitions.ReciprocalEdge
