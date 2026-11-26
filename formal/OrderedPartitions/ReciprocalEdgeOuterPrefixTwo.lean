import OrderedPartitions.ReciprocalEdgeOuterPrefix
import OrderedPartitions.ReciprocalEdgeTrigonometric
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! The complete complex-zero disk hypothesis holds at threshold two in both parities. -/

noncomputable section

namespace OrderedPartitions.ReciprocalEdge

open Filter Metric Set
open scoped Topology

/-- The positive cosine or sine angle for the requested parity and index. -/
def twoAngle (r k : ℕ) : ℝ := ((k:ℝ)+((r:ℝ)+1)/2)*Real.pi

def twoCenter (r k : ℕ) : ℝ := -(twoAngle r k)^2

/-- An explicit disk radius between the last selected zero and the next one. -/
def twoRadius (r k : ℕ) : ℝ := ((((k:ℝ)+((r:ℝ)+1)/2-1/4)*Real.pi)^2)

private theorem twoAngle_pos (r k : ℕ) : 0 < twoAngle r k := by
  unfold twoAngle
  positivity

private theorem twoAngle_strictMono (r : ℕ) : StrictMono (twoAngle r) := by
  intro a b h
  unfold twoAngle
  have lt : (a:ℝ) < b := by exact_mod_cast h
  exact mul_lt_mul_of_pos_right (by linarith only [lt]) Real.pi_pos

private theorem twoCenter_strictAnti (r : ℕ) : StrictAnti (twoCenter r) := by
  intro a b hb
  unfold twoCenter
  exact neg_lt_neg (pow_lt_pow_left₀ (twoAngle_strictMono r hb) (twoAngle_pos r a).le
    (by decide : (2:ℕ) ≠ 0))

private theorem twoCenter_simple {r : ℕ} (hr : r < 2) (k : ℕ) :
    reciprocalLimit 2 r (twoCenter r k : ℂ) = 0 ∧
      deriv (reciprocalLimit 2 r) (twoCenter r k : ℂ) ≠ 0 := by
  have cast_center : (twoCenter r k : ℂ) = -((twoAngle r k : ℂ)^2) := by
    simp [twoCenter]
  rw [cast_center]
  rcases (show r=0 ∨ r=1 by omega) with rfl|rfl
  · apply even_simple_zero
    rw [← Complex.ofReal_cos, Complex.ofReal_eq_zero]
    rw [show twoAngle 0 k = Real.pi/2+k*Real.pi by
      simp only [twoAngle, Nat.cast_zero]; ring]
    simp [Real.cos_add_nat_mul_pi, Real.cos_pi_div_two]
  · apply odd_simple_zero _ (Complex.ofReal_ne_zero.mpr (twoAngle_pos 1 k).ne')
    rw [← Complex.ofReal_sin, Complex.ofReal_eq_zero]
    rw [show twoAngle 1 k = ((k+1:ℕ):ℝ)*Real.pi by
      simp only [twoAngle, Nat.cast_one, Nat.cast_add]; ring]
    exact Real.sin_nat_mul_pi _

private theorem odd_origin : reciprocalLimit 2 1 (0:ℂ) = 1 := by
  unfold reciprocalLimit
  rw [tsum_eq_single 0]
  · norm_num
  · intro h hz
    simp [zero_pow hz]

private theorem cos_square_index {y : ℂ} (zero : Complex.cos y = 0) :
    ∃ k : ℕ, -(y^2) = (twoCenter 0 k : ℂ) := by
  obtain ⟨m, eq⟩ := Complex.cos_eq_zero_iff.mp zero
  by_cases hs : 0 ≤ m
  · let k := m.toNat
    have cast_k : (k:ℝ) = (m:ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hs)
    have form : y = (twoAngle 0 k : ℂ) := by
      rw [eq, twoAngle, cast_k]
      push_cast
      ring
    exact ⟨k, by rw [form]; simp [twoCenter]⟩
  · let k := (-m-1).toNat
    have cast_k : (k:ℝ) = ((-m-1 : ℤ):ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ -m-1))
    have form : y = -(twoAngle 0 k : ℂ) := by
      rw [eq, twoAngle, cast_k]
      push_cast
      ring
    exact ⟨k, by rw [form, neg_sq]; simp [twoCenter]⟩

private theorem sin_square_index {y : ℂ} (yn : y ≠ 0) (zero : Complex.sin y = 0) :
    ∃ k : ℕ, -(y^2) = (twoCenter 1 k : ℂ) := by
  obtain ⟨m, eq⟩ := Complex.sin_eq_zero_iff.mp zero
  have m0 : m ≠ 0 := fun hz ↦ yn (by simp [eq, hz])
  by_cases hs : 0 ≤ m
  · let k := (m-1).toNat
    have cast_k : (k:ℝ) = ((m-1 : ℤ):ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ m-1))
    have form : y = (twoAngle 1 k : ℂ) := by
      rw [eq, twoAngle, cast_k]
      push_cast
      ring
    exact ⟨k, by rw [form]; simp [twoCenter]⟩
  · let k := (-m-1).toNat
    have cast_k : (k:ℝ) = ((-m-1 : ℤ):ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ -m-1))
    have form : y = -(twoAngle 1 k : ℂ) := by
      rw [eq, twoAngle, cast_k]
      push_cast
      ring
    exact ⟨k, by rw [form, neg_sq]; simp [twoCenter]⟩

/-- Complete classification of the complex zeros in both threshold-two limits. -/
theorem two_limit_zeros {r : ℕ} (hr : r < 2) (w : ℂ) :
    reciprocalLimit 2 r w = 0 ↔ ∃ k : ℕ, w = (twoCenter r k : ℂ) := by
  constructor
  · intro zero
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (-w) (n := 2) (by decide)
    have form : w = -(y^2) := by rw [hy, neg_neg]
    rw [form] at zero ⊢
    rcases (show r=0 ∨ r=1 by omega) with rfl|rfl
    · exact cos_square_index ((even_limit_cos y).symm.trans zero)
    · have yn : y ≠ 0 := by
        intro eq
        simp only [eq, zero_pow (by decide : (2:ℕ) ≠ 0), neg_zero, odd_origin] at zero
        exact one_ne_zero zero
      apply sin_square_index yn
      rw [← odd_limit_sin y, zero, mul_zero]
  · rintro ⟨k, rfl⟩
    exact (twoCenter_simple hr k).1

theorem two_limit_prefix {r : ℕ} (hr : r < 2) (k : ℕ) :
    LimitPrefix 2 r (twoRadius r k) (fun i : Fin k ↦ twoCenter r i.val) := by
  let α := ((k:ℝ)+((r:ℝ)+1)/2-1/4)*Real.pi
  have αp : 0 < α := by
    dsimp [α]
    apply mul_pos _ Real.pi_pos
    linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) r]
  have inside (i : Fin k) : twoAngle r i.val < α := by
    have one : (i.val:ℝ)+1 ≤ k := by exact_mod_cast i.isLt
    unfold twoAngle
    apply mul_lt_mul_of_pos_right _ Real.pi_pos
    linarith [one]
  refine ⟨sq_pos_of_pos αp, fun _ _ h ↦ twoCenter_strictAnti r h, ?_,
    fun i ↦ (twoCenter_simple hr i.val).1, fun i ↦ (twoCenter_simple hr i.val).2, ?_⟩
  · intro i
    exact ⟨neg_lt_neg (pow_lt_pow_left₀ (inside i) (twoAngle_pos r i.val).le
      (by decide)), neg_neg_of_pos (sq_pos_of_pos (twoAngle_pos r i.val))⟩
  · intro w hw root
    obtain ⟨m, eq⟩ := (two_limit_zeros hr w).mp root
    by_cases below : m < k
    · exact ⟨⟨m,below⟩, eq⟩
    · have h : α < twoAngle r m := by
        have order : (k:ℝ) ≤ m := by exact_mod_cast (Nat.le_of_not_gt below)
        unfold twoAngle
        apply mul_lt_mul_of_pos_right _ Real.pi_pos
        linarith [order]
      have hw' := mem_closedBall.mp hw
      rw [dist_zero_right, eq, Complex.norm_real, Real.norm_eq_abs, twoCenter,
        abs_of_nonpos (neg_nonpos.mpr (sq_nonneg _)), neg_neg] at hw'
      exact ((pow_lt_pow_left₀ h αp.le (by decide : (2:ℕ) ≠ 0)).not_ge hw').elim

/-- Every finite prefix of the ordered largest-modulus roots at threshold two,
for either parity, converges in reciprocal coordinates to its explicit constants. -/
theorem eventually_two_outer_prefix {r : ℕ} (hr : r < 2) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∃ t : Fin k → ℝ,
      OriginalOuterPrefix 2 r d (twoRadius r k) ε (fun i ↦ twoCenter r i.val) t :=
  eventually_original_outer_prefix (by decide) hr (two_limit_prefix hr k) hε

#print axioms two_limit_zeros
#print axioms two_limit_prefix
#print axioms eventually_two_outer_prefix

end OrderedPartitions.ReciprocalEdge
