import OrderedPartitions.ReciprocalEdgeOuterPrefixInverse

/-! Eventual transfer of a complete finite prefix of limiting zeros to the original row. -/

noncomputable section

namespace OrderedPartitions.ReciprocalEdge

open Filter Metric Set
open scoped Topology

/-- All complex zeros in the closed disk are accounted for by the listed simple
negative zeros, starting with the least modulus. -/
structure LimitPrefix (j r : ℕ) (ρ : ℝ) {k : ℕ} (c : Fin k → ℝ) : Prop where
  radius_pos : 0 < ρ
  ordered : StrictAnti c
  inside : ∀ i, c i ∈ Ioo (-ρ) 0
  zero : ∀ i, reciprocalLimit j r (c i : ℂ) = 0
  simple : ∀ i, deriv (reciprocalLimit j r) (c i : ℂ) ≠ 0
  complete : ∀ w ∈ closedBall (0 : ℂ) ρ, reciprocalLimit j r w = 0 →
    ∃ i, w = (c i : ℂ)

private theorem shared_tolerance {j r k : ℕ} {ρ ε : ℝ} {c : Fin k → ℝ}
    (lim : LimitPrefix j r ρ c) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      (∀ i, δ < -c i ∧ δ < ρ+c i) ∧
      (∀ i j : Fin k, i < j → δ+δ < c i-c j) := by
  let l := 𝓝[>] (0 : ℝ)
  have nt : l.NeBot := nhdsGT_neBot _
  have positive : ∀ᶠ δ in l, 0 < δ := eventually_mem_nhdsWithin
  have small : ∀ᶠ δ in l, δ < ε := nhdsWithin_le_nhds (gt_mem_nhds hε)
  have inside (i : Fin k) : ∀ᶠ δ in l, δ < -c i ∧ δ < ρ+c i := by
    obtain ⟨lb, ub⟩ := lim.inside i
    exact nhdsWithin_le_nhds ((gt_mem_nhds (neg_pos.mpr ub)).and
      (gt_mem_nhds (show 0 < ρ+c i by linarith)))
  have sep (i j : Fin k) : ∀ᶠ δ in l, i < j → δ+δ < c i-c j := by
    by_cases lt : i < j
    · have pos : 0 < (c i-c j)/2 := half_pos (sub_pos.mpr (lim.ordered lt))
      have near : ∀ᶠ δ in l, δ < (c i-c j)/2 := nhdsWithin_le_nhds (gt_mem_nhds pos)
      exact near.mono fun δ h _ ↦ by linarith
    · exact .of_forall fun _ h ↦ (lt h).elim
  exact (positive.and (small.and ((eventually_all.mpr inside).and
    (eventually_all.mpr fun i ↦ eventually_all.mpr (sep i))))).exists

/-- The reciprocal row has exactly the listed real zeros inside the closed disk,
with simple zeros and proximity to the respective limiting centers. -/
structure RowDiskPrefix (j r d : ℕ) (ρ ε : ℝ) {k : ℕ} (c x : Fin k → ℝ) : Prop where
  ordered : StrictAnti x
  inside : ∀ i, x i ∈ Ioo (-ρ) 0
  near : ∀ i, dist (x i) (c i) < ε
  zero : ∀ i, reciprocalValue j r d (x i : ℂ) = 0
  simple : ∀ i, deriv (reciprocalValue j r d) (x i : ℂ) ≠ 0
  complete : ∀ w ∈ closedBall (0 : ℂ) ρ, reciprocalValue j r d w = 0 →
    ∃ i, w = (x i : ℂ)

theorem eventually_row_disk_prefix {j r k : ℕ} (hj : 2 ≤ j) {ρ ε : ℝ} {c : Fin k → ℝ}
    (lim : LimitPrefix j r ρ c) (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∃ x, RowDiskPrefix j r d ρ ε c x := by
  obtain ⟨δ, dp, dsmall, dinside, dsep⟩ := shared_tolerance lim hε
  choose R rsmall evt using fun i : Fin k ↦
    reciprocal_real_simple_isolation hj (lim.zero i) (lim.simple i) dp
  let K := closedBall (0 : ℂ) ρ \ ⋃ i : Fin k, ball (c i : ℂ) (R i)
  have compact : IsCompact K := (isCompact_closedBall _ _).diff (isOpen_iUnion fun _ ↦ isOpen_ball)
  have free : ∀ w ∈ K, reciprocalLimit j r w ≠ 0 := by
    intro w hw zero
    obtain ⟨i, rfl⟩ := lim.complete w hw.1 zero
    exact hw.2 (mem_iUnion.mpr ⟨i, mem_ball_self (rsmall i).1⟩)
  filter_upwards [eventually_all.mpr evt, reciprocal_eventually_zero_free hj compact free]
    with d roots empty
  choose x hx data using roots
  have distance (i : Fin k) : dist (x i) (c i) < δ := by
    have z := (mem_closedBall.mp (hx i)).trans_lt (rsmall i).2
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at z
    simpa only [Real.dist_eq] using z
  have displacement (i : Fin k) : -δ < x i-c i ∧ x i-c i < δ := by
    simpa only [Real.dist_eq, abs_lt] using distance i
  refine ⟨x, ⟨?_, ?_, fun i ↦ (distance i).trans dsmall, fun i ↦ (data i).1,
    fun i ↦ (data i).2.1, ?_⟩⟩
  · intro i j ij
    linarith only [dsep i j ij, (displacement i).1, (displacement j).2]
  · intro i
    exact ⟨by linarith only [(dinside i).2, (displacement i).1],
      by linarith only [(dinside i).1, (displacement i).2]⟩
  · intro w hw root
    have member : w ∈ ⋃ i : Fin k, ball (c i : ℂ) (R i) := by
      by_contra off
      exact empty w (show w ∈ K from ⟨hw, off⟩) root
    obtain ⟨i, hi⟩ := mem_iUnion.mp member
    exact ⟨i, (data i).2.2 w (ball_subset_closedBall hi) root⟩

/-- The selected original roots are ordered by strictly decreasing modulus.
Every other complex root has modulus strictly below the stated cutoff. -/
structure OriginalOuterPrefix (j r d : ℕ) (ρ ε : ℝ) {k : ℕ}
    (c t : Fin k → ℝ) : Prop where
  ordered : StrictMono t
  negative : ∀ i, t i < 0
  modulus_ordered : StrictAnti (fun i ↦ ‖(t i : ℂ)‖)
  near : ∀ i, dist (reciprocalArgumentScale j d / t i) (c i) < ε
  zero : ∀ i, originalValue j r d (t i : ℂ) = 0
  simple : ∀ i, deriv (originalValue j r d) (t i : ℂ) ≠ 0
  selected : ∀ i, reciprocalArgumentScale j d / ρ < ‖(t i : ℂ)‖
  remaining : ∀ z : ℂ, originalValue j r d z = 0 → (∀ i, z ≠ (t i : ℂ)) →
    ‖z‖ < reciprocalArgumentScale j d / ρ

private theorem disk_to_original {j r d k : ℕ} (hj : 2 ≤ j) (hr : r < j) (hd : 1 ≤ d)
    {ρ ε : ℝ} (hρ : 0 < ρ) {c x : Fin k → ℝ} (p : RowDiskPrefix j r d ρ ε c x) :
    ∃ t, OriginalOuterPrefix j r d ρ ε c t := by
  let S := reciprocalArgumentScale j d
  let t := fun i ↦ S/x i
  have Sp : 0 < S := reciprocalArgumentScale_pos j hd
  have Sc : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Sp.ne'
  have xp (i : Fin k) : x i < 0 := (p.inside i).2
  have tp (i : Fin k) : t i < 0 := div_neg_of_pos_of_neg Sp (xp i)
  have increasing : StrictMono t := fun i _ ij ↦ scaled_inverse_lt Sp (p.ordered ij) (xp i)
  have cast_t (i : Fin k) : (t i : ℂ) = (S : ℂ)/(x i : ℂ) := Complex.ofReal_div _ _
  have original (i : Fin k) :
      originalValue j r d (t i : ℂ) = 0 ∧ deriv (originalValue j r d) (t i : ℂ) ≠ 0 := by
    rw [cast_t]
    exact original_simple_of_reciprocal hj hr hd
      (Complex.ofReal_ne_zero.mpr (xp i).ne) (p.zero i) (p.simple i)
  refine ⟨t, ⟨increasing, tp, ?_, ?_, fun i ↦ (original i).1, fun i ↦ (original i).2, ?_, ?_⟩⟩
  · intro i j ij
    change ‖(t j : ℂ)‖ < ‖(t i : ℂ)‖
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_neg (tp i), abs_of_neg (tp j)]
    exact neg_lt_neg (increasing ij)
  · intro i
    change dist (S/(S/x i)) (c i) < ε
    rw [scaled_inverse_involutive Sp.ne' (xp i).ne]
    exact p.near i
  · intro i
    rw [cast_t, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Sp, abs_of_neg (xp i)]
    apply (div_lt_div_iff₀ hρ (neg_pos.mpr (xp i))).mpr
    exact mul_lt_mul_of_pos_left (by linarith [(p.inside i).1]) Sp
  · intro z zero other
    by_contra! above
    have zn : z ≠ 0 := by
      intro eq
      rw [eq, norm_zero] at above
      exact (div_pos Sp hρ).not_ge above
    let w := (S : ℂ)/z
    have wn : w ≠ 0 := div_ne_zero Sc zn
    have cut : (S : ℂ)/w = z := scaled_inverse_involutive Sc zn
    have in_disk : w ∈ closedBall (0 : ℂ) ρ := by
      rw [mem_closedBall, dist_zero_right]
      exact (reciprocal_norm_cutoff Sp hρ zn).mpr above
    have wroot : reciprocalValue j r d w = 0 :=
      (reciprocal_zero_iff_original_complex hj hr hd wn).mpr (cut ▸ zero)
    obtain ⟨i, wi⟩ := p.complete w in_disk wroot
    exact other i (by rw [cast_t, ← wi, cut])

/-- A complete disk of simple negative limiting zeros selects precisely the
corresponding simple negative roots of largest modulus in the original row. -/
theorem eventually_original_outer_prefix {j r k : ℕ} (hj : 2 ≤ j) (hr : r < j)
    {ρ ε : ℝ} {c : Fin k → ℝ} (lim : LimitPrefix j r ρ c) (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∃ t, OriginalOuterPrefix j r d ρ ε c t := by
  filter_upwards [eventually_row_disk_prefix hj lim hε, eventually_ge_atTop 1]
    with d near hd
  obtain ⟨x, cert⟩ := near
  exact disk_to_original hj hr hd lim.radius_pos cert

#print axioms eventually_row_disk_prefix
#print axioms eventually_original_outer_prefix

end OrderedPartitions.ReciprocalEdge
