import OrderedPartitions.ReciprocalEdgeFirstCorrectionDrift
import OrderedPartitions.ReciprocalEdgeAllLimitZeros
import OrderedPartitions.ReciprocalEdgeLadderPrefix

/-! Identify the same-residue drift with the actual ordered outer roots. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open Filter Metric Set
open scoped Topology

private theorem outer_prefix_unique {j r d k : ℕ} {ρ ε δ : ℝ} {c t u : Fin k → ℝ}
    (a : OriginalOuterPrefix j r d ρ ε c t) (b : OriginalOuterPrefix j r d ρ δ c u) : t = u := by
  classical
  have subset {η ζ : ℝ} {x y : Fin k → ℝ}
      (hx : OriginalOuterPrefix j r d ρ η c x) (hy : OriginalOuterPrefix j r d ρ ζ c y) :
      range x ⊆ range y := by
    rintro _ ⟨i, rfl⟩
    by_contra bad
    have other (p : Fin k) : (x i:ℂ) ≠ (y p:ℂ) := fun e ↦
      bad ⟨p, (Complex.ofReal_inj.mp e).symm⟩
    exact (not_lt_of_ge (hx.selected i).le) (hy.remaining _ (hx.zero i) other)
  exact (a.ordered.range_inj b.ordered).mp (Subset.antisymm (subset a b) (subset b a))

/-- The two-term expansion and strict same-residue motion of an indexed original root. -/
structure OuterRootDrift (j r : ℕ) (c : ℝ) (t : ℕ → ℝ) : Prop where
  second_term :
    Tendsto (fun d : ℕ ↦ (t d-(originalScaleConstant j/c)*(d:ℝ)^j)/(d:ℝ)^(j-1))
      atTop (𝓝 (originalScaleConstant j *
        (reciprocalCorrection j r (c:ℂ)/deriv (reciprocalLimit j r) (c:ℂ)).re/c^2))
  increment :
    Tendsto (fun d : ℕ ↦ (t (d+1)-t d)/(d:ℝ)^(j-1))
      atTop (𝓝 ((j:ℝ)*(originalScaleConstant j/c)))
  leftward : ∀ᶠ d : ℕ in atTop, t (d+1) < t d

/-- The unique modulus-selected prefix is coherent in the requested accuracy.
Its individual roots therefore have the correction and drift along the same residue. -/
theorem outer_prefix_drift {j r k : ℕ} (hj : 2 ≤ j) (hr : r < j) {ρ : ℝ}
    {c : Fin k → ℝ} (lim : LimitPrefix j r ρ c) :
    ∃ t : ℕ → Fin k → ℝ,
      (∀ ε>0, ∀ᶠ d : ℕ in atTop, OriginalOuterPrefix j r d ρ ε c (t d)) ∧
      ∀ i, OuterRootDrift j r (c i) (fun d ↦ t d i) := by
  classical
  let t (d : ℕ) : Fin k → ℝ :=
    if a : ∃ u, OriginalOuterPrefix j r d ρ 1 c u then a.choose else c
  have levels (ε : ℝ) (he : 0 < ε) :
      ∀ᶠ d : ℕ in atTop, OriginalOuterPrefix j r d ρ ε c (t d) := by
    filter_upwards [eventually_original_outer_prefix hj hr lim (by norm_num : 0<(1:ℝ)),
      eventually_original_outer_prefix hj hr lim he] with d a b
    obtain ⟨u, co⟩ := b
    have eq := outer_prefix_unique a.choose_spec co
    simpa only [t, dif_pos a, eq] using co
  refine ⟨t, levels, fun i ↦ ?_⟩
  let x (d : ℕ) := reciprocalArgumentScale j d/(t d i)
  have valid := levels 1 (by norm_num)
  have xlim : Tendsto x atTop (𝓝 (c i)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    exact (levels ε ep).mono (fun d a ↦ a.near i)
  have inverted : ∀ᶠ d : ℕ in atTop, reciprocalArgumentScale j d/x d = t d i := by
    filter_upwards [valid, eventually_ge_atTop 1] with d a hd
    exact scaled_inverse_involutive (reciprocalArgumentScale_pos j hd).ne' (a.negative i).ne
  have xroot : ∀ᶠ d : ℕ in atTop, reciprocalValue j r d (x d:ℂ) = 0 := by
    filter_upwards [valid, inverted, eventually_ge_atTop 1] with d a inv hd
    have zn : x d ≠ 0 := div_ne_zero (reciprocalArgumentScale_pos j hd).ne' (a.negative i).ne
    apply (reciprocal_zero_iff_original_complex hj hr hd (Complex.ofReal_ne_zero.mpr zn)).mpr
    rw [← Complex.ofReal_div, inv]
    exact a.zero i
  have ci := (lim.inside i).2
  have expansion :
      Tendsto (fun d : ℕ ↦ (t d i-(originalScaleConstant j/c i)*(d:ℝ)^j)/(d:ℝ)^(j-1))
        atTop (𝓝 (originalScaleConstant j *
          (reciprocalCorrection j r (c i:ℂ)/deriv (reciprocalLimit j r) (c i:ℂ)).re/(c i)^2)) := by
    apply (original_two_term_limit hj ci (lim.zero i) (lim.simple i) xlim xroot).congr'
    filter_upwards [inverted] with d inv
    rw [inv]
  have drift := increment_of_two_terms (by omega : 1≤j) expansion
  refine ⟨expansion, drift, ?_⟩
  have scale : 0 < originalScaleConstant j := by
    have b := edgeScale_pos j
    unfold originalScaleConstant
    positivity
  have neg : (j:ℝ)*(originalScaleConstant j/c i) < 0 :=
    mul_neg_of_pos_of_neg (by exact_mod_cast (by omega : 0<j)) (div_neg_of_pos_of_neg scale ci)
  filter_upwards [drift.eventually_lt_const neg, eventually_ge_atTop 1] with d v hd
  have dp : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  exact sub_neg.mp (by simpa only [zero_mul] using (div_lt_iff₀ (pow_pos dp (j-1))).mp v)

/-- For every cutoff and every fixed prefix length, all residues have actual
largest-modulus root arrays and the stated same-residue first-order drift. -/
theorem all_residue_outer_drift {j : ℕ} (hj : 2 ≤ j) (k : ℕ) :
    ∃ L : Fin j → ℕ → ℝ, ReciprocalSector.ZeroLadder j L ∧
      ∀ r : Fin j, ∃ t : ℕ → Fin k → ℝ,
        (∀ ε>0, ∀ᶠ d : ℕ in atTop,
          OriginalOuterPrefix j r d (ReciprocalSector.prefixRadius L r k) ε
            (fun i : Fin k ↦ -L r i) (t d)) ∧
        ∀ i : Fin k, OuterRootDrift j r (-L r i) (fun d ↦ t d i) := by
  obtain ⟨L, roots⟩ := ReciprocalSector.all_limit_zeros hj
  exact ⟨L, roots, fun r ↦ outer_prefix_drift hj r.isLt (roots.limit_prefix r k)⟩

#print axioms outer_prefix_drift
#print axioms all_residue_outer_drift

end OrderedPartitions.ReciprocalEdge
