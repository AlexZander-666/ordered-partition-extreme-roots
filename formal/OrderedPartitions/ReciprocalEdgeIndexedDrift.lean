import OrderedPartitions.ReciprocalEdgeAllFirstCorrection
import OrderedPartitions.ReciprocalEdgeFirstCorrectionPrefix

/-! Comparison of the indexed extreme roots in any fixed finite window of actual rows. -/
noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Filter OrderedPartitions.ReciprocalEdge
open scoped Topology

private theorem scaleConstant_pos (j : ℕ) : 0 < originalScaleConstant j := by
  have hb := edgeScale_pos j
  unfold originalScaleConstant
  positivity

theorem OriginalAsymptoticPrefix.indexed_drift {j k : ℕ} (hj : 2 ≤ j)
    {L : Fin j → ℕ → ℝ} {t : ℕ → Fin j → Fin k → ℝ}
    (ladder : ZeroLadder j L) (h : OriginalAsymptoticPrefix L t) (r : Fin j) (i : Fin k) :
    Tendsto (fun d : ℕ ↦ (t (d+1) r i - t d r i)/(d:ℝ)^(j-1)) atTop
      (𝓝 ((j:ℝ)*(originalScaleConstant j/(-L r i)))) ∧
    ∀ᶠ d : ℕ in atTop, t (d+1) r i < t d r i := by
  obtain ⟨u,uc,ud⟩ := outer_prefix_drift hj r.isLt (ladder.limit_prefix r k)
  have eq : ∀ᶠ d : ℕ in atTop, t d r = u d := by
    filter_upwards [h.certified 1 one_pos,uc 1 one_pos] with d both single
    exact original_prefix_unique (both r) single
  have nextEq : ∀ᶠ d : ℕ in atTop, t (d+1) r = u (d+1) :=
    (tendsto_add_atTop_nat 1).eventually eq
  refine ⟨(ud i).increment.congr' ?_,?_⟩
  · filter_upwards [eq,nextEq] with d same later
    rw [same,later]
  · filter_upwards [eq,nextEq,(ud i).leftward] with d same later lt
    simpa only [same,later] using lt

private theorem shifted_scale (j a : ℕ) : Tendsto
    (fun d : ℕ ↦ reciprocalArgumentScale j (d+a)/reciprocalArgumentScale j d) atTop (𝓝 1) := by
  have lim := ((Kernel.cutoff_inv_limit (J:=id) tendsto_id).const_mul (a:ℝ)).const_add 1
  simp only [mul_zero,add_zero,id_eq] at lim
  have h := lim.pow j
  simp only [one_pow] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have nz : (d:ℝ)≠0 := by exact_mod_cast (by omega : d≠0)
  simp only [reciprocalArgumentScale_factor,Nat.cast_add]
  rw [mul_div_mul_left _ _ (scaleConstant_pos j).ne',← div_pow]
  congr 1
  field_simp [nz]

theorem OriginalAsymptoticPrefix.shifted_limit {j k : ℕ}
    {L : Fin j → ℕ → ℝ} {t : ℕ → Fin j → Fin k → ℝ}
    (h : OriginalAsymptoticPrefix L t) (r : Fin j) (i : Fin k) (a : ℕ) :
    Tendsto (fun d : ℕ ↦ t (d+a) r i / reciprocalArgumentScale j d) atTop (𝓝 (1/(-L r i))) := by
  have res := ((h.original r i).comp (tendsto_add_atTop_nat a)).mul (shifted_scale j a)
  rw [mul_one] at res
  apply res.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have nz := (reciprocalArgumentScale_pos j (by omega : 1≤d+a)).ne'
  change t (d+a) r i / reciprocalArgumentScale j (d+a) *
    (reciprocalArgumentScale j (d+a)/reciprocalArgumentScale j d) = _
  field_simp

/-- In different ladder positions the limiting magnitudes determine the order, for
arbitrary fixed shifts of the two ranks. -/
theorem OriginalAsymptoticPrefix.compare_centers {j k : ℕ}
    {L : Fin j → ℕ → ℝ} {t : ℕ → Fin j → Fin k → ℝ}
    (ladder : ZeroLadder j L) (h : OriginalAsymptoticPrefix L t)
    {r s : Fin j} {i v : Fin k} (order : L r i < L s v) (a b : ℕ) :
    ∀ᶠ d : ℕ in atTop, t (d+a) r i < t (d+b) s v := by
  have lo : 1/(-L r i)<1/(-L s v) := by
    simp only [div_neg]
    exact neg_lt_neg ((one_div_lt_one_div_of_lt (ladder.positive r i) order))
  filter_upwards [((h.shifted_limit r i a).eventually_lt (h.shifted_limit s v b) lo),
    eventually_ge_atTop 1] with d hd hd1
  exact (div_lt_div_iff_of_pos_right (reciprocalArgumentScale_pos j hd1)).mp hd

/-- Coincident ladder positions are ordered by rank, with the larger rank on the left. -/
theorem OriginalAsymptoticPrefix.compare_same {j k : ℕ} (hj : 2 ≤ j)
    {L : Fin j → ℕ → ℝ} {t : ℕ → Fin j → Fin k → ℝ}
    (ladder : ZeroLadder j L) (h : OriginalAsymptoticPrefix L t)
    (r : Fin j) (i : Fin k) {a b : ℕ} (ba : b<a) :
    ∀ᶠ d : ℕ in atTop, t (d+a) r i<t (d+b) r i := by
  obtain ⟨d₀,h₀⟩ := eventually_atTop.mp ((h.indexed_drift hj ladder r i).2)
  filter_upwards [eventually_ge_atTop d₀] with d hd
  obtain ⟨v,e⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt ba)
  rw [e]
  clear e ba a
  induction v with
  | zero => simpa only [Nat.add_zero,Nat.add_succ] using h₀ (d+b) (by omega)
  | succ v ih =>
    rw [Nat.add_succ,Nat.add_succ]
    exact (h₀ _ (by omega)).trans ih

#print axioms OriginalAsymptoticPrefix.indexed_drift
#print axioms OriginalAsymptoticPrefix.compare_centers
#print axioms OriginalAsymptoticPrefix.compare_same
end OrderedPartitions.ReciprocalSector
