import OrderedPartitions.ReciprocalEdgeIndexedDrift

/-! For every fixed window and prefix size, compare the actual extreme roots
from each pair of rows, including pairs in the same residue class. -/

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Filter OrderedPartitions.ReciprocalEdge
open scoped Topology

/-- From the far left the two length-k lists start with p, and alternate strictly. -/
structure AlternatingPrefix {k : ℕ} (p q : Fin k → ℝ) : Prop where
  aligned : ∀ i, p i < q i
  separated : ∀ i v, i < v → q i < p v

theorem OriginalAsymptoticPrefix.alternating {j k : ℕ} (hj : 2≤j)
    {L : Fin j → ℕ → ℝ} {t : ℕ → Fin j → Fin k → ℝ}
    (ladder : ZeroLadder j L) (h : OriginalAsymptoticPrefix L t)
    (a b : ℕ) (r s : Fin j) (orientation : r<s ∨ (r=s ∧ b<a)) :
    ∀ᶠ d : ℕ in atTop, AlternatingPrefix (t (d+a) r) (t (d+b) s) := by
  have sameIndex (i : Fin k) : ∀ᶠ d : ℕ in atTop, t (d+a) r i < t (d+b) s i := by
    obtain rs | ⟨rfl,ba⟩ := orientation
    · exact h.compare_centers ladder (ladder.across (i:ℕ) rs) a b
    · exact h.compare_same hj ladder r i ba
  have nextIndex (i v : Fin k) : ∀ᶠ d : ℕ in atTop, i<v → t (d+b) s i < t (d+a) r v := by
    by_cases iv : i<v
    · have step : L s i < L r v := (ladder.next_level (i:ℕ) s r).trans_le
        ((ladder.increasing r).monotone (Nat.succ_le_of_lt (show i.val < v.val from iv)))
      exact (h.compare_centers ladder step b a).mono fun _ cmp _ ↦ cmp
    · exact .of_forall fun _ contra ↦ (iv contra).elim
  filter_upwards [eventually_all.mpr sameIndex,
    eventually_all.mpr (fun i ↦ eventually_all.mpr (nextIndex i))] with d same next
  exact ⟨same,next⟩

/-- All pairs in a fixed finite window, simultaneously, use the same indexed roots
as the two-coordinate first corrections and the complete largest-modulus cutoff. -/
theorem all_ordered_extremes {j : ℕ} (hj : 2≤j) :
    ∃ L, ZeroLadder j L ∧ ∀ k : ℕ, ∃ t : ℕ → Fin j → Fin k → ℝ,
      OriginalAsymptoticPrefix L t ∧ ∀ bmax : ℕ,
      ∀ᶠ d : ℕ in atTop, ∀ (a b : Fin bmax) (r s : Fin j),
        r<s ∨ (r=s ∧ b<a) → AlternatingPrefix (t (d+a) r) (t (d+b) s) := by
  obtain ⟨L,ladder,branches⟩ := all_original_first_correction hj
  refine ⟨L,ladder,?_⟩
  intro k
  obtain ⟨t,h⟩ := branches k
  refine ⟨t,h,fun bmax ↦ ?_⟩
  apply eventually_all.mpr
  intro a
  apply eventually_all.mpr
  intro b
  apply eventually_all.mpr
  intro r
  apply eventually_all.mpr
  intro s
  by_cases good : r<s ∨ (r=s ∧ b<a)
  · exact (h.alternating hj ladder a b r s good).mono fun _ p _ ↦ p
  · exact .of_forall fun _ invalid ↦ (good invalid).elim

#print axioms OriginalAsymptoticPrefix.alternating
#print axioms all_ordered_extremes
end OrderedPartitions.ReciprocalSector
