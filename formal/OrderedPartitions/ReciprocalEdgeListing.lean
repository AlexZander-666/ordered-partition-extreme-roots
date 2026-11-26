import OrderedPartitions.ReciprocalEdgeGap
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Set.Finite.Lemmas

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Set Filter Complex OrderedPartitions.ReciprocalEdge
open scoped Topology

/-- Decreasing enumeration in the real coordinate, starting at the zero closest to zero. -/
structure NegativeListing (f : ℝ→ℝ) (z : ℕ→ℝ) : Prop where
  decreasing : StrictAnti z
  negative : ∀ n, z n<0
  vanishes : ∀ n, f (z n)=0
  complete : ∀ {a}, a<0 → f a=0 → ∃ n, z n=a

private theorem next_exists {s : Set ℝ} (loc : ∀ a : ℝ, (s∩Ici a).Finite)
    (far : ∀ b : ℝ, ∃ a∈s, a<b) (b : ℝ) : ∃ x, IsGreatest (s∩Iio b) x := by
  classical
  obtain ⟨a,ha,ab⟩ := far b
  let cut := (s∩Ici a)∩Iio b
  have fin : cut.Finite := (loc a).subset inter_subset_left
  obtain ⟨x, hx, max⟩ := exists_max_image cut id fin ⟨a, ⟨⟨ha, show a≤a from le_rfl⟩,ab⟩⟩
  refine ⟨x,⟨hx.1.1,hx.2⟩,?_⟩
  intro y hy
  by_cases ya : a≤y
  · exact max y ⟨⟨hy.1,ya⟩,hy.2⟩
  · exact (le_of_not_ge ya).trans hx.1.2

theorem listing_of_locally_finite (f : ℝ→ℝ)
    (loc : ∀ a, ({x : ℝ | x<0 ∧ f x=0}∩Ici a).Finite)
    (far : ∀ b : ℝ, ∃ a, a<min b 0 ∧ f a=0) : ∃ z, NegativeListing f z := by
  classical
  let s := {x : ℝ | x<0 ∧ f x=0}
  have unbound (b : ℝ) : ∃ a∈s, a<b := by
    obtain ⟨a,ab,fa⟩ := far b
    exact ⟨a,⟨ab.trans_le (min_le_right _ _),fa⟩,ab.trans_le (min_le_left _ _)⟩
  choose next hn using next_exists (s:=s) loc unbound
  let z : ℕ→ℝ := Nat.rec (next 0) (fun _ old ↦ next old)
  have strict : StrictAnti z := strictAnti_nat_of_succ_lt fun n ↦ (hn (z n)).1.2
  have mem (n : ℕ) : z n∈s := by cases n with
    | zero => exact (hn 0).1.1
    | succ n => exact (hn (z n)).1.1
  have cofinal (a : ℝ) : ∃ n, z n≤a := by
    by_contra! none
    have sub : range z ⊆ s∩Ici a := by rintro _ ⟨n,rfl⟩; exact ⟨mem n,(none n).le⟩
    exact (Set.infinite_range_of_injective strict.injective) ((loc a).subset sub)
  refine ⟨z,strict,fun n ↦ (mem n).1,fun n ↦ (mem n).2,?_⟩
  intro a an fa
  obtain ⟨n,lo⟩ := cofinal a
  induction n with
  | zero => exact ⟨0,le_antisymm lo ((hn 0).2 ⟨⟨an,fa⟩,an⟩)⟩
  | succ n ih =>
    rcases le_or_gt (z n) a with prior|later
    · exact ih prior
    · exact ⟨n+1,le_antisymm lo ((hn (z n)).2 ⟨⟨an,fa⟩,later⟩)⟩

/-- The actual real zeros, restricted to the negative axis, form a closed discrete set. -/
theorem section_local_finite {j : ℕ} (hj : 1≤j) (r : Fin j) (a : ℝ) :
    ({x : ℝ | x<0 ∧ sectionR j r x=0}∩Ici a).Finite := by
  let f := sectionR j r
  let s := {x : ℝ | x<0 ∧ f x=0}
  have cf : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (real_derivative hj r x).continuousAt
  have closed : IsClosed s := by
    have eq : s=Iic 0∩f ⁻¹' {0} := by
      ext x
      constructor
      · rintro ⟨h,z⟩; exact ⟨h.le,z⟩
      · rintro ⟨h,z⟩
        change x≤0 at h
        rcases h.eq_or_lt with e|l
        · subst x; exact False.elim ((sectionR_zero_pos j r).ne' z)
        · exact ⟨l,z⟩
    rw [eq]
    exact isClosed_Iic.inter (isClosed_singleton.preimage cf)
  have disc : IsDiscrete s := by
    rw [isDiscrete_iff_nhdsNE]
    intro x hx
    have der : deriv f x≠0 := real_simple hj r hx.1 hx.2
    have punct : ∀ᶠ y in 𝓝[≠] x, f y≠0 :=
      (real_derivative hj r x).differentiableAt.hasDerivAt.eventually_ne der
    rw [Filter.inf_principal_eq_bot]
    exact punct.mono fun y hy mem ↦ hy mem.2
  have compact : IsCompact (s∩Ici a) := by
    apply (isCompact_Icc (α:=ℝ) (a:=a) (b:=0)).of_isClosed_subset (closed.inter isClosed_Ici)
    exact fun x hx ↦ ⟨hx.2,hx.1.1.le⟩
  exact compact.finite (disc.mono inter_subset_left)

theorem section_listing {j : ℕ} (hj : 1≤j) (r : Fin j)
    (far : ∀ b : ℝ, ∃ a, a<b ∧ reciprocalLimit j r a=0) :
    ∃ z, NegativeListing (sectionR j r) z := by
  apply listing_of_locally_finite _ (section_local_finite hj r)
  intro b
  obtain ⟨a,ab,zero⟩ := far (min b 0)
  exact ⟨a,ab,zero_cast.mpr zero⟩

#print axioms listing_of_locally_finite
#print axioms section_listing
end OrderedPartitions.ReciprocalSector
