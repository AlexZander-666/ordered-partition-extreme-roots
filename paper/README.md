# Extreme zeros of ordered set-partition polynomials

The manuscript concerns lists of nonempty labelled blocks. Each order of the blocks contributes to the row. For every fixed threshold `j ≥ 2` and every fixed prefix length, the results concern the simple negative roots of largest modulus and their strict order between ranks `n < m ≤ n+j` for sufficiently large `n`. The paper gives an asymptotic expansion for each such root. The onset is existential and depends on the threshold and prefix length.

## Rebuild the paper and run the checks

Extract the archive into a writable directory and run `python3 -B reproduce.py` with Python 3 and TeX Live 2026. The build accepts an explicit `PDFLATEX` executable path. It sets `SOURCE_DATE_EPOCH=1795737600`, `FORCE_SOURCE_DATE=1`, and `TZ=UTC`. It compiles the loose and extracted copies twice and compares the PDF bytes. PDF byte comparisons use the same TeX Live setup.

The scripts also run independently from an arbitrary working directory. Set `SOURCE` to the absolute path of the extracted archive.

```sh
python3 -B "$SOURCE/anc/check.py"
python3 -B "$SOURCE/anc/check_first_correction.py"
```

The first script compares 350 exact coefficients for `j=2,3,4,5` using a last-block recurrence and an independent exponential generating function expansion. It also checks rational sign probes at `j=2`; the expected alternating signs are asserted for the two residue classes at `d=128`. The second script checks the leading and first correction coefficients in 42 residue/offset cases by finite differences, including the constant case. Both scripts use only the Python standard library. The general results follow from the mathematical proofs and the separate Lean development.

## Formal statement map

The companion Lean source is distributed separately from this TeX archive. The Lean root index `i : Fin k` is zero-based, corresponding to the paper's index `i.val + 1`. For the paper's prefix length parameter `K`, take the Lean prefix length to be `K+1` to obtain both displayed inequalities for every compared index.

| Manuscript statement | Lean declaration |
| --- | --- |
| Original labelled ordered row and its recurrence | `OrderedPartitions.row`, `OrderedPartitions.row_recurrence` |
| Block generating function and scaled reciprocal coefficients | `OrderedPartitions.ReciprocalEdge.ordinary_coefficient`, `OrderedPartitions.ReciprocalEdge.scaled_coeff_of_offset`, `OrderedPartitions.ReciprocalEdge.eval₂_reciprocalRow` |
| Rational first correction and convergence on compact disks | `OrderedPartitions.ReciprocalEdge.H_two`, `OrderedPartitions.ReciprocalEdge.reciprocalCorrectionCoeff_formula`, `OrderedPartitions.ReciprocalEdge.reciprocal_uniform_first_correction` |
| All zeros of the limit series, strictness and ordering | `OrderedPartitions.ReciprocalSector.all_limit_zeros` |
| First correction for the indexed original roots | `OrderedPartitions.ReciprocalSector.all_original_first_correction` and the `original_correction` field of `OriginalAsymptoticPrefix` |
| Same-residue step | `OrderedPartitions.ReciprocalSector.OriginalAsymptoticPrefix.indexed_drift` |
| Extreme-root window on original rows, including strict modulus separation from every other complex zero | `OrderedPartitions.ReciprocalSector.original_rank_window` |
| Threshold-two limit locations | `OrderedPartitions.ReciprocalEdge.two_limit_zeros` |

The Lean proofs use an analytic isolation and zero-free-complement argument for the original root transfer. The paper gives a short Rouché argument for the same conclusion. The paper uses the Hurwitz–Hille theorem with a parameter shift to establish the real and simple limiting zeros.
