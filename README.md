# Extreme zeros of ordered set-partition polynomials

Bowen Zuo, East China University of Science and Technology.

An ordered partition of a labeled set contributes one factor of \(t\) for each block of size at least \(j\). For each fixed \(j\ge2\) and fixed prefix length, all sufficiently large rows have simple negative roots of largest modulus in that prefix. These prefixes strictly alternate at any two ranks within a window of \(j+1\) consecutive rows, in the degree-dependent order given in the paper. A Mittag–Leffler limit and its first correction give the outer-root scale and the comparison at distance \(j\). [Paper](paper/main.pdf) · [LaTeX source and checks](paper/arxiv-source.zip) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees)

## Rebuild the paper and the checks

Use TeX Live 2026 and Python 3.10 or later. If needed, set `PDFLATEX` to its executable path.

```sh
sha256sum --check SHA256SUMS
cd paper
python3 -B reproduce.py
```

The reproducer runs two LaTeX passes each from the loose files and a fresh TeX archive extraction. It compares the PDF bytes and runs both arithmetic checks. Directly invoking `python3 -B anc/check.py` verifies 350 exact reciprocal coefficients and two rational sign patterns at \(j=2\). Invoking `python3 -B anc/check_first_correction.py` checks 42 leading and first-correction coefficient cases.

## Verify the Lean proof

The formal project concerns the original ordered rows. Its public declarations include `OrderedPartitions.ReciprocalSector.original_rank_window`, `all_original_first_correction`, and the indexed drift assertion. The strict modulus cutoff separates every other complex root from the displayed prefix. [Paper-to-Lean map](verification/STATEMENT-MAP.md) · [Input pins](verification/SOURCE-PINS.md)

Install the Lean release in `formal/lean-toolchain` and prepare a separate directory with the external Lake packages and compiled dependencies pinned by `formal/lake-manifest.json`. Run from a fresh checkout or extraction with no local `.lake`:

```sh
cd formal
python3 -B verify.py /absolute/path/to/locked/.lake/packages 1
```

The verifier rebuilds local modules with warnings as errors, checks the dependency lock and formal import closure, audits the transitive axioms and replays each compiled local module separately. The hosted workflow runs the same checks and saves its receipts.

Apache-2.0 applies to the original proof and verification code. The author retains copyright in the manuscript. See [NOTICE](NOTICE).
