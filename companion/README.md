# warrior-iii: executable companion

Run the commands below from this directory with Python 3.10 or newer. Checks remain active with Python optimisation enabled. Only the Python standard library is required; the Python checks make no network or model-provider calls.

```sh
python harness.py --teeth
python harness.py --teeth --json outcomes.json
python break_harness.py
python -O harness.py --teeth --json outcomes-optimised.json
python -O break_harness.py
```

The first two commands execute the same 7 named checks. Success exits 0; a failed assertion or execution error exits nonzero. The optional JSON records every named outcome. The third command first checks the unchanged model, then runs 13 cases, each on an isolated temporary copy. There is one scientific mutation per named check, and four more break facts stated inside W01, W02, W04 and W06: a seam lost after an admitted first seam, factorisation through a decoder read as literal equality of key and verdict, the nonzero verdict of the linear bridge erased, and loss of every selected witness read as a zero transported functional. Each of these 11 mutations must fail first at its specified check. Renaming a local variable must survive, and changing the same computation must fail. It writes mutation-report.json with source hashes, exact outcomes and captured output; an incomplete run is not a passing result. The last two commands run the same checks and mutations with optimisation enabled, writing outcomes-optimised.json and mutation-report-optimised.json. The mutation runner passes its own optimisation setting to every child process. Each invocation replaces its own generated output files; archive them first if retaining multiple runs.

## Scope

W01: the A-B-A seam histories (0,0), (1,0), (1,-1) of the manuscript table with their totals, including cancellation (1,-1); and the history (0,1), admitted at the first seam and lost at the second, which is not persistent. Reversing the seam order changes no verdict.
W02: sufficient compression for a selected verdict, without injectivity. Bijectively relabelled keys, the complement among them, decode the same verdict through a decoder other than the identity, and a mixed fibre stays rejected.
W03: existence of a correct decoder, tested exhaustively for binary keys and verdicts on three elements. One decoder fixed in advance is shown to be wrong while a correct decoder exists; this is a counterexample, not a test of any procedure that selects a decoder.
W04: C5 on rational two-dimensional examples, all 600 pairs a, r with integer coefficients in [-2, 2] and a nonzero. Kernel inclusion is compared with nonzero proportionality, and with the C4 bridge: whether the verdict 1[a(v) != 0] can be decoded from the reading r(v) on the finite carrier of all integer vectors in [-2, 2]^2. Scaling r by -3/2, and the change of coordinates (x, y) -> (x + y, y) applied to the carrier and to both functionals, leave the bridge verdict and the kernel criterion unchanged, each recomputed from the transformed data. Applying that change to the carrier and to a but not to r changes the verdict for a = (1, 0), r = (2, 0).
W05: restricted witness domain W0 union {0}; the origin cannot be omitted.
W06: witness loss counted on a selected set W0: partial, none, and all selected witnesses lost. For a = (1, 0) and the nonzero r = (-2, -1), every witness in W0 = {(1, -2)} is lost while the a-witness (1, 0) keeps a nonzero transported pairing. Global loss is kept separate: r = 0 loses every a-witness of [-2, 2]^2, whose a-witnesses span the plane; the r above loses only part of them. Reordering W0 changes no verdict.
W07: the request/capability intervention truth table.

## Extended relational models

The deeper companion is in [deep/README.md](deep/README.md). It adds exact finite families, independent complete-assignment enumeration, executable relation maps, ambiguity witnesses, and model mutations. From this directory, run this work and its shared relation checks:

```sh
python deep/suite.py --work warrior --profile full --json deep-warrior-result.json
```

The deep README also gives the complete population and mutation commands. Its source index pins manuscript anchors and states which scientific claims remain outside finite execution. The smaller examples above remain available with their original scope.

## Limits

C5 is proved in the manuscript for the declared real vector space and linear functionals. W04 checks rational examples in dimension two, not that universal theorem. Its finite carrier decides the bridge exactly for the stated coefficients only, because it contains 0 and a kernel vector of every nonzero r among them, and both basis vectors for r = 0. Other coefficients need other carriers: for a = (1, 0) and r = (1, sqrt 2), no nonzero integer vector lies in the kernel of r, yet the real vector (-sqrt 2, 1) does and has nonzero a-pairing. That example is not executed; irrational equalities are not approximated in floating point, and it remains an analytic boundary of these checks. In W06, "all selected witnesses lost" is relative to the chosen W0 and does not mean that the transported functional is zero. C4 is an instance of the generic fibre criterion formalised in the Mirrors companion; there is no new Lean formalisation of the C4-C5 bridge here. No verdict about an actual Operator Zero follows from these examples.

The source manifest pins the packaged manuscript and program bytes. It records provenance, not a verdict of scientific completeness. The code and its usage instructions use the MIT licence in LICENSE-code.txt; the manuscripts retain their own stated licence, which is not replaced by the code licence.

## Lean companion

[lean/README.md](lean/README.md) describes the existing C2 formalisation, its pinned dependencies and the distinction between the proved finite examples and claims about physical identity.
