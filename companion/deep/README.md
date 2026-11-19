# Exact finite relational models

This shared engine accompanies Mirrors, Warrior III and Body IV. It uses Python 3.10 or later and the standard library only. It makes no network, model-provider or random calls. All numerical comparisons use integers or exact rational numbers. Checks remain active under Python optimisation.

From this directory:

```sh
python suite.py --profile full --json result.json
python break_suite.py --json mutation-result.json
python break_suite.py --full-only --timeout 300 --json full-result.json
```

The first command executes all 41 named families in `map.json`: 12 shared families (G), 17 for Mirrors (M), 4 for Warrior III (W) and 8 for Body IV (B). Each family tests its declared population. `--work mirrors`, `--work warrior` and `--work body` select that work together with the shared families: 29, 16 and 20 families in all. `map.json` declares each of these name sets. The requested selection is compared with its declared set before any family runs, and a missing, extra or repeated name refuses the run. deep/G06 makes the same comparison for every work, the all-work selection included, in every battery run that includes it; under `--only` it does not run. Use `--only` with an exact family name to run one example; an unknown name, or a name outside the selected work, is refused. `--profile quick` uses the smaller declared bounds.

The second command executes 107 cases on the complete quick population in isolated temporary copies: ordinary and optimised baselines, one named model mutation for each of the 41 families, and 32 controls, each run as an equivalent and as a damaging transformation of the same site. A mutation or damaging transformation succeeds only if its named family fails first; an equivalent transformation must leave the whole result unchanged. One control damages the independent decoder enumeration rather than the decoder itself, and its description says so. The control at the work selector also runs `--work warrior` directly. With the equivalent change that run must pass with exactly the 16 declared families. With warrior mapped to the shared letter G it must be refused before any family runs. The third command compares the full population in ordinary and optimised Python. Reports preserve source hashes and primary rejected child results. Choose a fresh output name to preserve a previous run.

Family identifiers such as M15 or B08 name executable families, not manuscript propositions; the table at the end gives the statement each family checks. deep/M15 enumerates the two-node contact with independent bond, wire and bias. deep/M16 tries each possible constant binary section against both endpoint values. deep/B08 evaluates the declared closed-form transport law: a full lap of increasing longitude rotates the transported vector by −sin λ turns. It reads an arrow and its unoriented axis at four non-polar latitudes; poles are excluded, because longitude does not parametrise a loop there. At 30° a full lap takes the arrow to its opposite and returns the axis to itself, a reading that cannot see the sign of the law. At sin λ = 1/3 it can: the lap gives two thirds of a turn and agrees, modulo one turn, with the cap-area expression 1 − sin λ. That agreement holds on closed loops only. Open quarter-lap arcs are read in the local tangent frame of the parallel and depend on that convention. These are formula and readout checks, not a numerical solution of the connection.

deep/G10 checks the shear action on points and its induced maximum norm on the sampled parameters. deep/G11 counts all fair sign histories through nine steps in the full profile. At a fixed horizon the mean stays at the initial point and the first-coordinate variance is the horizon times the squared second coordinate. With one shared sign the variance instead grows quadratically. deep/G12 applies a shear and its inverse on one capped account. At exactly two step charges both steps can execute. The coordinates return and both charges remain on the account.

## Relations and joint properties

`map.json` declares typed assumptions, conditional claims and empirical hypotheses separately. A hypothesis also carries the prerequisites its source states but no family executes, such as a declared class of messages, protocols, readings or connections; each executed finite interpretation is a separate finite check. Logical prerequisite cycles are rejected, as is a declared prerequisite that is removed, detached from every claim or replaced by an absent identifier. Cycles in the modelled system's relations are permitted and can carry obstructions. An acyclic, well-typed declared graph does not prove the truth of its nodes or the completeness of its extraction from prose.

The relation solver computes a natural join. A second algorithm independently enumerates every complete assignment and tests membership in the original relations. For the three declared composition examples, the output contains the full joint assignments, ambiguous observation pairs, inclusion-minimal incompatible subsets, and the assignments introduced by removing each relation. This last quantity is extensional constraint sensitivity, not evidence of a physical causal effect.

Two consistent links need not have a joint witness with a third. Pairwise projections need not determine a higher-arity relation. Two individually uninformative readings can jointly determine a verdict. The finite families include all ternary Boolean relations, higher-arity parity relations, inconsistent cycles and exact ambiguity witnesses, including honest consistent controls.

## Coverage and limits

The shared two-step covector check, deep/G09, asks whether each arrow preserves the same declared covector on the whole space and whether their composite preserves it. Two coordinate swaps restore the initial pairing after an intermediate zero. An independent calculation follows basis vectors forward through each matrix. A change of coordinates transforms the matrices, vector and covector together. A singular first arrow tests a second arrow whose defect is invisible on the reachable image.

| Work | Executed classes | Limits |
|---|---|---|
| Mirrors | Fibre decoders, rooted path lifting, charged residual languages, residual keys, prefix reflection, the complete three-input restart automaton, recurrence and the predicate P* on ultimately periodic words with the separating pair of Proposition M5, finite instances of Proposition M11 on event words with explicit per-step debits, the consecutive delayed constructor, silence bounds, driven completion, absolute witness costs, paid prefixes of witness words on one budget, geometric return debits, and the contact models of [K3b] (membership and interval extension) | Finite populations and parameter families; they do not establish arbitrary infinite-history or smooth-cohomology results. The finite P* sweep does not establish the topology theorem. Proposition M12 is illustrated only for eternal silence; its arbitrary admitted set and every-prefix premise are not modelled. Proposition M15(b), the infinite limit of M15(d) and the other analytic infinite limits retain their text proofs. |
| Warrior III | Exact rational linear algebra, full and restricted witness domains, zero-adjoined decoding, partial loss against loss of all selected witnesses with the global case r = 0 kept apart, and composed pullbacks as supporting algebra | The explicit linear model and its declared domains; the loss classification is relative to the declared selected witnesses. No empirical proof of slice visibility or a physical identity mechanism. |
| Body IV | Partition refinement; the borrowed joint reading (V₀, Z) as the meet of two partitions, apart from the intrinsic hint-off after channel; contextual cycles; exact cochains with the oriented boundary operator as supporting algebra; finite path/readout countermodels comparing selected traces with full states; explicit covariant derivatives v′ + Av for rational 2×2 connection matrices and the preservation sets they give, including independent blocks with equal nonempty sets; the Foucault transport law and its readings of an arrow and its unoriented axis | These constrain finite interpretations. They do not establish recognition, learning, consciousness, N1–N6, or the identification of a connection with Operator Zero. Neither a learner nor a causal attribution of a message is modelled; a control without the message belongs to an intervention study. No action protocol is modelled for N4. Equal nonempty preservation sets are not a coupling theorem. |

`source-index.json` records exact manuscript hashes, source anchors, family-to-source links and additional exclusions. Its paths refer to the joint three-work source layout. A family that only exercises shared apparatus, such as the relation solver, the type and dependency validators, the map contract, pullback composition or the boundary operator, carries no coverage link of its own. A standalone companion contains its own manuscript, and its index quotes that work only; the claims of the other works are pinned by path, line and the SHA-256 of the quoted span. Matching bytes and quotations prove source identity, not semantic correspondence. The original smaller companion examples and the previously compiled Lean sources retain their separately stated scope. No V3 internals are included or tested.

The three packages carry one deep layer: a change to its code, map or catalogue changes all three packages and their evidence together. The checks do not read the manuscripts; a claim edited under an unchanged anchor line leaves them green, and only the span hashes of the source index show the change. deep/M17 instantiates Proposition M6 on a finite version of the example of Mirrors §8.1: one declared family realised by two deployments, where a target history outside the common family has no lift; the infinite histories and the further predicate of that example are not modelled.

The declared finite populations, the mapping from source claims to models, and the set of mutations all have boundaries. Passing these checks is not a certificate of universal correctness, empirical truth or absence of every logical gap.

## Family identifiers

Identifiers name executable families. A deep family carries the prefix `deep/`; a family of a smaller companion carries the name of its package. The same letter and number can name different things: deep/M15 is the contact model, while Proposition M15 is checked by deep/M12 and mirrors/M07; deep/B08 is the Foucault model, while body-iv/B08 checks the equality clause of N5. Proposition numbers M1–M16, claims C1–C5 and hypotheses N1–N6 refer to the manuscripts. A family marked as supporting apparatus covers no manuscript result of its own.

| Family | Statement it checks |
|---|---|
| deep/G01 | Supporting apparatus: the relation solver's join equals an independent enumeration of complete assignments |
| deep/G02 | Body N1, gluing: links with pairwise witnesses and no common one; every inclusion-minimal conflict is returned |
| deep/G03 | Supporting apparatus: typed carriers and relations; empty and ill-typed declarations are rejected |
| deep/G04 | Supporting apparatus: the dependency order of declared claims; cycles, duplicates and missing prerequisites are rejected, and a hypothesis stays visible as a condition |
| deep/G05 | Warrior C4 and Body N6 on a composed relation: whether a projected readout decodes the verdict depends on the readout, not on relation order or variable names |
| deep/G06 | Supporting apparatus, the map contract: the claim graph with its source-only prerequisites, the family population, every per-work name set against its selector in every battery run (not under --only), and the computed composition examples (Warrior C4, Body N6) |
| deep/G07 | Body N1: pairwise projections do not determine a relation of higher arity |
| deep/G08 | Proposition M1 and Warrior C4 with the joint reading of two channels (Mirrors §9.2, cited in Body): readings that each fail can decode a verdict together; exact ambiguity witnesses |
| deep/G09 | Mirrors' protected-covector criterion: stepwise against terminal preservation of an exact covector by two arrows; a contrast with Warrior C5, which preserves nonzero pairing |
| deep/G10 | Mirrors' shear model: the shear action, its inverse and its induced maximum norm |
| deep/G11 | Mirrors' independent signs and Body's stationary mean: exact fixed-horizon mean and variance; one shared sign changes the variance |
| deep/G12 | Paid return on one account (Mirrors, Warrior [K3t], Body): a shear and its inverse return the coordinates and keep both charges |
| deep/M01 | Proposition M1: a decoder exists exactly when every observation fibre is homogeneous for the verdict |
| deep/M02 | Proposition M2: lifts of a target path from the declared root, against an enumerated table of source paths |
| deep/M03 | Proposition M8: a residual budget keeps the charge of the executed prefix |
| deep/M04 | Propositions M3 and M5: recurrence on ultimately periodic words and the predicate P*, with the separating pair of M5 |
| deep/M05 | Proposition M10: the complete three-input restart automaton (silence, request, block) |
| deep/M06 | Proposition M7: an inverse bijection is prefix-causal exactly when it reflects prefixes |
| deep/M07 | Proposition M8: derivatives of a charged language keep the charge of the executed prefix; negative prices are rejected |
| deep/M08 | Proposition M9: a key suffices exactly when a predicate indexed by it reproduces every residual language |
| deep/M09 | Proposition M10: the observation channels of the restart automaton; silence at completion separates the two modes |
| deep/M10 | Proposition M11 on finite event words; Proposition M12 is only illustrated, for eternal silence |
| deep/M11 | Proposition M13: under a silence bound no event occurs at or after step N(D+1) |
| deep/M12 | Proposition M15, parts (a) and (c) on finite words: absolute witness charges and paid prefixes on one budget |
| deep/M13 | Proposition M16: geometric frontier debits and the region where every period is paid |
| deep/M14 | Proposition M14: a driven trajectory spends the whole budget by step N(D+1) |
| deep/M15 | Mirrors' two-node contact model [K3b], with Proposition M1: the record decodes the wire, not the bond |
| deep/M16 | Mirrors' contact model [K3b]: a constant section on an interval exists exactly when the endpoint values agree |
| deep/M17 | Proposition M6 on a finite version of the instance of Mirrors §8.1: one declared family realised by two deployments; the pointwise transport is a bijection that keeps decoding, datum, admission and roots, every admitted target history lifts, and a target history outside the common family has no lift |
| deep/W01 | Warrior C5: for nonzero a, ker r ⊆ ker a exactly when a = c r |
| deep/W02 | Warrior C5 on a restricted domain W0 ∪ {0}; restricted preservation does not give global preservation |
| deep/W03 | Warrior C5, collapse: loss of every selected witness of W0 against global loss, which needs r = 0 |
| deep/W04 | Supporting algebra: pullback along composed matrices |
| deep/B01 | Body N1, finite interpretation: strict refinement of partitions; a bijective relabelling is not strict |
| deep/B02 | Body N2, finite interpretation: the borrowed reading (V₀, Z) as a meet of partitions, apart from the intrinsic after channel; N2 stays open |
| deep/B03 | Body N1, gluing countermodel: a parity cycle has a global assignment exactly when its parity sum is even |
| deep/B04 | Body N3: exact cochains have zero periods; an unfilled cycle can carry a nonzero period |
| deep/B05 | Body N5, finite interpretation: preservation sets from explicit covariant derivatives; common preservation against equal nonempty sets |
| deep/B06 | Supporting algebra: the oriented simplicial boundary, with ∂∂ = 0 |
| deep/B07 | Body N4, finite readout countermodel: equality of selected traces against equality of full states; no action protocol |
| deep/B08 | Body's Foucault paragraph [K3f]: the declared closed-form transport law and its arrow and axis readings |
| mirrors/M01 | Proposition M1: decoders for all binary readings and verdicts on three histories |
| mirrors/M02 | Proposition M2: lifting from the declared root against global path coverage; the images of the root and of each next state |
| mirrors/M03 | Mirrors' one-common-witness section: separate witnesses without a common one |
| mirrors/M04 | Propositions M3 and M5: equal finite prefixes with different recurrence of their periodic tails |
| mirrors/M05 | Propositions M8 and M9: a cumulative charged residual against a reset counter |
| mirrors/M06 | Proposition M10, the two-input slice without the blocking input: a request against capability |
| mirrors/M07 | Proposition M15 on finite words and horizons: geometric upkeep, a witness floor and payment from one budget |
| mirrors/M08 | Mirrors §9.2: the two shares of the declared XOR construction, each uninformative, together decisive |
| warrior-iii/W01 | Warrior's A, B, A example (C3, C4): seam histories against their totals; a seam lost after an admitted first seam |
| warrior-iii/W02 | Warrior C3 and C4: sufficient compression for a selected verdict without injectivity |
| warrior-iii/W03 | Warrior C4 and F4: existence of a correct decoder; a fixed wrong decoder is a counterexample only |
| warrior-iii/W04 | Warrior C5 with the C4 bridge on rational two-dimensional examples |
| warrior-iii/W05 | Warrior C5 on the restricted domain W0 ∪ {0} |
| warrior-iii/W06 | Warrior C5, collapse: loss of every selected witness against global loss |
| warrior-iii/W07 | Warrior's capability passage (Proposition M10): a request against capability |
| body-iv/B01 | Body N1 and F-e: strict refinement; block count does not decide refinement |
| body-iv/B02 | Body N2 and the partition clause of F-d: a borrowed coordinate against retained refinement; a message that is a function of V₀ adds nothing; the no-message control is not modelled |
| body-iv/B03 | Body N1: a contextual triangle without a global assignment |
| body-iv/B04 | Body N3: exact discrete forms, path independence and orientation |
| body-iv/B05 | Body N3: curvature on a filled triangle against a period on an unfilled cycle |
| body-iv/B06 | Body N4 and F-f: a finite readout countermodel; the protocol class of N4 is not modelled |
| body-iv/B07 | Body N5 and F-c1: common preservation, with explicit covariant derivatives |
| body-iv/B08 | Body N5 and F-c2: equality of preservation sets together with nonemptiness |
