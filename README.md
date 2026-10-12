# 2-Visits: the lower density threshold is exactly 1

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23309436.svg)](https://doi.org/10.5281/zenodo.23309436)

A Lean 4 / Mathlib proof that **every 2-Visits instance with density at most 1 is schedulable**,
which settles the open question in Section 8 of

> S. Kanellopoulos, G. Mitropoulos, C. Pergaminelis, T. Tolias,
> *Hardness, Tractability and Density Thresholds of finite Pinwheel Scheduling Variants*,
> arXiv:2604.16030 (ICALP 2026).

## The problem

**2-Visits** (introduced in Kanellopoulos, Pergaminelis, Kokkou, Markou, Pagourtzis,
*Finite Pinwheel Scheduling: the k-Visits Problem*, SODA 2026, arXiv:2507.11681) is the finite,
two-visit version of pinwheel scheduling. Given positive integer deadlines `d₁, …, dₙ`, find a
sequence of length `2n` in which every task `i` appears exactly twice: the first time among the
first `dᵢ` positions, the second time at most `dᵢ` positions after the first.

The **density** of an instance is `∑ 1/dᵢ`. Deciding schedulability is strongly NP-complete
(Kanellopoulos et al., SODA 2026; strengthened in arXiv:2604.16030), so density thresholds give a simple sufficient test. Theorem 11 of
arXiv:2604.16030 shows that the lower density threshold of 2-Visits is at least `√2 − 1/2 ≈ 0.9142`
and at most `1`; Section 8 asks whether `√2 − 1/2` is tight and remarks that
"it is possible that the lower density threshold of 2-Visits is exactly 1".

## The result

`TwoVisits.two_visits_density_threshold` (statement in `Challenge.lean`, proof in `Solution.lean`):

1. every instance with positive deadlines and `∑ 1/dᵢ ≤ 1` admits a 2-Visits schedule;
2. for every `ε > 0` there is an instance with density in `(1, 1 + ε)` that admits none
   (`k + 1` tasks of deadline `k`), so `1` is best possible.

So the lower density threshold of 2-Visits is exactly `1`. The schedule definition `IsSchedule`
is Definition 2 of arXiv:2604.16030 with `k = 2`, using 0-indexed positions. The proof
follows an explicit construction (split / core / chunked rotation block), finished by a matching
argument via Hall's theorem; an informal account is in
[`PROOF.md`](PROOF.md).

## Checking

```sh
lake exe cache get
lake build
```

`#print axioms TwoVisits.two_visits_density_threshold` reports only `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry` in `Solution.lean` and no
`native_decide`. `comparator.json` configures [Comparator](https://github.com/leanprover/comparator)
to check `Solution.lean` against `Challenge.lean`.

`reproduce.jl` (Julia, standard library only) implements the construction and checks it on all
5,862,658 sorted instances of density ≤ 1 with `n ≤ 10` (deadlines ≤ `2n + 1`) and on 593,204 random instances with
`n ≤ 60`; its output is in `output.txt`. This is a sanity check only; the Lean proof is the
evidence.

## How it was found

A Claude loop exploring open problems from recent math papers.

## Licence

Apache-2.0 (see `LICENSE`).
