# Every 2-Visits instance with density ≤ 1 is schedulable

The machine-checked version is `Solution.lean` (theorem `TwoVisits.two_visits_density_threshold`).
`reproduce.jl` implements the construction and checks it.

## Notation

A schedule assigns each task two positions x < y in [1, 2n], all distinct, with
x ≤ d and y − x ≤ d.

## Generalized statement T(b)

Positions are c+1..c+2n. Deadlines g_1 ≤ … ≤ g_n satisfy:
- (i) Σ 1/g_k + c/(2g_1) ≤ 1;
- (ii) g_k ≥ c + k.

Then there is an assignment with c < x_k < y_k ≤ c+2n, x_k ≤ g_k and y_k − x_k ≤ g_k.

The case c = 0 is the main theorem. There, (ii) follows from density: if g_k < k + 1, the first k+1 terms alone exceed 1.

## Proof by strong induction on n

### 1. Split

Suppose some s ∈ [1, n−1] has g_{s+k} ≥ c + 2s + k for all k ≥ 1. Then:
- S (the first s tasks) is solved at offset c.
- L (the remaining tasks) is solved at offset c+2s.
- L inherits (i) because Σ_S 1/g ≥ s/g_{s+1} and c/(2g_1) ≥ c/(2g_{s+1}).

### 2. Core

Otherwise the instance is irreducible. For every s there is r > s with g_r ≤ c + s + r − 1.
- Let w be the largest index with g_w = c + w (it exists by s = 1), and let D = n − w.
- **Chain bound:** Σ_{k>w} g_k ≤ Σ_{k=w+1}^{n} (c + 2k − 2). By the tangent line 1/g ≥ 2/T − g/T², this gives Σ_{k>w} 1/g_k ≥ D/(c + w + n − 1).
- **Two-case chord bound** for 1/(x − D) on [g_1, c + w]:
  - D < c, or D = 0;
  - the core (tasks 1..w, offset c − D, deadlines g − D) satisfies (i).

  The core also satisfies (ii), and all its deadlines are at most (offset + size). Call such an instance a C-instance.
- Tasks above w go to the top block slots unchanged.

### 3. Block for C-instances

The first visits are at offset+1..offset+n and the second visits at offset+n+1..offset+2n.

**Deficits.** These are tasks with g < n, with δ_j = n − g_j. Group them (largest first) into chunks of size E = ⌈c/2⌉. A chunk with leader δ = q and m deficits uses q + m slots:
- q partner slots, each shifted forward by m;
- m deficit slots, each shifted back by q.

**(S) Slot constraints.** These reduce to δ_1 + δ_j + j + (2/c)Σ_{i<j}δ_i ≤ n − c. The proof uses:
- density restricted to the first j tasks;
- a tangent line at u* = N(2j+c)/(2(j+c)).

**(Z) Partner dominance.** For 1 ≤ θ ≤ E:
- #partner slots + (c − θ + 1) ≤ #{tasks with g ≥ n + θ}.

The proof combines:
- a three-group density count;
- the tangent line at n;
- Q1: 2Δ ≤ c(n − c − 2d − δ_1);
- the exact identity R − L = ((c − 2t)/2)·Q1 + (nonnegative polynomial)/n².

**Matching.** Threshold dominance plus Hall's theorem assigns tasks to slots.

## Sharpness

k+1 tasks of deadline k have density 1 + 1/k and no schedule: their first visits would need k+1 distinct positions in [1, k].
