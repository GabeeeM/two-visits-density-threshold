module

public import Mathlib

/-!
# 2-Visits: the lower density threshold is exactly 1

The **2-Visits** problem (introduced by Kanellopoulos–Pergaminelis–Kokkou–Markou–Pagourtzis, SODA 2026, arXiv:2507.11681; see also
Kanellopoulos–Mitropoulos–Pergaminelis–Tolias, *Hardness, Tractability and Density Thresholds
of finite Pinwheel Scheduling Variants*, arXiv:2604.16030, ICALP 2026): given positive integer
deadlines `d₁, …, dₙ`, is there a sequence of length `2n` in which every task `i` occurs exactly
twice, its first occurrence among the first `dᵢ` positions and its second occurrence at most `dᵢ`
positions after the first? (Definition 2 of arXiv:2604.16030 with `k = 2`.)

The *density* of an instance is `∑ᵢ 1/dᵢ`. By Theorems 10 and 11 of arXiv:2604.16030, the lower
density threshold of 2-Visits (the largest `δ` such that every instance of density `≤ δ` is
schedulable) lies in `[√2 − 1/2, 1]`, and its Section 8 asks whether the lower bound is tight,
remarking that "it is possible that the lower density threshold of 2-Visits is exactly 1".

`two_visits_density_threshold` states that the threshold is exactly `1`:
* every instance with positive deadlines and density at most `1` admits a schedule, and
* for every `ε > 0` some instance with density in `(1, 1 + ε)` admits no schedule
  (so `1` cannot be improved).
-/


@[expose] public section

open Finset

namespace TwoVisits

/-- A 2-Visits schedule (Definition 2 of arXiv:2604.16030 with `k = 2`) for `n` tasks with
deadlines `d`. The schedule is `s : Fin (2 * n) → Fin n`; the 0-indexed position `p` is the
1-indexed position `p + 1`. Every task `i` occurs exactly twice, at positions `p < q`; the first
occurrence lies within the first `d i` positions (`p + 1 ≤ d i`) and the second is at most `d i`
positions after the first (`q - p ≤ d i`). -/
def IsSchedule (n : ℕ) (d : Fin n → ℕ) (s : Fin (2 * n) → Fin n) : Prop :=
  ∀ i : Fin n, ∃ p q : Fin (2 * n), p < q ∧ s p = i ∧ s q = i ∧
    (∀ r : Fin (2 * n), s r = i → r = p ∨ r = q) ∧
    (p : ℕ) + 1 ≤ d i ∧ (q : ℕ) - (p : ℕ) ≤ d i

/-- **The lower density threshold of 2-Visits is exactly 1.**
(1) Every instance with positive deadlines and density `∑ 1/dᵢ ≤ 1` is schedulable.
(2) For every `ε > 0` there is an unschedulable instance with density in `(1, 1 + ε)`. -/
theorem two_visits_density_threshold :
    (∀ (n : ℕ) (d : Fin n → ℕ), (∀ i, 0 < d i) → ∑ i, (1 : ℚ) / d i ≤ 1 →
      ∃ s : Fin (2 * n) → Fin n, IsSchedule n d s) ∧
    (∀ ε : ℚ, 0 < ε → ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, 0 < d i) ∧
      1 < ∑ i, (1 : ℚ) / d i ∧ ∑ i, (1 : ℚ) / d i < 1 + ε ∧
      ¬ ∃ s : Fin (2 * n) → Fin n, IsSchedule n d s) := by
  sorry

end TwoVisits
