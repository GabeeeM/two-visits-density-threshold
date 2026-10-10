module

public import Mathlib

/-!
# 2-Visits: the lower density threshold is exactly 1 (proof)

Proof of `TwoVisits.two_visits_density_threshold`, stated in `Challenge.lean`.
The proof outline (offset generalization T(b), split / core / chunked-rotation block,
Hall matching) is documented in `PROOF.md`.
-/


@[expose] public section


open Finset

namespace TwoVisits

/-! ### from A_defs.lean -/
/-- Definition 2 of Kanellopoulos–Mitropoulos–Pergaminelis–Tolias (k = 2).
A schedule of length `2n` is `s : Fin (2*n) → Fin n` (position `p : Fin (2n)` is the
1-indexed position `p+1`).  Every task `i` occurs exactly twice, at positions `p < q`;
the first occurrence is within the first `d i` positions (`p + 1 ≤ d i`) and the second
is at most `d i` positions after the first (`q - p ≤ d i`). -/
def IsSchedule (n : ℕ) (d : Fin n → ℕ) (s : Fin (2 * n) → Fin n) : Prop :=
  ∀ i : Fin n, ∃ p q : Fin (2 * n), p < q ∧ s p = i ∧ s q = i ∧
    (∀ r : Fin (2 * n), s r = i → r = p ∨ r = q) ∧
    (p : ℕ) + 1 ≤ d i ∧ (q : ℕ) - (p : ℕ) ≤ d i

/-- Pair assignment on absolute positions `c+1 .. c+2n` for tasks `0..n-1` with deadlines `g`. -/
def Good (n c : ℕ) (g x y : ℕ → ℕ) : Prop :=
  (∀ k < n, c < x k ∧ x k < y k ∧ y k ≤ c + 2 * n ∧ x k ≤ g k ∧ y k ≤ x k + g k) ∧
  (∀ k < n, ∀ l < n, x k ≠ y l) ∧
  (∀ k < n, ∀ l < n, x k = x l → k = l) ∧
  (∀ k < n, ∀ l < n, y k = y l → k = l)

/-- From a good pair assignment at offset 0 for the sorted deadlines `d ∘ σ`, build a schedule. -/
theorem schedule_of_good (n : ℕ) (d : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (x y : ℕ → ℕ)
    (hG : Good n 0 (fun k => if h : k < n then d (σ ⟨k, h⟩) else 0) x y) :
    ∃ s : Fin (2 * n) → Fin n, IsSchedule n d s := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  -- every position p < 2n is hit
  have hcover : ∀ p : ℕ, p < 2 * n → ∃ k, k < n ∧ (x k = p + 1 ∨ y k = p + 1) := by
    classical
    let f : ℕ × Bool → ℕ := fun kb => if kb.2 then x kb.1 else y kb.1
    let S : Finset (ℕ × Bool) := (range n) ×ˢ (univ : Finset Bool)
    have hinj : Set.InjOn f S := by
      rintro ⟨k, b⟩ hk ⟨l, b'⟩ hl hkl
      simp only [S, coe_product, Set.mem_prod, mem_coe, mem_range, coe_univ,
        Set.mem_univ, and_true] at hk hl
      simp only [f] at hkl
      cases b <;> cases b' <;> simp at hkl
      · rw [h4 k hk l hl hkl]
      · exact absurd hkl.symm (h2 l hl k hk)
      · exact absurd hkl (h2 k hk l hl)
      · rw [h3 k hk l hl hkl]
    have hsub : S.image f ⊆ Icc 1 (2 * n) := by
      intro v hv
      simp only [mem_image] at hv
      obtain ⟨⟨k, b⟩, hk, rfl⟩ := hv
      simp only [S, mem_product, mem_range, mem_univ, and_true] at hk
      obtain ⟨a1, a2, a3, _, _⟩ := h1 k hk
      simp only [f, mem_Icc]
      cases b <;> simp <;> omega
    have hcard : (S.image f).card = 2 * n := by
      rw [card_image_of_injOn hinj]; simp [S]; ring
    have heq : S.image f = Icc 1 (2 * n) := by
      apply eq_of_subset_of_card_le hsub
      simp [hcard]
    intro p hp
    have : p + 1 ∈ S.image f := by rw [heq]; simp; omega
    simp only [mem_image] at this
    obtain ⟨⟨k, b⟩, hk, hkb⟩ := this
    simp only [S, mem_product, mem_range, mem_univ, and_true] at hk
    refine ⟨k, hk, ?_⟩
    cases b <;> simp [f] at hkb <;> simp [hkb]
  classical
  -- task (in sorted index) at position p
  let T : Fin (2 * n) → ℕ := fun p => Classical.choose (hcover p.1 p.2)
  have hT : ∀ p : Fin (2 * n), T p < n ∧ (x (T p) = p.1 + 1 ∨ y (T p) = p.1 + 1) :=
    fun p => Classical.choose_spec (hcover p.1 p.2)
  refine ⟨fun p => σ ⟨T p, (hT p).1⟩, ?_⟩
  intro i
  set k : ℕ := (σ.symm i).1 with hkdef
  have hk : k < n := (σ.symm i).2
  have hσk : σ ⟨k, hk⟩ = i := by simp [k]
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1 k hk
  have hpx : x k - 1 < 2 * n := by omega
  have hqy : y k - 1 < 2 * n := by omega
  -- uniqueness: if position r holds task-index T r and that equals k
  have huniq : ∀ r : Fin (2 * n), (σ ⟨T r, (hT r).1⟩ = i) → T r = k := by
    intro r hr
    have : (⟨T r, (hT r).1⟩ : Fin n) = ⟨k, hk⟩ := by
      apply σ.injective; rw [hr, hσk]
    simpa using congrArg Fin.val this
  have hTx : T ⟨x k - 1, hpx⟩ = k := by
    obtain ⟨hlt, hor⟩ := hT ⟨x k - 1, hpx⟩
    rcases hor with h | h
    · exact h3 _ hlt k hk (by simp at h; omega)
    · exact absurd (by simp at h; omega : x k = y (T ⟨x k - 1, hpx⟩)) (h2 k hk _ hlt)
  have hTy : T ⟨y k - 1, hqy⟩ = k := by
    obtain ⟨hlt, hor⟩ := hT ⟨y k - 1, hqy⟩
    rcases hor with h | h
    · exact absurd (by simp at h; omega : x (T ⟨y k - 1, hqy⟩) = y k) (h2 _ hlt k hk)
    · exact h4 _ hlt k hk (by simp at h; omega)
  refine ⟨⟨x k - 1, hpx⟩, ⟨y k - 1, hqy⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Fin.lt_def]; omega
  · simp only; rw [show (⟨T ⟨x k - 1, hpx⟩, (hT _).1⟩ : Fin n) = ⟨k, hk⟩ by simp [hTx]]; exact hσk
  · simp only; rw [show (⟨T ⟨y k - 1, hqy⟩, (hT _).1⟩ : Fin n) = ⟨k, hk⟩ by simp [hTy]]; exact hσk
  · intro r hr
    have hTr := huniq r hr
    obtain ⟨_, hor⟩ := hT r
    rw [hTr] at hor
    rcases hor with h | h
    · left; ext; simp; omega
    · right; ext; simp; omega
  · have : (fun k => if h : k < n then d (σ ⟨k, h⟩) else 0) k = d i := by simp [hk, hσk]
    simp only; omega
  · have : (fun k => if h : k < n then d (σ ⟨k, h⟩) else 0) k = d i := by simp [hk, hσk]
    simp only; omega

/-- Sharpness: `k+1` tasks of deadline `k` admit no schedule (pigeonhole on first visits). -/
theorem not_schedulable_const (k : ℕ) :
    ¬ ∃ s : Fin (2 * (k + 1)) → Fin (k + 1), IsSchedule (k + 1) (fun _ => k) s := by
  rintro ⟨s, hs⟩
  classical
  choose p q hpq hp hq _ hpd _ using hs
  have hinj : Set.InjOn (fun i : Fin (k + 1) => (p i : ℕ)) (univ : Finset (Fin (k + 1))) := by
    intro i _ j _ hij
    have : p i = p j := Fin.ext hij
    rw [← hp i, ← hp j, this]
  have hmaps : ∀ i ∈ (univ : Finset (Fin (k + 1))), (fun i => (p i : ℕ)) i ∈ range k := by
    intro i _; simp only [mem_range]; have := hpd i; simp only at this; omega
  have := card_le_card_of_injOn _ hmaps hinj
  simp at this

/-! ### from B_hall.lean -/
/-- Threshold-dominance implies an assignment (Hall's theorem). -/
theorem assign (n : ℕ) (r e : ℕ → ℤ)
    (h : ∀ θ : ℤ, ((range n).filter (fun i => θ ≤ r i)).card ≤
      ((range n).filter (fun t => θ ≤ e t)).card) :
    ∃ τ : ℕ → ℕ, (∀ i < n, τ i < n) ∧ (∀ i < n, ∀ j < n, τ i = τ j → i = j) ∧
      ∀ i < n, r i ≤ e (τ i) := by
  classical
  let t : Fin n → Finset (Fin n) := fun i => univ.filter (fun j => r i ≤ e j)
  have hall : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion t).card := by
    intro S
    rcases S.eq_empty_or_nonempty with hS | hS
    · simp [hS]
    obtain ⟨i0, hi0, hmin⟩ := S.exists_min_image (fun i : Fin n => r i) hS
    have h1 : S.card ≤ ((range n).filter (fun i => r i0 ≤ r i)).card := by
      have : S.map Fin.valEmbedding ⊆ (range n).filter (fun i => r i0 ≤ r i) := by
        intro v hv
        simp only [mem_map, Fin.valEmbedding_apply] at hv
        obtain ⟨j, hj, rfl⟩ := hv
        simp [hmin j hj]
      simpa using card_le_card this
    have h2 : ((range n).filter (fun t => r i0 ≤ e t)).card ≤ (S.biUnion t).card := by
      have : (range n).filter (fun t => r i0 ≤ e t) ⊆ (S.biUnion t).map Fin.valEmbedding := by
        intro v hv
        simp only [mem_filter, mem_range] at hv
        simp only [mem_map, mem_biUnion, Fin.valEmbedding_apply]
        exact ⟨⟨v, hv.1⟩, ⟨i0, hi0, by simp [t, hv.2]⟩, rfl⟩
      simpa using card_le_card this
    exact h1.trans ((h (r i0)).trans h2)
  obtain ⟨f, hfinj, hf⟩ := (all_card_le_biUnion_card_iff_exists_injective t).1 hall
  refine ⟨fun i => if hi : i < n then (f ⟨i, hi⟩ : ℕ) else 0, ?_, ?_, ?_⟩
  · intro i hi; simp [hi]
  · intro i hi j hj hij
    simp only [hi, hj, dite_true] at hij
    have := hfinj (Fin.ext hij)
    simpa using congrArg Fin.val this
  · intro i hi
    have := hf ⟨i, hi⟩
    simp only [t, mem_filter, mem_univ, true_and] at this
    simpa [hi] using this

/-- An injective self-map of `range n` is surjective onto `range n`. -/
theorem surj_of_inj (n : ℕ) (τ : ℕ → ℕ) (h1 : ∀ i < n, τ i < n)
    (h2 : ∀ i < n, ∀ j < n, τ i = τ j → i = j) : ∀ t < n, ∃ i < n, τ i = t := by
  classical
  have hsub : (range n).image τ ⊆ range n := by
    intro v hv; simp only [mem_image, mem_range] at hv; obtain ⟨i, hi, rfl⟩ := hv; simp [h1 i hi]
  have hcard : ((range n).image τ).card = n := by
    rw [card_image_of_injOn]; · simp
    intro i hi j hj hij; exact h2 i (by simpa using hi) j (by simpa using hj) hij
  have heq : (range n).image τ = range n := eq_of_subset_of_card_le hsub (by simp [hcard])
  intro t ht
  have : t ∈ (range n).image τ := by rw [heq]; simpa using ht
  simp only [mem_image, mem_range] at this
  exact this

/-- Block from a permutation `π` of slots dominated (threshold-wise) by the task slacks. -/
theorem block_of_perm (n c : ℕ) (g : ℕ → ℕ) (π : ℕ → ℕ)
    (hπ : ∀ i < n, π i < n) (hπinj : ∀ i < n, ∀ j < n, π i = π j → i = j)
    (hdom : ∀ θ : ℤ,
      ((range n).filter (fun i => θ ≤ max ((π i : ℤ) - i) ((i : ℤ) + 1 + c - n))).card ≤
      ((range n).filter (fun t => θ ≤ (g t : ℤ) - n)).card) :
    ∃ sl sg : ℕ → ℕ, (∀ k < n, sl k < n ∧ sg k < n ∧ c + sl k + 1 ≤ g k ∧ n + sg k ≤ g k + sl k) ∧
      (∀ k < n, ∀ l < n, sl k = sl l → k = l) ∧ (∀ k < n, ∀ l < n, sg k = sg l → k = l) := by
  classical
  obtain ⟨τ, hτ1, hτ2, hτ3⟩ := assign n _ _ hdom
  have hsurj := surj_of_inj n τ hτ1 hτ2
  let sl : ℕ → ℕ := fun t => if ht : t < n then Classical.choose (hsurj t ht) else 0
  have hsl : ∀ t < n, sl t < n ∧ τ (sl t) = t := by
    intro t ht
    have := Classical.choose_spec (hsurj t ht)
    simp only [sl, ht, dite_true]; exact this
  refine ⟨sl, fun t => π (sl t), ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨a1, a2⟩ := hsl k hk
    have := hτ3 (sl k) a1
    rw [a2] at this
    refine ⟨a1, hπ _ a1, ?_, ?_⟩
    · have h' := (le_max_right _ _).trans this; omega
    · show n + π (sl k) ≤ g k + sl k
      have h' := (le_max_left _ _).trans this; omega
  · intro k hk l hl hkl
    rw [← (hsl k hk).2, ← (hsl l hl).2, hkl]
  · intro k hk l hl hkl
    have := hπinj _ (hsl k hk).1 _ (hsl l hl).1 hkl
    rw [← (hsl k hk).2, ← (hsl l hl).2, this]

/-! ### from C_chunk.lean -/
/-- Chunked rotations.  Deficits `δ 0 ≥ δ 1 ≥ … ≥ δ (d-1)` are grouped into consecutive chunks of
size `E` (last one possibly smaller); a chunk with leader `q = δ(first)` and `m` deficits occupies
`q + m` slots: `q` partner slots shifted forward by `m`, then the `m` deficit slots shifted back by `q`.
`π` is a permutation of `range W`, `s j` the slot of deficit `j`. -/
theorem chunk (E : ℕ) (hE : 1 ≤ E) : ∀ (d : ℕ) (δ : ℕ → ℕ), (∀ i j, i ≤ j → j < d → δ j ≤ δ i) →
    ∃ (W : ℕ) (π s : ℕ → ℕ),
      (∀ i < W, π i < W) ∧ (∀ i < W, ∀ j < W, π i = π j → i = j) ∧
      (∀ j < d, s j < W) ∧ (∀ j < d, ∀ j' < d, s j = s j' → j = j') ∧
      (∀ j < d, π (s j) + δ j ≤ s j) ∧
      (∀ j < d, E * s j ≤ E * (j + δ 0) + ∑ i ∈ range j, δ i) ∧
      (∀ i < W, (∀ j < d, s j ≠ i) → π i ≤ i + E) ∧
      (0 < d → W = s (d - 1) + 1) ∧ (d = 0 → W = 0) ∧
      (0 < d → E * W ≤ E * (d + δ 0) + ∑ i ∈ range d, δ i) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro δ hδ
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, id, id, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all
  set m := min d E with hm
  set q := δ 0 with hq
  set w := q + m with hw
  have hm1 : 1 ≤ m := by omega
  have hmd : m ≤ d := min_le_left _ _
  have hmE : m ≤ E := min_le_right _ _
  obtain ⟨W', π', s', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    IH (d - m) (by omega) (fun i => δ (m + i)) (by intro i j hij hj; exact hδ _ _ (by omega) (by omega))
  have hδq : ∀ j < d, δ j ≤ q := fun j hj => hδ 0 j (Nat.zero_le _) hj
  set π : ℕ → ℕ := fun i => if i < q then i + m else if i < w then i - q else w + π' (i - w)
    with hπdef
  set s : ℕ → ℕ := fun j => if j < m then q + j else w + s' (j - m) with hsdef
  have πA : ∀ i, i < q → π i = i + m := by intro i hi; simp [hπdef, hi]
  have πB : ∀ i, q ≤ i → i < w → π i = i - q := by
    intro i hi hi'; simp [hπdef, show ¬ i < q by omega, hi']
  have πC : ∀ i, w ≤ i → π i = w + π' (i - w) := by
    intro i hi; simp [hπdef, show ¬ i < q by omega, show ¬ i < w by omega]
  have sA : ∀ j, j < m → s j = q + j := by intro j hj; simp [hsdef, hj]
  have sB : ∀ j, m ≤ j → s j = w + s' (j - m) := by
    intro j hj; simp [hsdef, show ¬ j < m by omega]
  -- leader bound for a full chunk
  have hlead : m = E → d - m ≠ 0 → E * δ (m + 0) ≤ ∑ i ∈ range m, δ i := by
    intro hmE' _
    rw [← hmE']
    calc m * δ (m + 0) = ∑ _i ∈ range m, δ (m + 0) := by simp
      _ ≤ ∑ i ∈ range m, δ i := by
        apply Finset.sum_le_sum; intro i hi; simp at hi; exact hδ _ _ (by omega) (by omega)
  refine ⟨w + W', π, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases a : i < q
    · rw [πA i a]; omega
    by_cases b : i < w
    · rw [πB i (by omega) b]; omega
    · rw [πC i (by omega)]; have := h1 (i - w) (by omega); omega
  · intro i hi j hj hij
    rcases lt_or_ge i q with a | a <;> rcases lt_or_ge i w with b | b <;>
      rcases lt_or_ge j q with a' | a' <;> rcases lt_or_ge j w with b' | b' <;> try omega
    all_goals
      first
      | (rw [πA i a, πA j a'] at hij; omega)
      | (rw [πA i a, πB j a' b'] at hij; omega)
      | (rw [πB i a b, πA j a'] at hij; omega)
      | (rw [πB i a b, πB j a' b'] at hij; omega)
      | (rw [πA i a, πC j b'] at hij; omega)
      | (rw [πC i b, πA j a'] at hij; omega)
      | (rw [πB i a b, πC j b'] at hij; omega)
      | (rw [πC i b, πB j a' b'] at hij; omega)
      | (rw [πC i b, πC j b'] at hij
         have := h2 (i - w) (by omega) (j - w) (by omega) (by omega); omega)
  · intro j hj
    by_cases a : j < m
    · rw [sA j a]; omega
    · rw [sB j (by omega)]; have := h3 (j - m) (by omega); omega
  · intro j hj j' hj' hjj
    rcases lt_or_ge j m with a | a <;> rcases lt_or_ge j' m with a' | a'
    · rw [sA j a, sA j' a'] at hjj; omega
    · rw [sA j a, sB j' a'] at hjj; omega
    · rw [sB j a, sA j' a'] at hjj; omega
    · rw [sB j a, sB j' a'] at hjj
      have := h4 (j - m) (by omega) (j' - m) (by omega) (by omega); omega
  · intro j hj
    by_cases a : j < m
    · rw [sA j a, πB (q + j) (by omega) (by omega)]
      have := hδq j hj; omega
    · rw [sB j (by omega), πC _ (by omega)]
      have := h5 (j - m) (by omega)
      rw [show m + (j - m) = j by omega] at this
      rw [show w + s' (j - m) - w = s' (j - m) by omega]
      omega
  · intro j hj
    by_cases a : j < m
    · rw [sA j a, show q + j = j + δ 0 by omega]
      exact Nat.le_add_right _ _
    · obtain ⟨j', rfl⟩ : ∃ j', j = m + j' := ⟨j - m, by omega⟩
      have hmE' : m = E := by omega
      rw [sB _ (by omega), show m + j' - m = j' by omega]
      have hj' := h6 j' (by omega)
      have hl := hlead hmE' (by omega)
      rw [Finset.sum_range_add]
      have e1 : E * (w + s' j') = E * δ 0 + E * E + E * s' j' := by rw [hw, hq, hmE']; ring
      have e2 : E * (m + j' + δ 0) = E * E + E * j' + E * δ 0 := by rw [hmE']; ring
      have e3 : E * (j' + δ (m + 0)) = E * j' + E * δ (m + 0) := by ring
      rw [e1, e2]; rw [e3] at hj'
      omega
  · intro i hi hns
    by_cases a : i < q
    · rw [πA i a]; omega
    by_cases b : i < w
    · exfalso; exact hns (i - q) (by omega) (by rw [sA _ (by omega)]; omega)
    · rw [πC i (by omega)]
      have : ∀ j < d - m, s' j ≠ i - w := by
        intro j hj hji
        exact hns (m + j) (by omega) (by rw [sB _ (by omega), show m + j - m = j by omega, hji]; omega)
      have := h7 (i - w) (by omega) this
      omega
  · intro _
    by_cases hdm : d - m = 0
    · have := h9 hdm
      rw [sA _ (by omega)]; omega
    · have := h8 (by omega)
      rw [sB _ (by omega), show d - 1 - m = d - m - 1 by omega]; omega
  · intro h; omega
  · intro _
    by_cases hdm : d - m = 0
    · have := h9 hdm
      have : m = d := by omega
      rw [show w + W' = d + δ 0 by omega]
      exact Nat.le_add_right _ _
    · have hmE' : m = E := by omega
      have hW := h10 (by omega)
      have hl := hlead hmE' hdm
      obtain ⟨d', hd'⟩ : ∃ d', d = m + d' := ⟨d - m, by omega⟩
      rw [show d - m = d' by omega] at hW
      rw [hd', Finset.sum_range_add]
      have e1 : E * (w + W') = E * δ 0 + E * E + E * W' := by rw [hw, hq, hmE']; ring
      have e2 : E * (m + d' + δ 0) = E * E + E * d' + E * δ 0 := by rw [hmE']; ring
      have e3 : E * (d' + δ (m + 0)) = E * d' + E * δ (m + 0) := by ring
      rw [e1, e2]; rw [e3] at hW
      omega

/-! ### from D_T.lean -/
theorem tangent (x T : ℚ) (hx : 0 < x) (hT : 0 < T) : 2 / T - x / T ^ 2 ≤ 1 / x := by
  have h : 1 / x - (2 / T - x / T ^ 2) = (x - T) ^ 2 / (x * T ^ 2) := by
    field_simp; ring
  have : 0 ≤ (x - T) ^ 2 / (x * T ^ 2) := by positivity
  linarith

/-- Slot lemma core inequality (rational form). -/
theorem Tlemma (n c J : ℕ) (u : ℕ → ℚ) (hc : 1 ≤ c) (hJ : 1 ≤ J) (hn : 1 ≤ n)
    (hpos : 0 < u 0) (hmono : ∀ i < J, u 0 ≤ u i) (hlast : ∀ i < J, u i ≤ u (J - 1))
    (hub : u (J - 1) ≤ (n : ℚ) - 1)
    (hH : ∑ i ∈ range J, 1 / u i + c / (2 * u 0) ≤ ((J : ℚ) + c) / ((n : ℚ) + c)) :
    ((n : ℚ) + c + J) + 2 * ((J : ℚ) - 1) * n / c ≤
      u 0 + u (J - 1) + 2 / c * (∑ i ∈ range J, u i - u (J - 1)) := by
  have hcq : (1 : ℚ) ≤ c := by exact_mod_cast hc
  have hJq : (1 : ℚ) ≤ J := by exact_mod_cast hJ
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  set N : ℚ := (n : ℚ) + c with hN
  have hNpos : 0 < N := by rw [hN]; linarith
  set us : ℚ := N * (2 * J + c) / (2 * (J + c)) with hus
  have huspos : 0 < us := by rw [hus]; positivity
  have hupos : ∀ i < J, 0 < u i := fun i hi => lt_of_lt_of_le hpos (hmono i hi)
  set S : ℚ := ∑ i ∈ range J, u i with hS
  -- tangent bound on H
  have htan : (2 * J + c) / us - (S + c / 2 * u 0) / us ^ 2 ≤
      ∑ i ∈ range J, 1 / u i + c / (2 * u 0) := by
    have h1 : ∑ i ∈ range J, (2 / us - u i / us ^ 2) ≤ ∑ i ∈ range J, 1 / u i :=
      Finset.sum_le_sum (fun i hi => tangent _ _ (hupos i (by simpa using hi)) huspos)
    have h2 : (c : ℚ) / 2 * (2 / us - u 0 / us ^ 2) ≤ c / (2 * u 0) := by
      have := tangent (u 0) us hpos huspos
      have e : (c : ℚ) / (2 * u 0) = c / 2 * (1 / u 0) := by field_simp
      rw [e]; exact mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : ∑ i ∈ range J, (2 / us - u i / us ^ 2) = 2 * J / us - S / us ^ 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul, ← Finset.sum_div, ← hS]
      ring
    have : (2 * J + c) / us - (S + c / 2 * u 0) / us ^ 2 =
        (2 * J / us - S / us ^ 2) + c / 2 * (2 / us - u 0 / us ^ 2) := by
      field_simp; ring
    linarith
  -- lower bound on Lin = S + c/2 u0
  have hLin : N * (2 * J + c) ^ 2 / (4 * (J + c)) ≤ S + c / 2 * u 0 := by
    have hcomb : (2 * J + c) / us - (S + c / 2 * u 0) / us ^ 2 ≤ (J + c) / N := le_trans htan hH
    have hval : (2 * J + c) / us - (J + c) / N = N * (2 * J + c) ^ 2 / (4 * (J + c)) / us ^ 2 := by
      rw [hus]; field_simp; ring
    have : N * (2 * J + c) ^ 2 / (4 * (J + c)) / us ^ 2 ≤ (S + c / 2 * u 0) / us ^ 2 := by
      linarith
    exact (div_le_div_iff_of_pos_right (by positivity)).1 this
  -- lower bound on last
  have hLast : us ≤ u (J - 1) := by
    have hl : ((J : ℚ) + c / 2) / u (J - 1) ≤ ∑ i ∈ range J, 1 / u i + c / (2 * u 0) := by
      have hJ1 : J - 1 < J := by omega
      have h1 : ∑ i ∈ range J, 1 / u (J - 1) ≤ ∑ i ∈ range J, 1 / u i := by
        apply Finset.sum_le_sum; intro i hi
        exact one_div_le_one_div_of_le (hupos i (by simpa using hi)) (hlast i (by simpa using hi))
      have h2 : (c : ℚ) / (2 * u (J - 1)) ≤ c / (2 * u 0) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith [hmono (J - 1) hJ1]
      have e : ((J : ℚ) + c / 2) / u (J - 1) = ∑ i ∈ range J, 1 / u (J - 1) + c / (2 * u (J - 1)) := by
        simp; field_simp
      linarith
    have hl2 := le_trans hl hH
    have hpl : 0 < u (J - 1) := hupos (J - 1) (by omega)
    rw [div_le_div_iff₀ hpl hNpos] at hl2
    rw [hus, div_le_iff₀ (by positivity)]
    nlinarith
  -- Lu identity
  have hLu : u 0 + u (J - 1) + 2 / c * (S - u (J - 1)) =
      2 / c * (S + c / 2 * u 0) + (1 - 2 / c) * u (J - 1) := by
    field_simp; ring
  rw [hLu]
  rcases eq_or_lt_of_le hcq with hc1 | hc2
  · -- c = 1
    rw [← hc1] at hLin ⊢
    have hNn : N = n + 1 := by rw [hN, ← hc1]
    rw [hNn] at hLin
    have e : ((n : ℚ) + 1) * (2 * J + 1) ^ 2 / (4 * (J + 1)) =
        (n + 1) * J + (n + 1) / (4 * (J + 1)) := by field_simp; ring
    rw [e] at hLin
    have : 0 ≤ ((n : ℚ) + 1) / (4 * (J + 1)) := by positivity
    norm_num
    linarith
  · -- c ≥ 2
    have hc2' : (2 : ℚ) ≤ c := by
      have : (2 : ℕ) ≤ c := by
        by_contra h; push_neg at h; interval_cases c; norm_num at hc2
      exact_mod_cast this
    have hcoef : 0 ≤ 1 - 2 / (c : ℚ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hc2'
    have step1 : 2 / c * (N * (2 * J + c) ^ 2 / (4 * (J + c))) + (1 - 2 / c) * us ≤
        2 / c * (S + c / 2 * u 0) + (1 - 2 / c) * u (J - 1) := by
      have a := mul_le_mul_of_nonneg_left hLin (show (0 : ℚ) ≤ 2 / c by positivity)
      have b := mul_le_mul_of_nonneg_left hLast hcoef
      linarith
    refine le_trans ?_ step1
    rw [hus]
    have key : 2 / (c : ℚ) * (N * (2 * J + c) ^ 2 / (4 * (J + c))) +
        (1 - 2 / c) * (N * (2 * J + c) / (2 * (J + c))) -
        ((n + c + J) + 2 * (J - 1) * n / c) = (J - 2) + N / (J + c) := by
      rw [hN]; field_simp; ring
    have : (0 : ℚ) ≤ (J - 2) + N / (J + c) := by
      rcases eq_or_lt_of_le hJq with h1 | h1
      · rw [← h1]
        have : (1 : ℚ) ≤ N / (1 + c) := by
          rw [le_div_iff₀ (by positivity), hN]; linarith
        linarith
      · have hJ2 : (2 : ℚ) ≤ J := by
          have : (2 : ℕ) ≤ J := by
            by_contra h; push_neg at h; interval_cases J; norm_num at h1
          exact_mod_cast this
        have : 0 ≤ N / (J + c) := by positivity
        linarith
    linarith

/-! ### from D_Z.lean -/
/-- Partner-dominance core inequality (rational form). -/
theorem Zlemma (n c t d p Zb Δ δ0 H : ℚ) (hn : 0 < n) (hc : 1 ≤ c) (ht : 0 ≤ t) (htc : 2 * t + 1 ≤ c)
    (hd : 0 ≤ d) (hΔ : 0 ≤ Δ) (hδ0 : 0 ≤ δ0) (hpd : d ≤ p)
    (hHt : ((d + c / 2) * n + Δ + c * δ0 / 2) / n ^ 2 ≤ H)
    (hi : H + (p - d) / (n + t) + (n - p) / (n + c) ≤ 1)
    (hQ1 : 2 * Δ ≤ c * (n - c - 2 * d - δ0))
    (hZb : c * Zb ≤ c * δ0 + 2 * Δ) :
    p + Zb ≤ n - c + t := by
  set M := c - t with hM
  have hMpos : 0 < M := by rw [hM]; linarith
  have hnt : 0 < n + t := by linarith
  have hN : 0 < n + c := by linarith
  have hcpos : 0 < c := by linarith
  -- (p-d) M ≤ (n+t) ((c+d) - (n+c) H)
  have h1 : (p - d) * M ≤ (n + t) * ((c + d) - (n + c) * H) := by
    have e : (p - d) / (n + t) + (n - p) / (n + c) = (n - d) / (n + c) + (p - d) * M / ((n + t) * (n + c)) := by
      rw [hM]; field_simp; ring
    have hi2 : H + ((n - d) / (n + c) + (p - d) * M / ((n + t) * (n + c))) ≤ 1 := by
      rw [← e]; linarith
    have : (p - d) * M / ((n + t) * (n + c)) ≤ 1 - H - (n - d) / (n + c) := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    have e2 : (1 - H - (n - d) / (n + c)) * ((n + t) * (n + c)) = (n + t) * ((c + d) - (n + c) * H) := by
      field_simp; ring
    linarith
  have h2 : (n + t) * ((c + d) - (n + c) * H) ≤
      (n + t) * ((c + d) - (n + c) * (((d + c / 2) * n + Δ + c * δ0 / 2) / n ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hnt)
    nlinarith
  have h3 : M * Zb ≤ M * (δ0 + 2 * Δ / c) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hMpos)
    rw [show δ0 + 2 * Δ / c = (c * δ0 + 2 * Δ) / c by field_simp]
    rw [le_div_iff₀ hcpos]; linarith
  -- key identity
  set Q1e := n - c - 2 * d - δ0 - 2 * Δ / c with hQ1e
  have hQ1e' : 0 ≤ Q1e := by
    rw [hQ1e]
    have : 2 * Δ / c ≤ n - c - 2 * d - δ0 := by rw [div_le_iff₀ hcpos]; linarith
    linarith
  set rest := Δ * (c * n + c * t + n * t) + δ0 * (c ^ 2 * n / 2 + c ^ 2 * t / 2 + c * n * t / 2) +
    d * n * (n * (c - t) + c * t) + n * t * (c ^ 2 / 2 + n * (c / 2 - t)) with hrest
  have hrest' : 0 ≤ rest := by
    rw [hrest]
    have a1 : 0 ≤ c - t := by linarith
    have a2 : 0 ≤ c / 2 - t := by linarith
    positivity
  have key : M * (n - c + t) - ((n + t) * ((c + d) - (n + c) * (((d + c / 2) * n + Δ + c * δ0 / 2) / n ^ 2))
      + M * d + M * (δ0 + 2 * Δ / c)) = (c - 2 * t) / 2 * Q1e + rest / n ^ 2 := by
    rw [hM, hQ1e, hrest]; field_simp; ring
  have h4 : 0 ≤ (c - 2 * t) / 2 * Q1e + rest / n ^ 2 := by
    have : 0 ≤ (c - 2 * t) / 2 := by linarith
    positivity
  have h5 : M * (p + Zb) ≤ M * (n - c + t) := by nlinarith
  exact le_of_mul_le_mul_left h5 hMpos

/-! ### from D_core.lean -/
theorem chord (x x0 C D : ℚ) (hD : 0 ≤ D) (h0 : D < x0) (hx0 : x0 ≤ x) (hxC : x ≤ C) :
    1 / (x - D) ≤ (x0 * C / x - D) / ((x0 - D) * (C - D)) := by
  have hxD : 0 < x - D := by linarith
  have hx : 0 < x := by linarith
  have hCD : 0 < C - D := by linarith
  have hx0D : 0 < x0 - D := by linarith
  rw [div_le_div_iff₀ hxD (by positivity)]
  have e : (x0 * C / x - D) * (x - D) = ((x - D) * (x0 * C - D * x)) / x := by field_simp
  rw [e, le_div_iff₀ hx]
  nlinarith [mul_nonneg (mul_nonneg hD (sub_nonneg.2 hx0)) (sub_nonneg.2 hxC)]

/-- Core lemma (rational form): after peeling `D` top tasks the core still satisfies (i). -/
theorem corelemma (c W D : ℕ) (x : ℕ → ℚ) (hW : 1 ≤ W) (hint : ∃ m : ℕ, x 0 = m)
    (hx0 : (c : ℚ) + 1 ≤ x 0) (hmono : ∀ k < W, x 0 ≤ x k) (hC : ∀ k < W, x k ≤ c + W)
    (hS : ∑ k ∈ range W, 1 / x k + c / (2 * x 0) + D / ((c : ℚ) + 2 * W + D - 1) ≤ 1) :
    (D = 0 ∨ D < c) ∧
    ∑ k ∈ range W, 1 / (x k - D) + ((c : ℚ) - D) / (2 * (x 0 - D)) ≤ 1 := by
  have hWq : (1 : ℚ) ≤ W := by exact_mod_cast hW
  have hcq : (0 : ℚ) ≤ c := by exact_mod_cast Nat.zero_le c
  have hDq : (0 : ℚ) ≤ D := by exact_mod_cast Nat.zero_le D
  set C : ℚ := c + W with hCdef
  set Qn : ℚ := c + 2 * W + D - 1 with hQn
  have hQpos : 0 < Qn := by rw [hQn]; linarith
  have hx0pos : 0 < x 0 := by linarith
  have hxpos : ∀ k < W, 0 < x k := fun k hk => lt_of_lt_of_le hx0pos (hmono k hk)
  have hx0C : x 0 ≤ C := hC 0 (by omega)
  set Y : ℚ := ∑ k ∈ range W, 1 / x k with hY
  -- (a)
  have ha : D = 0 ∨ D < c := by
    have hY1 : (W - 1 : ℚ) / C + 1 / x 0 ≤ Y := by
      rw [hY]
      have : ∑ k ∈ range W, 1 / x k = 1 / x 0 + ∑ k ∈ (range W).erase 0, 1 / x k :=
        (Finset.add_sum_erase (range W) (fun k => 1 / x k) (by simp; omega)).symm
      rw [this]
      have : ((W : ℚ) - 1) / C ≤ ∑ k ∈ (range W).erase 0, 1 / x k := by
        have hc : (((range W).erase 0).card : ℚ) = W - 1 := by
          rw [Finset.card_erase_of_mem (by simp; omega)]; simp; push_cast [Nat.cast_sub hW]; ring
        calc ((W : ℚ) - 1) / C = ∑ k ∈ (range W).erase 0, 1 / C := by
              rw [Finset.sum_const, nsmul_eq_mul, hc]; ring
          _ ≤ ∑ k ∈ (range W).erase 0, 1 / x k := by
              apply Finset.sum_le_sum; intro k hk
              simp at hk
              exact one_div_le_one_div_of_le (hxpos k hk.2) (hC k hk.2)
      linarith
    have hCpos : 0 < C := by rw [hCdef]; linarith
    have h1 : (1 + c / 2) / C ≤ 1 / x 0 + c / (2 * x 0) := by
      have : (1 + c / 2) / C ≤ (1 + c / 2) / x 0 := div_le_div_of_nonneg_left (by positivity) hx0pos hx0C
      have e : (1 + (c : ℚ) / 2) / x 0 = 1 / x 0 + c / (2 * x 0) := by field_simp
      linarith
    have h2 : (W + c / 2 : ℚ) / C + D / Qn ≤ 1 := by
      have e : (W + (c : ℚ) / 2) / C = (W - 1) / C + (1 + c / 2) / C := by field_simp; ring
      linarith
    have h3 : 2 * D * C ≤ c * Qn := by
      have e : (W + (c : ℚ) / 2) / C = 1 - (c / 2) / C := by rw [hCdef]; field_simp; ring
      rw [e] at h2
      have : (D : ℚ) / Qn ≤ (c / 2) / C := by linarith
      rw [div_le_div_iff₀ hQpos hCpos] at this
      linarith
    by_contra hcon
    push_neg at hcon
    obtain ⟨hD0, hDc⟩ := hcon
    have hDc' : (c : ℚ) ≤ D := by exact_mod_cast hDc
    have hD1 : (1 : ℚ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hD0
    rw [hCdef, hQn] at h3
    nlinarith
  refine ⟨ha, ?_⟩
  rcases ha with hD0 | hDc
  · subst hD0; simp only [Nat.cast_zero, sub_zero]; linarith [div_nonneg (Nat.cast_nonneg 0 : (0:ℚ) ≤ (0:ℕ)) hQpos.le]
  have hDc' : (D : ℚ) + 1 ≤ c := by exact_mod_cast hDc
  have hx0D : (D : ℚ) < x 0 := by linarith
  have hCD : (D : ℚ) < C := by rw [hCdef]; linarith
  -- chord sum
  have hchord : ∑ k ∈ range W, 1 / (x k - D) ≤ (x 0 * C * Y - W * D) / ((x 0 - D) * (C - D)) := by
    calc ∑ k ∈ range W, 1 / (x k - D) ≤ ∑ k ∈ range W, (x 0 * C / x k - D) / ((x 0 - D) * (C - D)) := by
          apply Finset.sum_le_sum; intro k hk; simp at hk
          exact chord _ _ _ _ hDq hx0D (hmono k hk) (hC k hk)
      _ = (x 0 * C * Y - W * D) / ((x 0 - D) * (C - D)) := by
          rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul, hY,
            Finset.mul_sum]
          congr 1; congr 1; apply Finset.sum_congr rfl; intro k hk; ring
  have hx0D' : 0 < x 0 - D := by linarith
  have hCD' : 0 < C - D := by linarith
  -- reduce goal
  suffices hsuff : (x 0 * C * Y - W * D) / (C - D) + (c - D) / 2 ≤ x 0 - D by
    have e : (x 0 * C * Y - W * D) / ((x 0 - D) * (C - D)) + ((c : ℚ) - D) / (2 * (x 0 - D)) =
        ((x 0 * C * Y - W * D) / (C - D) + (c - D) / 2) / (x 0 - D) := by field_simp
    have : ((x 0 * C * Y - W * D) / (C - D) + (c - D) / 2) / (x 0 - D) ≤ 1 := by
      rw [div_le_one hx0D']; exact hsuff
    linarith
  by_cases hcase : 2 * W + c + D ≤ 2 * x 0
  · -- case A
    have hYW : Y ≤ W / x 0 := by
      rw [hY]
      calc ∑ k ∈ range W, 1 / x k ≤ ∑ k ∈ range W, 1 / x 0 := by
            apply Finset.sum_le_sum; intro k hk; simp at hk
            exact one_div_le_one_div_of_le hx0pos (hmono k hk)
        _ = W / x 0 := by simp; ring
    have : x 0 * C * Y ≤ C * W := by
      have := mul_le_mul_of_nonneg_left hYW (show 0 ≤ x 0 * C by positivity)
      rw [show x 0 * C * (W / x 0) = C * W by field_simp] at this
      linarith
    have : (x 0 * C * Y - W * D) / (C - D) ≤ W := by
      rw [div_le_iff₀ hCD']; nlinarith
    linarith
  · -- case B
    push_neg at hcase
    have hcase' : 2 * x 0 ≤ Qn := by
      obtain ⟨m, hm⟩ := hint
      rw [hm] at hcase ⊢
      have : 2 * m < 2 * W + c + D := by exact_mod_cast hcase
      have : 2 * m + 1 ≤ 2 * W + c + D := this
      rw [hQn]
      have : ((2 * m + 1 : ℕ) : ℚ) ≤ ((2 * W + c + D : ℕ) : ℚ) := by exact_mod_cast this
      push_cast at this
      linarith
    have hYB : Y ≤ 1 - D / Qn - c / (2 * x 0) := by linarith
    have : x 0 * C * Y ≤ C * (x 0 - x 0 * D / Qn - c / 2) := by
      have := mul_le_mul_of_nonneg_left hYB (show 0 ≤ x 0 * C by positivity)
      have e : x 0 * C * (1 - D / Qn - c / (2 * x 0)) = C * (x 0 - x 0 * D / Qn - c / 2) := by
        field_simp
      linarith
    rw [div_add' _ _ _ (ne_of_gt hCD'), div_le_iff₀ hCD']
    have hkey : (x 0 - D) * (C - D) - (C * (x 0 - x 0 * D / Qn - c / 2) - W * D + (c - D) / 2 * (C - D))
        = D * ((D + W) / 2 - x 0 * (W + D - 1) / Qn) := by
      rw [hCdef]; field_simp; rw [hQn]; ring
    have hpos : 0 ≤ D * ((D + W) / 2 - x 0 * (W + D - 1) / Qn) := by
      apply mul_nonneg hDq
      have : x 0 * (W + D - 1) / Qn ≤ (W + D - 1) / 2 := by
        rw [div_le_div_iff₀ hQpos (by norm_num)]
        have : (0 : ℚ) ≤ W + D - 1 := by linarith
        nlinarith
      linarith
    nlinarith


/-! ### prefix counts and block for C-instances -/

/-- For monotone `g` on `range n`, `{k < n | g k < T}` is an initial segment. -/
theorem prefix_count (n T : ℕ) (g : ℕ → ℕ) (hmono : ∀ i j, i ≤ j → j < n → g i ≤ g j) :
    ∃ p ≤ n, ∀ k < n, (g k < T ↔ k < p) := by
  classical
  by_cases h : ∃ k < n, T ≤ g k
  · obtain ⟨hp1, hp2⟩ := Nat.find_spec h
    refine ⟨Nat.find h, le_of_lt hp1, ?_⟩
    intro k hk
    constructor
    · intro hgk
      by_contra hkp; push_neg at hkp
      have := hmono (Nat.find h) k hkp hk
      omega
    · intro hkp
      by_contra hgk; push_neg at hgk
      exact Nat.find_min h hkp ⟨hk, hgk⟩
  · push_neg at h
    exact ⟨n, le_refl _, fun k hk => ⟨fun _ => hk, fun _ => h k hk⟩⟩

theorem card_filter_lt (n p : ℕ) (P : ℕ → Prop) [DecidablePred P] (hp : p ≤ n)
    (h : ∀ k < n, (P k ↔ k < p)) : ((range n).filter P).card = p := by
  have : (range n).filter P = range p := by
    ext k; simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hk, hP⟩; exact (h k hk).1 hP
    · intro hk; exact ⟨by omega, (h k (by omega)).2 hk⟩
  rw [this, card_range]


theorem slot_arith (c E s j δ0 δj Dj n : ℕ) (hc : 1 ≤ c) (hE : 1 ≤ E) (hcE : c ≤ 2 * E)
    (h1 : E * s ≤ E * (j + δ0) + Dj) (h2 : c * (c + j + 1 + δ0 + δj) + 2 * Dj ≤ c * n) :
    c + s + 1 + δj ≤ n := by
  have h3 : c * s ≤ c * (j + δ0) + 2 * Dj := by
    have a : E * (c * s) ≤ E * (c * (j + δ0) + 2 * Dj) := by
      have := Nat.mul_le_mul_left c h1
      have b : c * Dj ≤ 2 * E * Dj := Nat.mul_le_mul_right Dj hcE
      nlinarith
    exact Nat.le_of_mul_le_mul_left a (by omega)
  by_contra hcon
  push_neg at hcon
  have : c * n < c * (c + s + 1 + δj) := Nat.mul_lt_mul_of_pos_left hcon (by omega)
  nlinarith

/-- Block lemma for C-instances. -/
theorem cblock (n c : ℕ) (g : ℕ → ℕ) (hmono : ∀ i j, i ≤ j → j < n → g i ≤ g j)
    (hii : ∀ k < n, c + k + 1 ≤ g k) (hC : ∀ k < n, g k ≤ c + n)
    (hi : 0 < n → ∑ k ∈ range n, (1 : ℚ) / g k + c / (2 * g 0) ≤ 1) :
    ∃ sl sg : ℕ → ℕ, (∀ k < n, sl k < n ∧ sg k < n ∧ c + sl k + 1 ≤ g k ∧ n + sg k ≤ g k + sl k) ∧
      (∀ k < n, ∀ l < n, sl k = sl l → k = l) ∧ (∀ k < n, ∀ l < n, sg k = sg l → k = l) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; exact ⟨id, id, by simp, by simp, by simp⟩
  have hi' := hi hnpos
  obtain ⟨d, hdn, hd⟩ := prefix_count n n g hmono
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- no deficits: identity
    refine ⟨id, id, ?_, ?_, ?_⟩
    · intro k hk
      have h1 := hii k hk
      have h2 : ¬ g k < n := fun h => by have := (hd k hk).1 h; omega
      simp only [id]; omega
    · intro k _ l _ h; exact h
    · intro k _ l _ h; exact h
  -- positivity facts
  have hgpos : ∀ k < n, (0 : ℚ) < g k := fun k hk => by
    have := hii k hk; exact_mod_cast (show 0 < g k by omega)
  have hnq : (0 : ℚ) < n := by exact_mod_cast hnpos
  -- lower bound: tasks ≥ J contribute ≥ 1/(n+c)
  have hrest : ∀ J ≤ n, ∑ k ∈ range J, (1 : ℚ) / g k + (n - J) / ((n : ℚ) + c) ≤
      ∑ k ∈ range n, (1 : ℚ) / g k := by
    intro J hJ
    rw [← Finset.sum_range_add_sum_Ico _ hJ]
    have : ((n : ℚ) - J) / (n + c) ≤ ∑ k ∈ Ico J n, (1 : ℚ) / g k := by
      calc ((n : ℚ) - J) / (n + c) = ∑ k ∈ Ico J n, (1 : ℚ) / (n + c) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; push_cast [Nat.cast_sub hJ]; ring
        _ ≤ ∑ k ∈ Ico J n, (1 : ℚ) / g k := by
            apply Finset.sum_le_sum; intro k hk; simp at hk
            apply one_div_le_one_div_of_le (hgpos k hk.2)
            have := hC k hk.2
            have : g k ≤ n + c := by omega
            exact_mod_cast this
    linarith
  -- c ≥ 1
  have hc1 : 1 ≤ c := by
    by_contra hc; push_neg at hc
    have hc0 : c = 0 := by omega
    subst hc0
    have h0 : g 0 < n := (hd 0 hnpos).2 hdpos
    have h1 := hrest 1 hnpos
    rw [Finset.sum_range_one] at h1
    simp only [Nat.cast_zero, add_zero, zero_div] at h1 hi'
    have hlt : (1 : ℚ) / n < 1 / g 0 := by
      apply one_div_lt_one_div_of_lt (hgpos 0 hnpos); exact_mod_cast h0
    have e : (1 : ℚ) / n + (n - 1) / n = 1 := by field_simp; ring
    linarith
  -- deficits
  set δ : ℕ → ℕ := fun j => n - g j with hδ
  set E := (c + 1) / 2 with hEdef
  have hE1 : 1 ≤ E := by omega
  have hcE : c ≤ 2 * E := by omega
  have hdef : ∀ j < d, g j < n := fun j hj => (hd j (by omega)).2 hj
  have hδmono : ∀ i j, i ≤ j → j < d → δ j ≤ δ i := by
    intro i j hij hj; simp only [hδ]; have := hmono i j hij (by omega); omega
  have hδg : ∀ j < d, g j + δ j = n := by intro j hj; have := hdef j hj; simp only [hδ]; omega
  obtain ⟨W, π0, s, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10⟩ := chunk E hE1 d δ hδmono
  have hHJ : ∀ J ≤ n, ∑ i ∈ range J, (1 : ℚ) / g i + c / (2 * g 0) ≤ ((J : ℚ) + c) / ((n : ℚ) + c) := by
    intro J hJ
    have := hrest J hJ
    have e : ((J : ℚ) + c) / (n + c) = 1 - (n - J) / (n + c) := by field_simp; ring
    rw [e]; linarith
  -- (S)
  have hS : ∀ j < d, c + s j + 1 + δ j ≤ n := by
    intro j hj
    have hub : (g j : ℚ) ≤ (n : ℚ) - 1 := by
      have := hdef j hj; have : g j + 1 ≤ n := this
      have : ((g j + 1 : ℕ) : ℚ) ≤ n := by exact_mod_cast this
      push_cast at this; linarith
    have hT := Tlemma n c (j + 1) (fun i => (g i : ℚ)) hc1 (by omega) hnpos (hgpos 0 hnpos)
      (fun i hi => by exact_mod_cast hmono 0 i (by omega) (by omega))
      (fun i hi => by simp only [Nat.add_sub_cancel]; exact_mod_cast hmono i j (by omega) (by omega))
      (by simpa using hub) (hHJ (j + 1) (by omega))
    simp only [Nat.add_sub_cancel, Finset.sum_range_succ, add_sub_cancel_right] at hT
    -- G_j + D_j = j n
    have hGD : ∑ i ∈ range j, g i + ∑ i ∈ range j, δ i = j * n := by
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun i hi => hδg i (by simp at hi; omega))]
      simp
    have hcq : (0 : ℚ) < c := by exact_mod_cast (show 0 < c by omega)
    have h2q : (c : ℚ) * (c + j + 1 + δ 0 + δ j) + 2 * (∑ i ∈ range j, δ i : ℕ) ≤ c * n := by
      have hG : ((∑ i ∈ range j, g i : ℕ) : ℚ) = ∑ i ∈ range j, (g i : ℚ) := by push_cast; rfl
      have hGD' : ((∑ i ∈ range j, g i : ℕ) : ℚ) + ((∑ i ∈ range j, δ i : ℕ) : ℚ) = j * n := by
        exact_mod_cast hGD
      have h0 : (g 0 : ℚ) + δ 0 = n := by exact_mod_cast hδg 0 (by omega)
      have hj' : (g j : ℚ) + δ j = n := by exact_mod_cast hδg j hj
      rw [← hG] at hT
      have := mul_le_mul_of_nonneg_left hT (le_of_lt hcq)
      have e1 : (c : ℚ) * ((n + c + (j + 1 : ℕ)) + 2 * (((j + 1 : ℕ) : ℚ) - 1) * n / c) =
          c * (n + c + j + 1) + 2 * j * n := by push_cast; field_simp; ring
      have e2 : (c : ℚ) * (g 0 + g j + 2 / c * ((∑ i ∈ range j, g i : ℕ) : ℚ)) =
          c * (g 0 + g j) + 2 * ((∑ i ∈ range j, g i : ℕ) : ℚ) := by field_simp
      rw [e1, e2] at this
      nlinarith
    have h2 : c * (c + j + 1 + δ 0 + δ j) + 2 * (∑ i ∈ range j, δ i) ≤ c * n := by exact_mod_cast h2q
    exact slot_arith c E (s j) j (δ 0) (δ j) (∑ i ∈ range j, δ i) n hc1 hE1 hcE (P6 j hj) h2
  have hδpos : ∀ j < d, 1 ≤ δ j := by intro j hj; have := hdef j hj; simp only [hδ]; omega
  have hW : c + W + 1 ≤ n := by
    have h8 := P8 hdpos
    have := hS (d - 1) (by omega)
    have := hδpos (d - 1) (by omega)
    omega
  set π : ℕ → ℕ := fun i => if i < W then π0 i else i with hπ
  have hπW : ∀ i < W, π i = π0 i := fun i hi => by simp [hπ, hi]
  have hπW' : ∀ i, W ≤ i → π i = i := fun i hi => by simp [hπ, show ¬ i < W by omega]
  -- requirement of deficit slots
  have hreqdef : ∀ j < d, max ((π (s j) : ℤ) - s j) ((s j : ℤ) + 1 + c - n) ≤ -(δ j : ℤ) := by
    intro j hj
    rw [hπW _ (P3 j hj)]
    have a := P5 j hj
    have b := hS j hj
    apply max_le <;> omega
  apply block_of_perm n c g π
  · intro i hi
    by_cases h : i < W
    · rw [hπW i h]; have := P1 i h; omega
    · rw [hπW' i (by omega)]; exact hi
  · intro i hi j hj hij
    by_cases a : i < W <;> by_cases b : j < W
    · rw [hπW i a, hπW j b] at hij; exact P2 i a j b hij
    · rw [hπW i a, hπW' j (by omega)] at hij; have := P1 i a; omega
    · rw [hπW' i (by omega), hπW j b] at hij; have := P1 j b; omega
    · rw [hπW' i (by omega), hπW' j (by omega)] at hij; exact hij
  · intro θ
    rcases le_or_gt θ 0 with hθ | hθ
    · -- θ ≤ 0
      have hA1 := Finset.card_filter_add_card_filter_not (s := range n)
        (fun i => θ ≤ max ((π i : ℤ) - i) ((i : ℤ) + 1 + c - n))
      have hB1 := Finset.card_filter_add_card_filter_not (s := range n) (fun t => θ ≤ (g t : ℤ) - n)
      rw [card_range] at hA1 hB1
      have hBA : ((range n).filter (fun t => ¬ θ ≤ (g t : ℤ) - n)).card ≤
          ((range n).filter (fun i => ¬ θ ≤ max ((π i : ℤ) - i) ((i : ℤ) + 1 + c - n))).card := by
        apply Finset.card_le_card_of_injOn s
        · intro t ht
          rw [Finset.mem_coe, Finset.mem_filter, mem_range, not_le] at ht
          have htd : t < d := (hd t ht.1).1 (by omega)
          rw [Finset.mem_coe, Finset.mem_filter, mem_range, not_le]
          refine ⟨by have := P3 t htd; omega, ?_⟩
          have := hreqdef t htd
          have := hδg t htd
          omega
        · intro t ht t' ht' h
          rw [Finset.mem_coe, Finset.mem_filter, mem_range, not_le] at ht ht'
          have htd : t < d := (hd t ht.1).1 (by omega)
          have htd' : t' < d := (hd t' ht'.1).1 (by omega)
          exact P4 t htd t' htd' h
      omega
    · -- θ ≥ 1
      obtain ⟨t, rfl⟩ : ∃ t : ℕ, θ = (t : ℤ) + 1 := ⟨(θ - 1).toNat, by omega⟩
      obtain ⟨p, hpn, hp⟩ := prefix_count n (n + (t + 1)) g hmono
      have hBcard : ((range n).filter (fun u => ((t : ℤ) + 1) ≤ (g u : ℤ) - n)).card = n - p := by
        have : (range n).filter (fun u => ((t : ℤ) + 1) ≤ (g u : ℤ) - n) =
            (range n).filter (fun u => ¬ (g u < n + (t + 1))) := by
          apply Finset.filter_congr; intro u _; omega
        rw [this]
        have h1 := Finset.card_filter_add_card_filter_not (s := range n) (fun u => g u < n + (t + 1))
        rw [card_filter_lt n p _ hpn hp, card_range] at h1
        omega
      rw [hBcard]
      -- p ≤ n - c + t  (from (ii))
      have hp2 : p ≤ n - c + t := by
        by_contra hcon; push_neg at hcon
        have hk : n - c + t < n := by omega
        have := (hp (n - c + t) hk).2 hcon
        have := hii (n - c + t) hk
        omega
      -- A ⊆ (range W \ image s) ∪ Ico (n-c+t) n, with first part only if t+1 ≤ E
      set A := (range n).filter (fun i => ((t : ℤ) + 1) ≤ max ((π i : ℤ) - i) ((i : ℤ) + 1 + c - n))
        with hA
      set X := ((range W).filter (fun i => ∀ j < d, s j ≠ i)) with hX
      have hXcard : X.card = W - d := by
        have hsub : (range d).image s ⊆ range W := by
          intro v hv; simp only [mem_image, mem_range] at hv; obtain ⟨j, hj, rfl⟩ := hv
          simp [P3 j hj]
        have himg : ((range d).image s).card = d := by
          rw [card_image_of_injOn (fun a ha b hb hab => P4 a (by simpa using ha) b (by simpa using hb) hab)]
          simp
        have : X = range W \ (range d).image s := by
          ext i; simp only [hX, mem_filter, mem_range, mem_sdiff, mem_image, not_exists, not_and]
        rw [this, card_sdiff_of_subset hsub, himg, card_range]
      have hYcard : (Ico (n - c + t) n).card = c - t := by rw [Nat.card_Ico]; omega
      have hAsub : A ⊆ (if t + 1 ≤ E then X else ∅) ∪ Ico (n - c + t) n := by
        intro i hi
        simp only [hA, mem_filter, mem_range] at hi
        obtain ⟨hin, hr⟩ := hi
        by_cases hiW : i < W
        · -- i is not a deficit slot
          have hnd : ∀ j < d, s j ≠ i := by
            intro j hj hji
            have := hreqdef j hj
            rw [hji] at this
            omega
          have hπi := P7 i hiW hnd
          rw [hπW i hiW] at hr
          have hrE : max ((π0 i : ℤ) - i) ((i : ℤ) + 1 + c - n) ≤ E := by
            apply max_le <;> omega
          have htE : t + 1 ≤ E := by omega
          simp only [htE, ite_true, mem_union, hX, mem_filter, mem_range]
          left; exact ⟨hiW, hnd⟩
        · rw [hπW' i (by omega)] at hr
          simp only [mem_union, mem_Ico]
          right
          constructor
          · have : ((t : ℤ) + 1) ≤ (i : ℤ) + 1 + c - n := by
              rcases le_total ((i : ℤ) - i) ((i : ℤ) + 1 + c - n) with h | h
              · rw [max_eq_right h] at hr; exact hr
              · rw [max_eq_left h] at hr; simp at hr; omega
            omega
          · exact hin
      have hAcard := card_le_card hAsub
      have hU := card_union_le ((if t + 1 ≤ E then X else ∅)) (Ico (n - c + t) n)
      by_cases htE : t + 1 ≤ E
      · simp only [htE, ite_true] at hU hAcard
        rw [hXcard, hYcard] at hU
        -- Zlemma
        have hdW : d ≤ W := by
          have := Finset.card_le_card_of_injOn (s := range d) (t := range W) s
            (fun j hj => by simp only [coe_range, Set.mem_Iio] at hj ⊢; exact P3 j hj)
            (fun a ha b hb hab => P4 a (by simpa using ha) b (by simpa using hb) hab)
          simpa using this
        have hpd : d ≤ p := by
          by_contra hcon; push_neg at hcon
          have := (hp p (by omega)).1 (by have := hdef p hcon; omega)
          omega
        have hcn : c ≤ n := by omega
        -- Zb bound in ℕ
        have hZbN : c * (W - d) ≤ c * δ 0 + 2 * (∑ i ∈ range d, δ i) := by
          have h10 := P10 hdpos
          have a : E * (c * (W - d)) ≤ E * (c * δ 0 + 2 * ∑ i ∈ range d, δ i) := by
            have e1 : E * W = E * (W - d) + E * d := by rw [← Nat.mul_add]; congr 1; omega
            have e2 : E * (d + δ 0) = E * d + E * δ 0 := by ring
            have hE' : E * (W - d) ≤ E * δ 0 + ∑ i ∈ range d, δ i := by omega
            have := Nat.mul_le_mul_left c hE'
            have b : c * (∑ i ∈ range d, δ i) ≤ 2 * E * (∑ i ∈ range d, δ i) := Nat.mul_le_mul_right _ hcE
            nlinarith
          exact Nat.le_of_mul_le_mul_left a (by omega)
        -- sums
        have hsumgd : ∑ i ∈ range d, (g i : ℚ) + ∑ i ∈ range d, (δ i : ℚ) = d * n := by
          rw [← Finset.sum_add_distrib]
          rw [Finset.sum_congr rfl (fun i hi => show (g i : ℚ) + δ i = n by
            exact_mod_cast hδg i (by simp at hi; omega))]
          simp
        have hnq' : (0 : ℚ) < n := hnq
        set H : ℚ := ∑ i ∈ range d, (1 : ℚ) / g i + c / (2 * g 0) with hHdef
        have hHt : (((d : ℚ) + c / 2) * n + (∑ i ∈ range d, (δ i : ℚ)) + c * (δ 0 : ℚ) / 2) / n ^ 2 ≤ H := by
          have h1 : ∑ i ∈ range d, (2 / (n : ℚ) - g i / n ^ 2) ≤ ∑ i ∈ range d, (1 : ℚ) / g i :=
            Finset.sum_le_sum (fun i hi => tangent _ _ (hgpos i (by simp at hi; omega)) hnq')
          have h2 : (c : ℚ) / 2 * (2 / n - g 0 / n ^ 2) ≤ c / (2 * g 0) := by
            have := tangent (g 0 : ℚ) n (hgpos 0 hnpos) hnq'
            have e : (c : ℚ) / (2 * g 0) = c / 2 * (1 / g 0) := by field_simp
            rw [e]; exact mul_le_mul_of_nonneg_left this (by positivity)
          have h3 : ∑ i ∈ range d, (2 / (n : ℚ) - g i / n ^ 2) = 2 * d / n - (∑ i ∈ range d, (g i : ℚ)) / n ^ 2 := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul, ← Finset.sum_div]; ring
          have h0 : (g 0 : ℚ) + δ 0 = n := by exact_mod_cast hδg 0 (by omega)
          have e : (((d : ℚ) + c / 2) * n + (∑ i ∈ range d, (δ i : ℚ)) + c * (δ 0 : ℚ) / 2) / n ^ 2 =
              (2 * d / n - (∑ i ∈ range d, (g i : ℚ)) / n ^ 2) + c / 2 * (2 / n - g 0 / n ^ 2) := by
            have : (∑ i ∈ range d, (g i : ℚ)) = d * n - ∑ i ∈ range d, (δ i : ℚ) := by linarith
            rw [this, show (g 0 : ℚ) = n - δ 0 by linarith]
            field_simp; ring
          rw [e, hHdef]; linarith
        have hiZ : H + ((p : ℚ) - d) / (n + t) + ((n : ℚ) - p) / (n + c) ≤ 1 := by
          have hsplit : ∑ k ∈ range n, (1 : ℚ) / g k = ∑ k ∈ range d, (1 : ℚ) / g k +
              ∑ k ∈ Ico d p, (1 : ℚ) / g k + ∑ k ∈ Ico p n, (1 : ℚ) / g k := by
            rw [Finset.sum_range_add_sum_Ico _ hpd]; exact (Finset.sum_range_add_sum_Ico _ hpn).symm
          have hmid : ((p : ℚ) - d) / (n + t) ≤ ∑ k ∈ Ico d p, (1 : ℚ) / g k := by
            calc ((p : ℚ) - d) / (n + t) = ∑ k ∈ Ico d p, (1 : ℚ) / (n + t) := by
                  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; push_cast [Nat.cast_sub hpd]; ring
              _ ≤ ∑ k ∈ Ico d p, (1 : ℚ) / g k := by
                  apply Finset.sum_le_sum; intro k hk; simp at hk
                  apply one_div_le_one_div_of_le (hgpos k (by omega))
                  have := (hp k (by omega)).2 hk.2
                  have : g k ≤ n + t := by omega
                  exact_mod_cast this
          have htop : ((n : ℚ) - p) / (n + c) ≤ ∑ k ∈ Ico p n, (1 : ℚ) / g k := by
            calc ((n : ℚ) - p) / (n + c) = ∑ k ∈ Ico p n, (1 : ℚ) / (n + c) := by
                  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; push_cast [Nat.cast_sub hpn]; ring
              _ ≤ ∑ k ∈ Ico p n, (1 : ℚ) / g k := by
                  apply Finset.sum_le_sum; intro k hk; simp at hk
                  apply one_div_le_one_div_of_le (hgpos k hk.2)
                  have := hC k hk.2
                  have : g k ≤ n + c := by omega
                  exact_mod_cast this
          rw [hHdef]
          linarith
        have hQ1 : 2 * (∑ i ∈ range d, (δ i : ℚ)) ≤ c * (n - c - 2 * d - δ 0) := by
          have hup := hHJ d hdn
          have hle := le_trans hHt hup
          rw [div_le_div_iff₀ (by positivity) (by positivity)] at hle
          have hΔ0 : (0 : ℚ) ≤ ∑ i ∈ range d, (δ i : ℚ) := by positivity
          have hcq : (0 : ℚ) ≤ c := by positivity
          have hδ0 : (0 : ℚ) ≤ δ 0 := by positivity
          by_contra hcon; push_neg at hcon
          nlinarith [mul_pos hnq' hnq', mul_nonneg hcq hΔ0, mul_nonneg (mul_nonneg hcq hcq) hδ0]
        have hZ := Zlemma n c t d p ((W - d : ℕ) : ℚ) (∑ i ∈ range d, (δ i : ℚ)) (δ 0) H hnq'
          (by exact_mod_cast hc1) (by positivity) (by have : 2 * t + 1 ≤ c := by omega
                                                      exact_mod_cast this)
          (by positivity) (by positivity) (by positivity) (by exact_mod_cast hpd)
          hHt hiZ hQ1
          (by have := hZbN; push_cast at this ⊢; exact_mod_cast this)
        have hfin : p + (W - d) ≤ n - c + t := by
          have : ((p + (W - d) : ℕ) : ℚ) ≤ ((n - c + t : ℕ) : ℚ) := by
            push_cast [Nat.cast_sub hcn, Nat.cast_sub hdW] at hZ ⊢; linarith
          exact_mod_cast this
        omega
      · simp only [htE, ite_false, card_empty, zero_add] at hU hAcard
        rw [hYcard] at hU
        omega




/-! ### chain bound, Lemma C, and the main induction -/

theorem sum_Ico_lin (c a : ℕ) : ∀ d : ℕ,
    ∑ k ∈ Ico a (a + d), (c + 2 * k) + d = d * (c + 2 * a + d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show a + (d + 1) = (a + d) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    have : (d + 1) * (c + 2 * a + (d + 1)) = d * (c + 2 * a + d) + (c + 2 * a + 2 * d + 1) := by ring
    omega

theorem chain (n c : ℕ) (g : ℕ → ℕ) (hmono : ∀ i j, i ≤ j → j < n → g i ≤ g j)
    (hirr : ∀ s, 1 ≤ s → s < n → ∃ k, s ≤ k ∧ k < n ∧ g k ≤ c + s + k) :
    ∀ a, 1 ≤ a → a ≤ n → ∑ k ∈ Ico a n, g k ≤ ∑ k ∈ Ico a n, (c + 2 * k) := by
  have main : ∀ m, ∀ a, n - a = m → 1 ≤ a → a ≤ n →
      ∑ k ∈ Ico a n, g k ≤ ∑ k ∈ Ico a n, (c + 2 * k) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
    intro a hm ha1 han
    rcases eq_or_lt_of_le han with h | h
    · subst h; simp
    obtain ⟨k, hk1, hk2, hk3⟩ := hirr a ha1 h
    have hsplit1 := Finset.sum_Ico_consecutive (fun k => g k) (show a ≤ k + 1 by omega) (show k + 1 ≤ n by omega)
    have hsplit2 := Finset.sum_Ico_consecutive (fun k => c + 2 * k) (show a ≤ k + 1 by omega) (show k + 1 ≤ n by omega)
    rw [← hsplit1, ← hsplit2]
    have h1 : ∑ i ∈ Ico a (k + 1), g i ≤ ∑ i ∈ Ico a (k + 1), (c + 2 * i) := by
      have hl := sum_Ico_lin c a (k + 1 - a)
      rw [show a + (k + 1 - a) = k + 1 by omega] at hl
      calc ∑ i ∈ Ico a (k + 1), g i ≤ ∑ i ∈ Ico a (k + 1), (c + a + k) := by
            apply Finset.sum_le_sum; intro i hi; simp at hi
            exact le_trans (hmono i k (by omega) hk2) hk3
        _ = (k + 1 - a) * (c + a + k) := by
            rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
        _ ≤ ∑ i ∈ Ico a (k + 1), (c + 2 * i) := by
            have : (k + 1 - a) * (c + 2 * a + (k + 1 - a)) = (k + 1 - a) * (c + a + k) + (k + 1 - a) := by
              rw [show c + 2 * a + (k + 1 - a) = (c + a + k) + 1 by omega]; ring
            omega
    have h2 := IH (n - (k + 1)) (by omega) (k + 1) rfl (by omega) (by omega)
    omega
  intro a ha1 han
  exact main (n - a) a rfl ha1 han

/-- Lemma C via tangent line. -/
theorem lemmaC (n c W : ℕ) (g : ℕ → ℕ) (hW : 1 ≤ W) (hWn : W ≤ n) (hpos : ∀ k < n, 0 < g k)
    (hsum : ∑ k ∈ Ico W n, g k ≤ (n - W) * (c + W + n - 1)) :
    ((n - W : ℕ) : ℚ) / ((c : ℚ) + W + n - 1) ≤ ∑ k ∈ Ico W n, (1 : ℚ) / g k := by
  set T : ℚ := (c : ℚ) + W + n - 1 with hT
  have hTpos : 0 < T := by
    rw [hT]; have : (1 : ℚ) ≤ W := by exact_mod_cast hW
    have : (0 : ℚ) ≤ c := by positivity
    have : (W : ℚ) ≤ n := by exact_mod_cast hWn
    linarith
  have h1 : ∑ k ∈ Ico W n, (2 / T - (g k : ℚ) / T ^ 2) ≤ ∑ k ∈ Ico W n, (1 : ℚ) / g k := by
    apply Finset.sum_le_sum; intro k hk; simp at hk
    exact tangent _ _ (by exact_mod_cast hpos k hk.2) hTpos
  have h2 : ∑ k ∈ Ico W n, (2 / T - (g k : ℚ) / T ^ 2) =
      2 * ((n - W : ℕ) : ℚ) / T - ((∑ k ∈ Ico W n, g k : ℕ) : ℚ) / T ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, ← Finset.sum_div]
    push_cast; ring
  have h3 : ((∑ k ∈ Ico W n, g k : ℕ) : ℚ) ≤ ((n - W : ℕ) : ℚ) * T := by
    have : (((n - W) * (c + W + n - 1) : ℕ) : ℚ) = ((n - W : ℕ) : ℚ) * T := by
      rw [hT]; push_cast [Nat.cast_sub (show 1 ≤ c + W + n by omega)]; ring
    rw [← this]; exact_mod_cast hsum
  have h4 : ((n - W : ℕ) : ℚ) / T ≤ 2 * ((n - W : ℕ) : ℚ) / T - ((∑ k ∈ Ico W n, g k : ℕ) : ℚ) / T ^ 2 := by
    have : ((∑ k ∈ Ico W n, g k : ℕ) : ℚ) / T ^ 2 ≤ ((n - W : ℕ) : ℚ) * T / T ^ 2 :=
      div_le_div_of_nonneg_right h3 (by positivity)
    have e : ((n - W : ℕ) : ℚ) * T / T ^ 2 = ((n - W : ℕ) : ℚ) / T := by field_simp
    have e2 : 2 * ((n - W : ℕ) : ℚ) / T = ((n - W : ℕ) : ℚ) / T + ((n - W : ℕ) : ℚ) / T := by ring
    linarith
  linarith


/-! ### the generalized theorem T(b) -/

theorem tb : ∀ (n c : ℕ) (g : ℕ → ℕ), (∀ i j, i ≤ j → j < n → g i ≤ g j) →
    (∀ k < n, c + k + 1 ≤ g k) →
    (0 < n → ∑ k ∈ range n, (1 : ℚ) / g k + c / (2 * g 0) ≤ 1) →
    ∃ x y : ℕ → ℕ, Good n c g x y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro c g hmono hii hi
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact ⟨id, id, by simp, by simp, by simp, by simp⟩
  have hi' := hi hnpos
  have hgpos : ∀ k < n, (0 : ℚ) < g k := fun k hk => by
    have := hii k hk; exact_mod_cast (show 0 < g k by omega)
  by_cases hsplit : ∃ s, 1 ≤ s ∧ s < n ∧ ∀ k, s ≤ k → k < n → c + s + k + 1 ≤ g k
  · -- split
    obtain ⟨s, hs1, hsn, hsk⟩ := hsplit
    -- S part
    obtain ⟨x1, y1, hG1⟩ := IH s hsn c g (fun i j hij hj => hmono i j hij (by omega))
      (fun k hk => hii k (by omega))
      (by
        intro _
        have : ∑ k ∈ range s, (1 : ℚ) / g k ≤ ∑ k ∈ range n, (1 : ℚ) / g k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
          intro k hk _; simp at hk; exact le_of_lt (by have := hgpos k hk; positivity)
        linarith)
    -- L part
    obtain ⟨x2, y2, hG2⟩ := IH (n - s) (by omega) (c + 2 * s) (fun k => g (s + k))
      (fun i j hij hj => hmono _ _ (by omega) (by omega))
      (fun k hk => by have := hsk (s + k) (by omega) (by omega); omega)
      (by
        intro _
        have hsum : ∑ k ∈ range n, (1 : ℚ) / g k =
            ∑ k ∈ range s, (1 : ℚ) / g k + ∑ k ∈ range (n - s), (1 : ℚ) / g (s + k) := by
          rw [← Finset.sum_range_add, show s + (n - s) = n by omega]
        have hS : (s : ℚ) / g s ≤ ∑ k ∈ range s, (1 : ℚ) / g k := by
          calc (s : ℚ) / g s = ∑ k ∈ range s, (1 : ℚ) / g s := by simp; ring
            _ ≤ ∑ k ∈ range s, (1 : ℚ) / g k := by
                apply Finset.sum_le_sum; intro k hk; simp at hk
                exact one_div_le_one_div_of_le (hgpos k (by omega)) (by exact_mod_cast hmono k s (by omega) hsn)
        have hc : (c : ℚ) / (2 * g s) ≤ c / (2 * g 0) := by
          apply div_le_div_of_nonneg_left (by positivity) (by have := hgpos 0 hnpos; positivity)
          have : (g 0 : ℚ) ≤ g s := by exact_mod_cast hmono 0 s (by omega) hsn
          linarith
        have e : ((c + 2 * s : ℕ) : ℚ) / (2 * g (s + 0)) = c / (2 * g s) + s / g s := by
          simp; field_simp
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at e ⊢
        rw [e]
        linarith)
    obtain ⟨g1a, g1b, g1c, g1d⟩ := hG1
    obtain ⟨g2a, g2b, g2c, g2d⟩ := hG2
    refine ⟨fun k => if k < s then x1 k else x2 (k - s), fun k => if k < s then y1 k else y2 (k - s),
      ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases h : k < s
      · simp only [h, ite_true]; have := g1a k h; omega
      · simp only [h, ite_false]
        have := g2a (k - s) (by omega)
        simp only [show s + (k - s) = k by omega] at this
        omega
    · intro k hk l hl
      by_cases h : k < s <;> by_cases h' : l < s <;> simp only [h, h', ite_true, ite_false]
      · exact g1b k h l h'
      · have := g1a k h; have := g2a (l - s) (by omega); omega
      · have := g2a (k - s) (by omega); have := g1a l h'; omega
      · exact g2b (k - s) (by omega) (l - s) (by omega)
    · intro k hk l hl hkl
      by_cases h : k < s <;> by_cases h' : l < s <;> simp only [h, h', ite_true, ite_false] at hkl
      · exact g1c k h l h' hkl
      · have := g1a k h; have := g2a (l - s) (by omega); omega
      · have := g2a (k - s) (by omega); have := g1a l h'; omega
      · have := g2c (k - s) (by omega) (l - s) (by omega) hkl; omega
    · intro k hk l hl hkl
      by_cases h : k < s <;> by_cases h' : l < s <;> simp only [h, h', ite_true, ite_false] at hkl
      · exact g1d k h l h' hkl
      · have := g1a k h; have := g2a (l - s) (by omega); omega
      · have := g2a (k - s) (by omega); have := g1a l h'; omega
      · have := g2d (k - s) (by omega) (l - s) (by omega) hkl; omega
  · -- irreducible
    push_neg at hsplit
    have hirr : ∀ s, 1 ≤ s → s < n → ∃ k, s ≤ k ∧ k < n ∧ g k ≤ c + s + k := by
      intro s hs1 hsn
      obtain ⟨k, hk1, hk2, hk3⟩ := hsplit s hs1 hsn
      exact ⟨k, hk1, hk2, by omega⟩
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n = 1
      have hn1 : n = 1 := by omega
      subst hn1
      refine ⟨fun _ => c + 1, fun _ => c + 2, ?_, ?_, ?_, ?_⟩
      · intro k hk; have := hii k hk; dsimp only; omega
      · intro k _ l _; dsimp only; omega
      · intro k hk l hl _; omega
      · intro k hk l hl _; omega
    -- tight index w (largest)
    classical
    have hex : ∃ k, 1 ≤ k ∧ k < n ∧ g k = c + k + 1 := by
      obtain ⟨k, hk1, hk2, hk3⟩ := hirr 1 (le_refl _) (by omega)
      exact ⟨k, hk1, hk2, by have := hii k hk2; omega⟩
    let P : ℕ → Prop := fun k => 1 ≤ k ∧ k < n ∧ g k = c + k + 1
    have hbdd : ∀ k, P k → k ≤ n := fun k hk => le_of_lt hk.2.1
    let w := Nat.findGreatest P n
    have hwP : P w := Nat.findGreatest_spec (P := P) (m := hex.choose) (le_of_lt hex.choose_spec.2.1) hex.choose_spec
    obtain ⟨hw1, hwn, hwg⟩ := hwP
    have hwmax : ∀ k, w < k → k < n → g k ≠ c + k + 1 := by
      intro k hwk hkn hgk
      have := Nat.le_findGreatest (P := P) (le_of_lt hkn) ⟨by omega, hkn, hgk⟩
      omega
    set W := w + 1 with hWdef
    set D := n - W with hDdef
    -- chain bound and Lemma C
    have hch := chain n c g hmono hirr W (by omega) (by omega)
    have hlin := sum_Ico_lin c W (n - W)
    rw [show W + (n - W) = n by omega] at hlin
    have hsumbound : ∑ k ∈ Ico W n, g k ≤ (n - W) * (c + W + n - 1) := by
      have : (n - W) * (c + 2 * W + (n - W)) = (n - W) * (c + W + n - 1) + (n - W) := by
        rw [show c + 2 * W + (n - W) = (c + W + n - 1) + 1 by omega]; ring
      omega
    have hLC := lemmaC n c W g (by omega) (by omega) (fun k hk => by have := hii k hk; omega) hsumbound
    -- core inequality input
    have hsum_split : ∑ k ∈ range n, (1 : ℚ) / g k = ∑ k ∈ range W, (1 : ℚ) / g k + ∑ k ∈ Ico W n, (1 : ℚ) / g k :=
      (Finset.sum_range_add_sum_Ico _ (by omega)).symm
    have hS : ∑ k ∈ range W, 1 / (g k : ℚ) + c / (2 * (g 0 : ℚ)) + (D : ℚ) / ((c : ℚ) + 2 * W + D - 1) ≤ 1 := by
      have e : ((c : ℚ) + 2 * W + D - 1) = (c : ℚ) + W + n - 1 := by
        rw [hDdef]; push_cast [Nat.cast_sub (show W ≤ n by omega)]; ring
      rw [e]; rw [hDdef]
      linarith
    have hgw : g w = c + W := by omega
    obtain ⟨hDc, hcore⟩ := corelemma c W D (fun k => (g k : ℚ)) (by omega) ⟨g 0, rfl⟩
      (by have := hii 0 hnpos; exact_mod_cast (show c + 1 ≤ g 0 by omega))
      (fun k hk => by exact_mod_cast hmono 0 k (by omega) (by omega))
      (fun k hk => by have := hmono k w (by omega) hwn; exact_mod_cast (show g k ≤ c + W by omega))
      hS
    have hDc' : D ≤ c := by rcases hDc with h | h <;> omega
    -- core block
    obtain ⟨sl, sg, hB1, hB2, hB3⟩ := cblock W (c - D) (fun k => g k - D)
      (fun i j hij hj => by have := hmono i j hij (by omega); omega)
      (fun k hk => by have := hii k (by omega); omega)
      (fun k hk => by have := hmono k w (by omega) hwn; omega)
      (by
        intro _
        have hgD : ∀ k < W, D ≤ g k := fun k hk => by have := hii k (by omega); omega
        have e1 : ∑ k ∈ range W, (1 : ℚ) / ((g k - D : ℕ) : ℚ) = ∑ k ∈ range W, 1 / ((g k : ℚ) - D) := by
          apply Finset.sum_congr rfl; intro k hk; simp at hk
          rw [Nat.cast_sub (hgD k hk)]
        have e2 : ((c - D : ℕ) : ℚ) / (2 * ((g 0 - D : ℕ) : ℚ)) = ((c : ℚ) - D) / (2 * ((g 0 : ℚ) - D)) := by
          rw [Nat.cast_sub hDc', Nat.cast_sub (hgD 0 (by omega))]
        rw [e1, e2]; exact hcore)
    refine ⟨fun k => if k < W then c + sl k + 1 else c + k + 1,
      fun k => if k < W then c + n + sg k + 1 else c + n + k + 1, ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases h : k < W
      · simp only [h, ite_true]
        obtain ⟨a1, a2, a3, a4⟩ := hB1 k h
        refine ⟨by omega, by omega, by omega, by omega, by omega⟩
      · simp only [h, ite_false]
        have := hii k hk
        have : g w ≤ g k := hmono w k (by omega) hk
        refine ⟨by omega, by omega, by omega, by omega, by omega⟩
    · intro k hk l hl
      by_cases h : k < W <;> by_cases h' : l < W <;> simp only [h, h', ite_true, ite_false]
      · have := hB1 k h; omega
      · have := hB1 k h; omega
      · have := hB1 l h'; omega
      · omega
    · intro k hk l hl hkl
      by_cases h : k < W <;> by_cases h' : l < W <;> simp only [h, h', ite_true, ite_false] at hkl
      · exact hB2 k h l h' (by omega)
      · have := hB1 k h; omega
      · have := hB1 l h'; omega
      · omega
    · intro k hk l hl hkl
      by_cases h : k < W <;> by_cases h' : l < W <;> simp only [h, h', ite_true, ite_false] at hkl
      · exact hB3 k h l h' (by omega)
      · have := hB1 k h; omega
      · have := hB1 l h'; omega
      · omega

/-! ### main theorem -/

theorem schedulable_of_density_le_one (n : ℕ) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (hdens : ∑ i, (1 : ℚ) / d i ≤ 1) : ∃ s : Fin (2 * n) → Fin n, IsSchedule n d s := by
  set σ := Tuple.sort d with hσ
  have hmon := Tuple.monotone_sort d
  set g : ℕ → ℕ := fun k => if h : k < n then d (σ ⟨k, h⟩) else 0 with hg
  have hgmono : ∀ i j, i ≤ j → j < n → g i ≤ g j := by
    intro i j hij hj
    simp only [hg, show i < n by omega, hj, dif_pos]
    exact hmon (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  have hsum : ∑ k ∈ range n, (1 : ℚ) / g k = ∑ i, (1 : ℚ) / d i := by
    rw [Finset.sum_range (fun k => (1 : ℚ) / g k)]
    have : ∀ i : Fin n, (1 : ℚ) / g i = (1 : ℚ) / d (σ i) := by
      intro i; simp [hg, i.2]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    exact Equiv.sum_comp σ (fun i => (1 : ℚ) / d i)
  -- (ii) at offset 0
  have hii : ∀ k < n, 0 + k + 1 ≤ g k := by
    intro k hk
    by_contra hcon; push_neg at hcon
    -- tasks 0..k all have g ≤ k, so Σ 1/g ≥ (k+1)/k > 1
    have hgpos : ∀ j < n, 0 < g j := fun j hj => by simp [hg, hj, hd]
    have hle : ∀ j ≤ k, (g j : ℚ) ≤ k := by
      intro j hj
      have := hgmono j k hj hk
      exact_mod_cast (show g j ≤ k by omega)
    have hk0 : 1 ≤ k := by have := hgpos k hk; omega
    have h1 : ((k + 1 : ℕ) : ℚ) / k ≤ ∑ j ∈ range (k + 1), (1 : ℚ) / g j := by
      calc ((k + 1 : ℕ) : ℚ) / k = ∑ j ∈ range (k + 1), (1 : ℚ) / k := by simp; ring
        _ ≤ ∑ j ∈ range (k + 1), (1 : ℚ) / g j := by
          apply Finset.sum_le_sum; intro j hj; simp at hj
          exact one_div_le_one_div_of_le (by exact_mod_cast hgpos j (by omega)) (hle j (by omega))
    have h2 : ∑ j ∈ range (k + 1), (1 : ℚ) / g j ≤ ∑ j ∈ range n, (1 : ℚ) / g j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
      intro j hj _; simp at hj; exact le_of_lt (by have := hgpos j hj; positivity)
    have h3 : (1 : ℚ) < ((k + 1 : ℕ) : ℚ) / k := by
      rw [lt_div_iff₀ (by exact_mod_cast hk0)]; push_cast; linarith
    linarith
  obtain ⟨x, y, hG⟩ := tb n 0 g hgmono hii (by
    intro _
    rw [show ((0 : ℕ) : ℚ) / (2 * (g 0 : ℚ)) = 0 by simp, add_zero, hsum]; exact hdens)
  exact schedule_of_good n d σ x y hG

/-- **Main theorem.** The lower density threshold of 2-Visits is exactly 1:
every instance with `Σ 1/dᵢ ≤ 1` admits a schedule, and for every `ε > 0` there is an
unschedulable instance with density in `(1, 1+ε)`. -/
theorem two_visits_density_threshold :
    (∀ (n : ℕ) (d : Fin n → ℕ), (∀ i, 0 < d i) → ∑ i, (1 : ℚ) / d i ≤ 1 →
      ∃ s : Fin (2 * n) → Fin n, IsSchedule n d s) ∧
    (∀ ε : ℚ, 0 < ε → ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, 0 < d i) ∧
      1 < ∑ i, (1 : ℚ) / d i ∧ ∑ i, (1 : ℚ) / d i < 1 + ε ∧
      ¬ ∃ s : Fin (2 * n) → Fin n, IsSchedule n d s) := by
  refine ⟨schedulable_of_density_le_one, ?_⟩
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hk1 : 1 ≤ k := by
    by_contra h; push_neg at h; interval_cases k; simp at hk; linarith [one_div_pos.2 hε]
  have hkq : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsumk : (∑ _i : Fin (k + 1), (1 : ℚ) / ((k : ℕ) : ℚ)) = ((k : ℚ) + 1) / k := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  refine ⟨k + 1, fun _ => k, fun _ => by show 0 < k; omega, ?_, ?_, not_schedulable_const k⟩
  · show 1 < ∑ _i : Fin (k + 1), (1 : ℚ) / ((k : ℕ) : ℚ)
    rw [hsumk, lt_div_iff₀ hkq]; linarith
  · show ∑ _i : Fin (k + 1), (1 : ℚ) / ((k : ℕ) : ℚ) < 1 + ε
    rw [hsumk, div_lt_iff₀ hkq]
    have : 1 < ε * k := by
      rw [div_lt_iff₀ hε] at hk; linarith
    nlinarith


end TwoVisits
