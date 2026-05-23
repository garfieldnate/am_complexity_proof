import CountUnionFamilyPowersetsProof.AM.Propositions
import CountUnionFamilyPowersetsProof.Basic

set_option linter.style.openClassical false
open Classical

/-!
## Analogical Modeling — #P-Hardness of Exact AM Scoring

This file proves that computing the exact analogical modeling score is #P-hard
by exhibiting a polynomial-time reduction from #⋃℘ (counting the size of a union
of powerset families).

### Background: the AM algorithm

If you have implemented AM, here is what each object corresponds to in your code:

- `matchSet τ D` (M): the set of distinct patterns `τ ∩ d.features` as d ranges over D.
  In the algorithm, M is the set of "match patterns" your test query τ produces against D.

- `θ τ D x`: the set of exemplars in D whose match pattern with τ is exactly x.
  In the algorithm, `θ` is the partition of D by which element of M each exemplar maps to.

- `σ D m`: the "support" of pattern m — all exemplars whose features contain m.
  This is the set of exemplars "activated" by pattern m in the AM weighting scheme.

- `δ D m`: the total pairwise disagreement within σ(m).  If σ(m) contains exemplars
  of different outcome classes, δ > 0; if they all agree, δ = 0.

- `IsHomogeneous τ D m`: m has non-empty support and δ stays constant across all
  super-patterns with non-empty support.  These are exactly the patterns the
  algorithm sums over in the analogical set A.

- `c τ D x` (c_x): the count of homogeneous sub-patterns of x.  Theorem 1
  (representation_theorem) shows that the total score equals Σ_{x ∈ M} c_x · score(θ(x)),
  so computing c_x is the inner bottleneck of exact AM.

### The reduction

Given a #⋃℘ instance — a family of sets {S₁, …, Sₖ} ⊆ Finset (Fin n) — we
construct a small AM database D over n+1 features with two outcome classes (0 and 1):

  Feature space: Fin (n+1).  Features 0..n-1 are the "real" features.
                              Feature n is a "fresh" marker feature.

  Test query τ = Finset.univ = {0, 1, …, n}

  d₀: features = {0, …, n-1},          outcome = 0   (one class-0 exemplar)
  dᵢ S: features = embedFin(S) ∪ {n},  outcome = 1   (one class-1 exemplar per Sᵢ)

where `embedFin S` embeds a subset S ⊆ Fin n into Fin (n+1) by casting each
element with `Fin.castSucc` (the identity on 0..n-1, not touching feature n).

When you run AM on test query τ against D, the following happens:

1. Match set M = {x_A} ∪ {embedFin S ∪ {n} | S ∈ family}
     where x_A = {0, …, n-1} is the match pattern produced by d₀.

2. θ(x_A) = {d₀}: the only exemplar whose match pattern is x_A.
   θ(embedFin S ∪ {n}) = {dᵢ S}: each class-1 exemplar maps to its own fiber.

3. outcomeCount(θ(x_A), 0) = 1.
   outcomeCount(θ(embedFin S ∪ {n}), 0) = 0 (all class-1).

4. The total score for outcome 0 is:
     Σ_{x ∈ M} c_x · outcomeCount(θ(x), 0) = c_{x_A} · 1 = c_{x_A}.

5. c_{x_A} = |{p ⊆ x_A : p is homogeneous}|
           = |{p ⊆ {0..n-1} : ∀ Sᵢ, p ⊄ embedFin Sᵢ}|   (Section G)
           = 2^n − |⋃ᵢ ℘(embedFin Sᵢ)|                   (Section H).

Therefore: `totalScore τ D 0 = 2^n − |⋃ᵢ ℘(Sᵢ)|`.

Given an oracle for `totalScore`, we recover |⋃ᵢ ℘(Sᵢ)| by subtraction.  Since
#⋃℘ is #P-hard (proved in Basic.lean via reduction from #VERTEX-COVER), exact AM
scoring is also #P-hard.
-/

/-! ### Database Construction

The feature type is `Fin (n+1)`, giving n+1 slots indexed 0..n.
`embedFin` injects a subset of Fin n (features 0..n-1) into Fin (n+1)
via `Fin.castSucc`, which does not touch slot n.
`freshFeature n` is slot n — the marker that distinguishes class-1 exemplars.
-/

/-- Embed a subset of the first n features into the (n+1)-feature space by
    lifting each element with `Fin.castSucc`.  The image misses `Fin.last n`
    (i.e., the fresh feature) entirely. -/
def embedFin {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.image Fin.castSucc

/-- The "fresh" feature that marks class-1 exemplars; absent from all class-0
    exemplars and from x_A. -/
def freshFeature (n : ℕ) : Fin (n + 1) := Fin.last n

/-- The test query: we run AM against *all* features simultaneously.
    With τ = univ, the match pattern τ ∩ d.features = d.features directly. -/
def testExemplar (n : ℕ) : Finset (Fin (n + 1)) := Finset.univ

/-- The single class-0 exemplar.  Its features are {0, …, n-1} — all real features,
    no fresh feature.  It is the sole source of class-0 vote in the database. -/
def d₀ (n : ℕ) : Exemplar (Fin (n + 1)) (Fin 2) where
  features := embedFin (Finset.univ : Finset (Fin n))
  outcome  := 0

/-- One class-1 exemplar per set S in the family.  Its features are embedFin(S) ∪ {n},
    so it carries the fresh feature n as a tag.  Any pattern p that contains n must
    therefore be "compatible" with a class-1 exemplar. -/
def dᵢ (n : ℕ) (S : Finset (Fin n)) : Exemplar (Fin (n + 1)) (Fin 2) where
  features := embedFin S ∪ {freshFeature n}
  outcome  := 1

/-- The encoded database: d₀ together with one dᵢ S per member of the family. -/
noncomputable def encodeDatabase (n : ℕ) (family : Finset (Finset (Fin n))) :
    Database (Fin (n + 1)) (Fin 2) :=
  {d₀ n} ∪ family.image (dᵢ n)

/-- x_A is the match pattern τ ∩ d₀.features = {0, …, n-1}.
    This is also the "class-0 region" of the feature lattice — the set of real
    features that d₀ possesses.  The c_x coefficient at x_A drives the entire
    class-0 score. -/
def x_A (n : ℕ) : Finset (Fin (n + 1)) := embedFin (Finset.univ : Finset (Fin n))

/-! ### Section A: Basic Membership

    Bookkeeping: who lives in encodeDatabase, and how to recognize them. -/

lemma d₀_mem (n : ℕ) (family : Finset (Finset (Fin n))) :
    d₀ n ∈ encodeDatabase n family := by
  simp [encodeDatabase]

lemma dᵢ_mem {n : ℕ} (family : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ family) : dᵢ n S ∈ encodeDatabase n family := by
  simp only [encodeDatabase, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨S, hS, rfl⟩

/-- Every exemplar in the database is either d₀ or one of the dᵢ S. -/
lemma encodeDatabase_mem_iff {n : ℕ} (family : Finset (Finset (Fin n)))
    (e : Exemplar (Fin (n + 1)) (Fin 2)) :
    e ∈ encodeDatabase n family ↔ e = d₀ n ∨ ∃ S ∈ family, e = dᵢ n S := by
  simp [encodeDatabase, Finset.mem_image, eq_comm]

lemma d₀_outcome_ne_dᵢ (n : ℕ) (S : Finset (Fin n)) :
    (d₀ n).outcome ≠ (dᵢ n S).outcome := by
  simp [d₀, dᵢ]

/-! ### Section B: The Fresh Feature and x_A

    The fresh feature n is the key separator between class-0 and class-1 exemplars.
    Since `Fin.castSucc` never produces `Fin.last`, embedFin never contains the fresh
    feature — so x_A and d₀.features are both "below" n.

    Informally:
    - "no fresh feature in p" ⟺ p is purely about the real features ⟺ p ⊆ x_A.
    - "fresh feature in p" ⟺ p asks about feature n ⟺ only class-1 exemplars can
      satisfy p (since d₀ lacks the fresh feature). -/

lemma d₀_not_fresh (n : ℕ) : freshFeature n ∉ (d₀ n).features := by
  simp only [d₀, embedFin, Finset.mem_image]
  rintro ⟨y, _, hy⟩; exact absurd hy (Fin.castSucc_ne_last y)

lemma dᵢ_has_fresh (n : ℕ) (S : Finset (Fin n)) : freshFeature n ∈ (dᵢ n S).features :=
  Finset.mem_union_right _ (Finset.mem_singleton_self _)

lemma fresh_not_in_xA (n : ℕ) : freshFeature n ∉ x_A n := by
  simp only [x_A, embedFin, Finset.mem_image]
  rintro ⟨y, _, hy⟩; exact absurd hy (Fin.castSucc_ne_last y)

/-- Every element of Fin(n+1) that is not the fresh feature lies in x_A.
    So x_A is precisely the complement of {freshFeature n} in the real-feature lattice. -/
lemma mem_xA_of_ne_fresh {n : ℕ} {x : Fin (n + 1)} (hx : x ≠ freshFeature n) :
    x ∈ x_A n := by
  simp only [x_A, embedFin, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨x.castPred hx, x.castSucc_castPred hx⟩

/-- A subset of Fin(n+1) that doesn't contain the fresh feature is contained in x_A.
    This is how we lift "p doesn't involve n" to "p ⊆ x_A". -/
lemma sub_xA_of_no_fresh {n : ℕ} {q : Finset (Fin (n + 1))} (hn : freshFeature n ∉ q) :
    q ⊆ x_A n :=
  fun x hx => mem_xA_of_ne_fresh (fun h => hn (h ▸ hx))

/-- x_A has exactly n elements (one per real feature). -/
lemma x_A_card (n : ℕ) : (x_A n).card = n := by
  unfold x_A embedFin
  rw [Finset.card_image_of_injective _ (Fin.castSucc_injective n), Finset.card_fin]

/-- x_A has 2^n subsets, matching the #⋃℘ universe size. -/
lemma x_A_powerset_card (n : ℕ) : (x_A n).powerset.card = 2 ^ n := by
  rw [Finset.card_powerset, x_A_card]

/-! ### Section C: Match Patterns for τ = univ

    When the test query is τ = univ, the match pattern for each exemplar d is
    τ ∩ d.features = d.features.  So:
    - d₀ produces match pattern x_A = {0, …, n-1}.
    - dᵢ S produces match pattern embedFin S ∪ {n}.
    These two types of patterns are always distinct (one contains n, the other doesn't). -/

lemma testExemplar_inter_d₀ (n : ℕ) :
    testExemplar n ∩ (d₀ n).features = x_A n := by
  simp [testExemplar, d₀, x_A]

lemma testExemplar_inter_dᵢ (n : ℕ) (S : Finset (Fin n)) :
    testExemplar n ∩ (dᵢ n S).features = embedFin S ∪ {freshFeature n} := by
  simp [testExemplar, dᵢ]

/-- x_A ≠ embedFin S ∪ {n} because x_A doesn't contain the fresh feature. -/
lemma xA_ne_embedFin_union_fresh (n : ℕ) (S : Finset (Fin n)) :
    x_A n ≠ embedFin S ∪ {freshFeature n} := fun h =>
  fresh_not_in_xA n (h ▸ Finset.mem_union_right _ (Finset.mem_singleton_self _))

/-! ### Section D: The θ-Fiber at x_A

    In the AM algorithm, θ(x) is the set of exemplars in D that produce match pattern x.
    At x_A, only d₀ falls in this fiber: no class-1 exemplar produces x_A as its
    match pattern (they all produce patterns that include the fresh feature n).

    The score contribution of this fiber is:
      c_{x_A} · outcomeCount(θ(x_A), 0) = c_{x_A} · 1 = c_{x_A}. -/

lemma θ_xA (n : ℕ) (family : Finset (Finset (Fin n))) :
    θ (testExemplar n) (encodeDatabase n family) (x_A n) = {d₀ n} := by
  ext e
  simp only [mem_θ, Finset.mem_singleton]
  constructor
  · intro ⟨hmem, hpat⟩
    rw [encodeDatabase_mem_iff] at hmem
    rcases hmem with rfl | ⟨S, _, rfl⟩
    · rfl
    · rw [testExemplar_inter_dᵢ] at hpat
      exact absurd hpat.symm (xA_ne_embedFin_union_fresh n S)
  · rintro rfl
    exact ⟨d₀_mem n family, testExemplar_inter_d₀ n⟩

/-- The θ-fiber at x_A contains exactly one class-0 exemplar (d₀). -/
lemma outcomeCount_θ_xA (n : ℕ) (family : Finset (Finset (Fin n))) :
    outcomeCount (θ (testExemplar n) (encodeDatabase n family) (x_A n)) 0 = 1 := by
  rw [θ_xA, outcomeCount, Finset.filter_singleton,
    if_pos (show (d₀ n).outcome = (0 : Fin 2) from rfl), Finset.card_singleton]

/-- Every other θ-fiber (over a class-1 match pattern) contains no class-0 exemplars.
    The dᵢ exemplars all have outcome 1, so they never vote for class 0. -/
lemma outcomeCount_θ_non_xA (n : ℕ) (family : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ family) :
    outcomeCount (θ (testExemplar n) (encodeDatabase n family)
      (embedFin S ∪ {freshFeature n})) 0 = 0 := by
  simp only [outcomeCount]
  apply Finset.card_eq_zero.mpr
  ext e; constructor
  · intro he
    simp only [Finset.mem_filter, mem_θ] at he
    obtain ⟨⟨hmem, hpat⟩, hout⟩ := he
    rw [encodeDatabase_mem_iff] at hmem
    rcases hmem with rfl | ⟨T, _, rfl⟩
    · -- d₀ can't have match pattern embedFin S ∪ {n}: its pattern is x_A
      rw [testExemplar_inter_d₀] at hpat
      exact absurd hpat (xA_ne_embedFin_union_fresh n S)
    · -- dᵢ T has outcome 1, not 0
      simp [dᵢ] at hout
  · intro h; simp at h

/-! ### Section E: Support σ Characterization

    σ(p) is the set of exemplars whose features contain p — the set of exemplars
    "activated" when p is the queried pattern.

    For p ⊆ x_A (no fresh feature), the support splits cleanly:
    - d₀ is always in σ(p), because p ⊆ x_A = d₀.features.
    - dᵢ S is in σ(p) iff p ⊆ embedFin S.
      (The fresh feature n is always in dᵢ S's features but never in p ⊆ x_A,
       so n doesn't affect whether p ⊆ dᵢ S's features.) -/

lemma d₀_in_σ_of_sub_xA {n : ℕ} (family : Finset (Finset (Fin n)))
    {p : Finset (Fin (n + 1))} (hp : p ⊆ x_A n) :
    d₀ n ∈ σ (encodeDatabase n family) p := by
  rw [mem_σ]
  exact ⟨d₀_mem n family, hp.trans (by simp [x_A, d₀])⟩

/-- For p ⊆ x_A, dᵢ S ∈ σ(p) iff p ⊆ embedFin S.
    The fresh feature n cancels out: p never contains n (since p ⊆ x_A),
    so p ⊆ embedFin S ∪ {n} is equivalent to just p ⊆ embedFin S. -/
lemma dᵢ_in_σ_iff {n : ℕ} (family : Finset (Finset (Fin n)))
    {p : Finset (Fin (n + 1))} (hp : p ⊆ x_A n)
    {S : Finset (Fin n)} (hS : S ∈ family) :
    dᵢ n S ∈ σ (encodeDatabase n family) p ↔ p ⊆ embedFin S := by
  rw [mem_σ]
  constructor
  · intro ⟨_, hpd⟩
    intro x hx
    rcases Finset.mem_union.mp (hpd hx) with h | h
    · exact h
    · -- x would have to be freshFeature n, but x ∈ p ⊆ x_A and n ∉ x_A
      exact absurd (hp hx) (Finset.mem_singleton.mp h ▸ fresh_not_in_xA n)
  · intro hpS
    exact ⟨dᵢ_mem family hS, hpS.trans Finset.subset_union_left⟩

/-! ### Section F: Disagreement δ

    Two helper lemmas about when the disagreement count is positive or zero.
    These are needed for the homogeneity characterization in Section G. -/

/-- If two exemplars in σ(m) have different outcomes, δ(m) > 0.
    In the algorithm: if σ(m) contains both class-0 and class-1 exemplars, the
    pattern m is "conflicted" and δ will be nonzero. -/
lemma δ_pos_of_disagreeing {α β : Type*} [DecidableEq α] [DecidableEq β]
    {D : Database α β} {m : Finset α} {r s : Exemplar α β}
    (hr : r ∈ σ D m) (hs : s ∈ σ D m) (hne : r.outcome ≠ s.outcome) : 0 < δ D m := by
  rw [Nat.pos_iff_ne_zero]
  intro heq
  exact hne (δ_eq_zero_iff.mp heq r hr s hs)

/-- When q contains the fresh feature n, d₀ cannot be in σ(q): d₀ lacks feature n,
    so no pattern requiring n can be supported by d₀. -/
lemma d₀_not_in_σ_if_fresh {n : ℕ} (family : Finset (Finset (Fin n)))
    {q : Finset (Fin (n + 1))} (hq : freshFeature n ∈ q) :
    d₀ n ∉ σ (encodeDatabase n family) q := by
  rw [mem_σ]; push Not
  intro _; exact fun hsub => absurd (hsub hq) (d₀_not_fresh n)

/-- When q contains the fresh feature n, only class-1 exemplars can be in σ(q),
    so all exemplars in σ(q) agree on outcome 1, giving δ(q) = 0.
    This is the key reason why "adding n to a pattern" makes it homogeneous:
    the pattern stops seeing d₀, leaving only a unanimous class-1 support. -/
lemma δ_zero_of_fresh_in_q {n : ℕ} (family : Finset (Finset (Fin n)))
    {q : Finset (Fin (n + 1))} (hq : freshFeature n ∈ q) :
    δ (encodeDatabase n family) q = 0 := by
  rw [δ_eq_zero_iff]
  intro r hr s hs
  have hr_mem := (mem_σ.mp hr).1
  have hs_mem := (mem_σ.mp hs).1
  have hr_not_d₀ : r ≠ d₀ n := by
    intro h; exact absurd (h ▸ (mem_σ.mp hr).2 hq) (d₀_not_fresh n)
  have hs_not_d₀ : s ≠ d₀ n := by
    intro h; exact absurd (h ▸ (mem_σ.mp hs).2 hq) (d₀_not_fresh n)
  rw [encodeDatabase_mem_iff] at hr_mem hs_mem
  rcases hr_mem with rfl | ⟨Sr, _, rfl⟩
  · exact absurd rfl hr_not_d₀
  rcases hs_mem with rfl | ⟨Ss, _, rfl⟩
  · exact absurd rfl hs_not_d₀
  simp [dᵢ]

/-! ### Section G: Homogeneity Characterization

    This is the mathematical core of the reduction.

    A pattern p ⊆ x_A is homogeneous (in the sense used by the AM algorithm)
    if and only if p is NOT a subset of any Sᵢ in the family.

    Intuition:
    - If p ⊆ embedFin Sᵢ for some i: then both d₀ (class 0) and dᵢ Sᵢ (class 1)
      are in σ(p), so the pattern sees conflicting outcomes.  More specifically,
      the superset q = p ∪ {n} has δ(q) = 0 (only class-1 support) while δ(p) > 0
      (mixed support) — so δ is NOT constant going up, violating homogeneity.

    - If p ⊄ Sᵢ for all i: then σ(p) = {d₀} only.  For every superset q of p in τ:
      · If n ∈ q: d₀ ∉ σ(q), all of σ(q) is class-1, δ(q) = 0 = δ(p). ✓
      · If n ∉ q: q ⊆ x_A, so σ(q) ⊆ {d₀} (same argument as p), δ(q) = 0 = δ(p). ✓
      So δ is constant (always 0), and p is homogeneous. -/
theorem isHomogeneous_iff {n : ℕ} (family : Finset (Finset (Fin n)))
    {p : Finset (Fin (n + 1))} (hp : p ⊆ x_A n) :
    IsHomogeneous (testExemplar n) (encodeDatabase n family) p ↔
    ∀ S ∈ family, ¬(p ⊆ embedFin S) := by
  simp only [IsHomogeneous, mem_lattice, testExemplar]
  constructor
  · -- Forward: homogeneous ⟹ p is not a subset of any Sᵢ.
    -- If p ⊆ embedFin Sᵢ, we derive a contradiction: δ jumps from >0 at p to 0 at p ∪ {n}.
    intro ⟨_, hconst⟩ S hS hpS
    have hd₀ : d₀ n ∈ σ (encodeDatabase n family) p := d₀_in_σ_of_sub_xA family hp
    have hdᵢ : dᵢ n S ∈ σ (encodeDatabase n family) p :=
      (dᵢ_in_σ_iff family hp hS).mpr hpS
    -- Both d₀ and dᵢ S support p with different outcomes, so δ(p) > 0.
    have hδp_pos : 0 < δ (encodeDatabase n family) p :=
      δ_pos_of_disagreeing hd₀ hdᵢ (d₀_outcome_ne_dᵢ n S)
    -- The superset q = p ∪ {n} has d₀ ∉ σ(q), so σ(q) is all class-1, δ(q) = 0.
    set q := p ∪ {freshFeature n} with hq_def
    have hfresh_q : freshFeature n ∈ q := Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hpq : p ⊆ q := Finset.subset_union_left
    -- dᵢ S ∈ σ(q) because q = p ∪ {n} ⊆ embedFin S ∪ {n} = dᵢ S's features.
    have hq_ne : (σ (encodeDatabase n family) q).Nonempty :=
      ⟨dᵢ n S, mem_σ.mpr ⟨dᵢ_mem family hS, by
        rw [hq_def]
        exact Finset.union_subset (hpS.trans Finset.subset_union_left) Finset.subset_union_right⟩⟩
    have hδq_zero : δ (encodeDatabase n family) q = 0 := δ_zero_of_fresh_in_q family hfresh_q
    -- By homogeneity, δ(q) = δ(p) — but 0 = δ(q) ≠ δ(p) > 0. Contradiction.
    have hδq_eq : δ (encodeDatabase n family) q = δ (encodeDatabase n family) p :=
      hconst q (Finset.subset_univ _) hpq hq_ne
    linarith [hδp_pos, hδq_zero, hδq_eq]
  · -- Backward: p ⊄ any Sᵢ ⟹ p is homogeneous.
    -- σ(p) = {d₀} only, so δ(p) = 0, and for every superset q the δ stays 0.
    intro hno
    have hσ_only_d₀ : ∀ e ∈ σ (encodeDatabase n family) p, e = d₀ n := by
      intro e he
      have hemem := (mem_σ.mp he).1
      rw [encodeDatabase_mem_iff] at hemem
      rcases hemem with rfl | ⟨S, hS, rfl⟩
      · rfl
      · exact absurd ((dᵢ_in_σ_iff family hp hS).mp he) (hno S hS)
    have hδp_zero : δ (encodeDatabase n family) p = 0 := by
      rw [δ_eq_zero_iff]; intro r hr s hs
      rw [hσ_only_d₀ r hr, hσ_only_d₀ s hs]
    refine ⟨⟨d₀ n, d₀_in_σ_of_sub_xA family hp⟩, fun q hqτ hpq hqne => ?_⟩
    rw [hδp_zero]
    by_cases hn : freshFeature n ∈ q
    · -- q contains n → d₀ not in σ(q) → all class-1 → δ(q) = 0
      exact δ_zero_of_fresh_in_q family hn
    · -- q doesn't contain n → q ⊆ x_A → σ(q) ⊆ {d₀} → δ(q) = 0
      have hq_sub_xA : q ⊆ x_A n := sub_xA_of_no_fresh hn
      rw [δ_eq_zero_iff]; intro r hr s hs
      have : ∀ e ∈ σ (encodeDatabase n family) q, e = d₀ n := by
        intro e he
        have hemem := (mem_σ.mp he).1
        rw [encodeDatabase_mem_iff] at hemem
        rcases hemem with rfl | ⟨S, hS, rfl⟩
        · rfl
        · -- dᵢ S ∈ σ(q) → q ⊆ embedFin S → p ⊆ q ⊆ embedFin S → contradicts hno
          exact absurd (hpq.trans ((dᵢ_in_σ_iff family hq_sub_xA hS).mp he)) (hno S hS)
      rw [this r hr, this s hs]

/-! ### Section H: Counting c_{x_A}

    In the AM algorithm, c_x = |{p ⊆ x : p is homogeneous in (τ, D)}|.
    This is the weight that multiplies each θ-fiber score in the representation theorem.

    At x_A, the homogeneous subsets are exactly those that avoid all Sᵢ (Section G).
    The "bad" subsets — those that hit at least one Sᵢ — form the union of powersets
    ⋃ᵢ ℘(embedFin Sᵢ).  Since these two sets partition ℘(x_A), we get:
      c_{x_A} + |⋃ᵢ ℘(embedFin Sᵢ)| = 2^n. -/

/-- c_{x_A} equals the number of subsets of x_A that are not contained in any Sᵢ. -/
theorem c_xA_eq_card_avoiding {n : ℕ} (family : Finset (Finset (Fin n))) :
    c (testExemplar n) (encodeDatabase n family) (x_A n) =
    (x_A n |>.powerset.filter (fun p => ∀ S ∈ family, ¬(p ⊆ embedFin S))).card := by
  simp only [c]
  congr 1; ext p
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun ⟨hpx, hHom⟩ => ⟨hpx, (isHomogeneous_iff family hpx).mp hHom⟩,
         fun ⟨hpx, hno⟩  => ⟨hpx, (isHomogeneous_iff family hpx).mpr hno⟩⟩

/-- The "bad" subsets of x_A: those contained in at least one member of the family
    (viewed via embedFin).  These are exactly the subsets that are NOT homogeneous. -/
def unionEmbeddedPowersets {n : ℕ} (family : Finset (Finset (Fin n))) :
    Finset (Finset (Fin (n + 1))) :=
  family.biUnion (fun S => (embedFin S).powerset)

/-- **c_{x_A} counting equation**: the homogeneous and non-homogeneous subsets of x_A
    partition ℘(x_A), so their counts sum to 2^n.

    In AM terms: (# "good" sub-patterns of x_A) + (# "bad" sub-patterns) = 2^|x_A| = 2^n. -/
theorem c_xA_counting {n : ℕ} (family : Finset (Finset (Fin n))) :
    c (testExemplar n) (encodeDatabase n family) (x_A n) +
    (unionEmbeddedPowersets family).card = 2 ^ n := by
  rw [c_xA_eq_card_avoiding, ← x_A_powerset_card]
  set A := (x_A n).powerset.filter (fun p => ∀ S ∈ family, ¬(p ⊆ embedFin S))
  set B := unionEmbeddedPowersets family ∩ (x_A n).powerset
  -- A and B partition ℘(x_A): every subset either avoids all Sᵢ (in A) or hits one (in B).
  have hpart : A ∪ B = (x_A n).powerset := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, Finset.mem_inter,
               unionEmbeddedPowersets, Finset.mem_biUnion]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact h
    · intro hp
      by_cases h : ∀ S ∈ family, ¬(p ⊆ embedFin S)
      · exact Or.inl ⟨hp, h⟩
      · push Not at h
        obtain ⟨S, hS, hpS⟩ := h
        exact Or.inr ⟨⟨S, hS, hpS⟩, hp⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [A, Finset.mem_filter] at hp
    simp only [B, Finset.mem_inter, unionEmbeddedPowersets, Finset.mem_biUnion,
               Finset.mem_powerset] at hq
    obtain ⟨⟨S, hS, hpS⟩, _⟩ := hq
    exact hp.2 S hS hpS
  -- B has the same cardinality as unionEmbeddedPowersets because every element of
  -- unionEmbeddedPowersets is already a subset of x_A (embedFin lands in x_A).
  have huniv_card : B.card = (unionEmbeddedPowersets family).card := by
    have hB_eq : B = unionEmbeddedPowersets family := by
      simp only [B]
      apply Finset.inter_eq_left.mpr
      intro p hp
      simp only [Finset.mem_powerset]
      simp only [unionEmbeddedPowersets, Finset.mem_biUnion, Finset.mem_powerset] at hp
      obtain ⟨S, _, hpS⟩ := hp
      exact hpS.trans (fun x hx => by
        simp only [embedFin, Finset.mem_image] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact mem_xA_of_ne_fresh (Fin.castSucc_ne_last y))
    rw [hB_eq]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hpart] at hcard
  linarith [huniv_card]

/-! ### Section I: Score Computation

    In the AM algorithm, the total score for outcome o is:
      Σ_{x ∈ M} c_x · outcomeCount(θ(x), o)

    For outcome 0 in our encoded database:
    - The only element of M that contributes is x_A (since all other fibers have
      outcomeCount = 0 for class 0).
    - The contribution of x_A is c_{x_A} · 1 = c_{x_A}.
    So totalScore(τ, D, 0) = c_{x_A}. -/

/-- The match set M has exactly two types of elements:
    x_A (from d₀) and embedFin S ∪ {n} (from each dᵢ S). -/
lemma matchSet_encodeDatabase (n : ℕ) (family : Finset (Finset (Fin n))) :
    matchSet (testExemplar n) (encodeDatabase n family) =
    {x_A n} ∪ family.image (fun S => embedFin S ∪ {freshFeature n}) := by
  ext x
  simp only [mem_matchSet, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ⟨e, hemem, rfl⟩
    rw [encodeDatabase_mem_iff] at hemem
    rcases hemem with rfl | ⟨S, hS, rfl⟩
    · exact Or.inl (testExemplar_inter_d₀ n)
    · exact Or.inr ⟨S, hS, (testExemplar_inter_dᵢ n S).symm⟩
  · rintro (rfl | ⟨S, hS, rfl⟩)
    · exact ⟨d₀ n, d₀_mem n family, testExemplar_inter_d₀ n⟩
    · exact ⟨dᵢ n S, dᵢ_mem family hS, testExemplar_inter_dᵢ n S⟩

/-- The total class-0 score equals c_{x_A}, because x_A is the only element of M
    whose θ-fiber contains any class-0 exemplars. -/
theorem totalScore_eq_c_xA {n : ℕ} (family : Finset (Finset (Fin n))) :
    totalScore (testExemplar n) (encodeDatabase n family) 0 =
    c (testExemplar n) (encodeDatabase n family) (x_A n) := by
  simp only [totalScore, matchSet_encodeDatabase]
  rw [Finset.sum_union]
  · simp only [Finset.sum_singleton, outcomeCount_θ_xA]
    suffices h : (family.image (fun S => embedFin S ∪ {freshFeature n})).sum
        (fun x => c (testExemplar n) (encodeDatabase n family) x *
          outcomeCount (θ (testExemplar n) (encodeDatabase n family) x) 0) = 0 by
      rw [h]; ring
    apply Finset.sum_eq_zero
    intro x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    rw [outcomeCount_θ_non_xA n family hS, Nat.mul_zero]
  · -- x_A and the class-1 patterns are disjoint in M.
    simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_image]
    rintro x rfl ⟨S, _, hS⟩
    exact xA_ne_embedFin_union_fresh n S hS.symm

/-! ### Section J: Main Hardness Theorem -/

/-- **#P-Hardness of Exact AM Scoring** (Johnsen & Johansson 2005, §4.3).

    For the encoded database, the class-0 AM score and the union-of-powersets count
    sum to exactly 2^n:

      totalScore(τ, D, 0) + |⋃ᵢ ℘(embedFin Sᵢ)| = 2^n

    This means:
    - Given an oracle for `totalScore`, recover |⋃ᵢ ℘(Sᵢ)| = 2^n − score.
    - The construction (encodeDatabase) is polynomial in n and |family|.
    - Therefore #⋃℘ ≤_T exact-AM-scoring (Turing reduction in polynomial time).

    Since Basic.lean proves #VERTEX-COVER ≤ #⋃℘ and #VERTEX-COVER is #P-hard
    (Greenhill 2000), the chain  #VERTEX-COVER ≤ #⋃℘ ≤ exact-AM  makes exact AM
    scoring #P-hard.

    Note on the Lean code: the two ends of this chain are proved in separate files
    (Basic.lean and this file).  The connection is conceptual: this theorem shows
    that an oracle for AM lets you solve #⋃℘, and Basic.lean shows that #⋃℘ is
    at least as hard as #VERTEX-COVER. -/
theorem exact_AM_scoring_is_hard (n : ℕ) (family : Finset (Finset (Fin n))) :
    totalScore (testExemplar n) (encodeDatabase n family) 0 +
    (unionEmbeddedPowersets family).card = 2 ^ n := by
  rw [totalScore_eq_c_xA]
  exact c_xA_counting family
