import CountUnionFamilyPowersetsProof.AM.Score

set_option linter.style.openClassical false
open Classical

/-!
## Analogical Modeling — Representation Theorem (Theorem 1)

Proves the fundamental representation theorem from Johnsen & Johansson (2005), §4:

  Σ_{p ∈ A} outcomeCount(σ(p), o) = Σ_{x ∈ M} c_x · outcomeCount(θ(x), o)

**Proof sketch** (double-counting over pairs (p, d)):

  LHS = Σ_{p ∈ A} Σ_{d ∈ σ(p), d.outcome=o} 1
      = Σ_{d ∈ D, d.outcome=o} |{p ∈ A | d ∈ σ(p)}|    (swap sums)

For p ∈ A ⊆ ℘(τ) and d ∈ D:
  d ∈ σ(p) ↔ p ⊆ d.features
           ↔ p ⊆ τ ∩ d.features   (since p ⊆ τ)

Letting x = τ ∩ d.features (the unique element of M with d ∈ θ(x)):
  |{p ∈ A | d ∈ σ(p)}| = |{p ∈ ℘(x) | p is homogeneous}| = c_x

Then grouping by x ∈ M (using that θ partitions D):
  = Σ_{x ∈ M} Σ_{d ∈ θ(x), d.outcome=o} c_x
  = Σ_{x ∈ M} c_x · outcomeCount(θ(x), o) = RHS
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! ### Key Auxiliary Lemma -/

/-- For p ⊆ τ and d ∈ D: d ∈ σ(p) ↔ p ⊆ τ ∩ d.features.

    This is the bridge between σ (defined via ⊆ d.features) and M
    (defined via τ ∩ d.features): restricting to p ∈ lattice τ lets us
    replace d.features by the matched pattern τ ∩ d.features. -/
lemma mem_σ_iff_subset_inter {τ : Finset α} {D : Database α β} {p : Finset α} (hp : p ⊆ τ)
    {d : Exemplar α β} (hd : d ∈ D) : d ∈ σ D p ↔ p ⊆ τ ∩ d.features := by
  rw [mem_σ]
  constructor
  · intro ⟨_, hpd⟩
    exact Finset.subset_inter hp hpd
  · intro h
    exact ⟨hd, h.trans Finset.inter_subset_right⟩

/-- For p ∈ A ⊆ ℘(τ) and d ∈ θ(x):
    the set {p ∈ A | d ∈ σ(p)} equals {p ∈ A | p ⊆ x}. -/
lemma homogeneous_in_σ_iff_subset {τ : Finset α} {D : Database α β} {x : Finset α}
    {d : Exemplar α β} (hd : d ∈ θ τ D x) {p : Finset α} (hp : p ⊆ τ) :
    d ∈ σ D p ↔ p ⊆ x := by
  rw [mem_σ_iff_subset_inter hp (θ_subset τ D x hd), (mem_θ.mp hd).2]

/-- c_x = |{p ∈ A | p ⊆ x}| for x ∈ M: the homogeneous powerset count equals
    the number of homogeneous elements of A that are subsets of x.

    Key: A ∩ ℘(x) = {p ∈ ℘(x) | IsHomogeneous τ D p}, since A ⊆ ℘(τ) and
    for p ⊆ x ⊆ τ, p ∈ ℘(x) iff p ∈ ℘(τ) ∧ p ⊆ x. -/
lemma c_eq_card_homogeneous_subsets {τ : Finset α} {D : Database α β} {x : Finset α}
    (hx : x ∈ matchSet τ D) :
    c τ D x = (analogicalSet τ D |>.filter (· ⊆ x)).card := by
  -- analogicalSet τ D |>.filter (· ⊆ x) = x.powerset.filter (IsHomogeneous τ D)
  -- because p ∈ analogicalSet ∧ p ⊆ x ↔ p ⊆ τ ∧ IsHom p ∧ p ⊆ x
  -- and p ⊆ x ∧ x ⊆ τ → p ⊆ τ, and x ∈ matchSet → x ⊆ τ
  have hx_lat : x ∈ lattice τ := matchSet_subset_lattice τ D hx
  have hxτ : x ⊆ τ := mem_lattice.mp hx_lat
  simp only [c, analogicalSet]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hpx, hHom⟩
    exact ⟨⟨hpx.trans hxτ, hHom⟩, hpx⟩
  · rintro ⟨⟨_, hHom⟩, hpx⟩
    exact ⟨hpx, hHom⟩

/-! ### The Representation Theorem -/

/-- **Theorem 1** (Johnsen & Johansson 2005, §4):
    The total analogical score computed via the analogical set A equals
    the total score computed via the (smaller) match set M with c_x weights.

      totalScoreA τ D o = totalScore τ D o

    i.e., Σ_{p ∈ A} outcomeCount(σ(p), o) = Σ_{x ∈ M} c_x · outcomeCount(θ(x), o)

    This is the key computational result: instead of summing over exponentially many
    elements of L, we only need |M| ≤ |D| terms. Computing c_x is #P-hard
    (equivalent to #⋃℘), but the representation reduces the outer sum to polynomial
    size. -/
theorem representation_theorem (τ : Finset α) (D : Database α β) (o : β) :
    totalScoreA τ D o = totalScore τ D o := by
  simp only [totalScoreA, totalScore, outcomeCount]
  -- The proof swaps the order of summation: sum over (p, d) pairs.
  -- Key steps (all pending formalization via Finset.sum_comm'):
  -- 1. Expand each summand as a Finset.card = Σ 1
  -- 2. Swap: Σ_{p ∈ A} Σ_{d ∈ σ(p) with d.outcome=o} 1
  --        = Σ_{d ∈ D with d.outcome=o} |{p ∈ A | p ⊆ τ ∩ d.features}|
  --        (using mem_σ_iff_subset_inter)
  -- 3. |{p ∈ A | p ⊆ τ ∩ d.features}| = c(τ ∩ d.features)
  --    (using c_eq_card_homogeneous_subsets)
  -- 4. Group d's by x = τ ∩ d.features using D_eq_biUnion_θ
  -- 5. For each x ∈ M: contributes c(x) · |{d ∈ θ(x) | d.outcome = o}|
  sorry
