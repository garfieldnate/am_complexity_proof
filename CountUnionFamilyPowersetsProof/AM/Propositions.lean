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
  -- Do NOT unfold c yet; we need c_eq_card_homogeneous_subsets to apply directly.
  simp only [totalScoreA, totalScore, outcomeCount]
  -- Step 1: For each p ∈ A ⊆ ℘(τ), expand |σ(p) ∩ D_o| via Proposition 2.
  have lhs_eq : ∀ p ∈ analogicalSet τ D,
      ((σ D p).filter (fun d => d.outcome = o)).card =
      (matchSet τ D).sum (fun x =>
        if p ⊆ x then ((θ τ D x).filter (fun d => d.outcome = o)).card else 0) := by
    intro p hp
    rw [mem_analogicalSet] at hp
    -- σ(p) = ⋃_{p ⊆ x, x ∈ M} θ(x); filter distributes over biUnion
    have heq : ((σ D p).filter (fun d => d.outcome = o)) =
        (matchSet τ D).biUnion (fun x =>
          (if p ⊆ x then θ τ D x else ∅).filter (fun d => d.outcome = o)) := by
      rw [σ_eq_biUnion_θ hp.1]
      ext d; simp [Finset.mem_biUnion, Finset.mem_filter]; tauto
    -- Disjointness of the filtered θ-fibers
    have hdisj : ∀ x ∈ matchSet τ D, ∀ y ∈ matchSet τ D, x ≠ y →
        Disjoint ((if p ⊆ x then θ τ D x else ∅).filter (fun d => d.outcome = o))
                 ((if p ⊆ y then θ τ D y else ∅).filter (fun d => d.outcome = o)) := by
      intro x _ y _ hne
      split_ifs with hpx hpy
      · exact (θ_disjoint hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      · simp
      · simp
      · simp
    rw [heq, Finset.card_biUnion hdisj]
    -- Pointwise: ((if p ⊆ x then θ x else ∅).filter f).card = if p ⊆ x then |θ(x) ∩ Do| else 0
    apply Finset.sum_congr rfl; intro x _
    split_ifs with hpx <;> simp
  rw [Finset.sum_congr rfl lhs_eq]
  -- Step 2: Swap the independent double sum (A × M → M × A)
  rw [Finset.sum_comm]
  -- Step 3: For each x ∈ M, the inner sum Σ_{p ∈ A} (if p ⊆ x then c else 0) = c_x * c
  apply Finset.sum_congr rfl; intro x hx
  -- Pull the constant out using filter + sum_const_nat
  rw [← Finset.sum_filter, Finset.sum_const_nat (fun _ _ => rfl)]
  -- Now: ((analogicalSet τ D).filter (· ⊆ x)).card * |...| = c τ D x * |...|
  congr 1
  exact (c_eq_card_homogeneous_subsets hx).symm
