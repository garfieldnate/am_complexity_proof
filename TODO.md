# Project TODO: AM #P-Completeness Formalization

## What we have proved (informal + Lean)

### Informal (proof.md)
- #⋃℘ is in #P (membership verifiable in polynomial time)
- #VERTEX-COVER ≤ #⋃℘ via: given G=(V,E), set Sⱼ = V \ eⱼ for each edge eⱼ
  - T is a vertex cover ↔ T ∉ ⋃ⱼ ℘(Sⱼ)
  - #vertex covers = 2^|V| − |⋃ⱼ ℘(Sⱼ)|
- Therefore #⋃℘ is #P-complete
- Reference for #VERTEX-COVER being #P-hard: Greenhill (2000)

### Lean (CountUnionFamilyPowersetsProof/Basic.lean)
- `IsVertexCover edges T` — definition
- `unionComplementPowersets V edges` — definition of ⋃ ℘(V \ e)
- `unionComplementPowersets_subset` — all elements lie in V.powerset
- `isVertexCover_iff_not_mem_unionComplementPowersets` — the KEY bijection
- `vertexCovers_disjoint` — vertex covers and union are disjoint in V.powerset
- `vertexCovers_union_eq` — together they partition V.powerset
- `counting_equation` — #vertex covers + |⋃ ℘(V \ e)| = 2^|V|

## What we want to prove next

### Goal: exact AM scoring is #P-complete

**Claim**: Computing the total analogical set score is #P-hard.

**Proof strategy**: Show #⋃℘ ≤ exact-AM-scoring via explicit database construction:

Given {S₁,...,Sₖ} ⊆ [n-1] (a #⋃℘ instance), construct:
- τ = {0,...,n}  (add one fresh feature `n`)
- d₀: features = {0,...,n-1},  outcome = 0  (one class-0 exemplar)
- dᵢ: features = Sᵢ ∪ {n},    outcome = 1  (k class-1 exemplars)

Key facts to verify:
- A  = {0,...,n-1} ∈ M_A  (deterministically homogeneous: σ(A) = {d₀} only)
- Bᵢ = Sᵢ ∪ {n}   ∈ M_A  (deterministically homogeneous: σ(Bᵢ) ⊆ {dⱼ | Sᵢ ⊆ Sⱼ})
- H(A) = {A ∩ Bᵢ} = {Sᵢ}  (exactly the #⋃℘ input family)
- c_A = 2ⁿ − |⋃ᵢ ℘(Sᵢ)|   (readable from the AM score)

This gives #⋃℘ ≤ exact-AM, so combined with Basic.lean: exact-AM is #P-hard.

## Lean formalization plan

### Step 1: Core data structures (new file: AM/Basic.lean)

```lean
structure Exemplar (α β : Type*) where
  features : Finset α
  outcome  : β

-- A database is a Finset of exemplars
abbrev Database (α β : Type*) := Finset (Exemplar α β)
```

### Step 2: The five core AM functions (AM/Functions.lean)

```lean
-- Match set: M = { τ ∩ d.features | d ∈ D }
def matchSet (τ : Finset α) (D : Database α β) : Finset (Finset α) :=
  D.image (fun d => τ ∩ d.features)

-- θ: partition D by which element of M they produce
def θ (τ : Finset α) (D : Database α β) (a : Finset α) : Finset (Exemplar α β) :=
  D.filter (fun d => τ ∩ d.features = a)

-- σ: support — all exemplars whose features contain m
def σ (D : Database α β) (m : Finset α) : Finset (Exemplar α β) :=
  D.filter (fun d => m ⊆ d.features)

-- κ: disagreement between two exemplars
def κ (r s : Exemplar α β) : ℕ := if r.outcome ≠ s.outcome then 1 else 0

-- δ: total disagreement in σ(m)
def δ (D : Database α β) (m : Finset α) : ℕ :=
  (σ D m ×ˢ σ D m).sum (fun (r, s) => κ r s)
```

### Step 3: Homogeneity (AM/Homogeneity.lean)

```lean
-- m is homogeneous if it has non-empty support and all supersets with
-- non-empty support have the same disagreement count
def IsHomogeneous (τ : Finset α) (D : Database α β) (m : Finset α) : Prop :=
  (σ D m).Nonempty ∧
  ∀ n ∈ τ.powerset, m ⊆ n → (σ D n).Nonempty → δ D n = δ D m

-- Deterministic homogeneity: homogeneous with δ = 0
def IsDeterministicallyHomogeneous (τ : Finset α) (D : Database α β) (m : Finset α) : Prop :=
  IsHomogeneous τ D m ∧ δ D m = 0

-- The analogical set A ⊆ L = τ.powerset
def analogicalSet (τ : Finset α) (D : Database α β) : Finset (Finset α) :=
  τ.powerset.filter (IsHomogeneous τ D)
```

### Step 4: Scoring (AM/Score.lean)

```lean
-- outcome vector: count of each outcome in a set of exemplars
-- (simplest case: two outcomes, represented as ℕ × ℕ)

-- Total analogical set score (Theorem 1 from the paper):
-- tot = Σ_{p ∈ A} score(σ(p)) = Σ_{x ∈ M} c_x · score(θ(x))
-- where c_x = |{p ∈ ℘(x) | p is homogeneous}|
def c (τ : Finset α) (D : Database α β) (x : Finset α) : ℕ :=
  (x.powerset.filter (IsHomogeneous τ D)).card
```

### Step 5: Key lemmas needed

- `σ_antitone`: m ⊆ n → σ(D)(n) ⊆ σ(D)(m)  (σ is antitone on L)
- `θ_partition`: θ partitions D (Proposition 1 from paper — already proved informally)
- `σ_eq_union_θ`: σ(p) = ⋃_{p ⊆ x, x ∈ M} θ(x)  (Proposition 2 from paper)
- `representation_theorem`: tot = Σ_{x ∈ M} c_x · score(θ(x))  (Theorem 1)

### Step 6: The hardness reduction (AM/Hardness.lean)

```lean
-- Construct the specific database encoding a #⋃℘ instance
def encodeInstance (n : ℕ) (family : Finset (Finset (Fin n))) :
    Finset α × Database (Fin (n+1)) (Fin 2) := ...

-- Key lemma: H(A) = family in the constructed instance
-- Key lemma: c_A in the constructed instance = 2^n - |⋃ ℘(Sᵢ)|
-- Main theorem: exact-AM-scoring is #P-hard
```

## File structure

```
CountUnionFamilyPowersetsProof/
  Basic.lean          ✅ DONE — #⋃℘ is #P-complete
  AM/
    Basic.lean        ✅ DONE — Exemplar, Database, lattice L=℘(τ)
    Functions.lean    ✅ DONE — matchSet, θ, σ, κ, δ; Props 1+2
    Homogeneity.lean  ✅ DONE — IsHomogeneous, IsDetermHomogeneous, analogicalSet A
    Score.lean        ✅ DONE — outcomeCount, c_x coefficients, totalScore, totalScoreA
    Propositions.lean ⚠ PARTIAL — key aux lemmas done; Theorem 1 body is sorry
    Hardness.lean     ⚠ PARTIAL — database construction + structural lemmas done;
                                  hardness theorem statement is placeholder (trivial sorry)
```

## Remaining work (Propositions.lean + Hardness.lean)

### Propositions.lean: Theorem 1 (representation_theorem)
Need to prove `totalScoreA τ D o = totalScore τ D o` via double-counting.
Key Lean tactic: `Finset.sum_comm'` or `Finset.sum_sigma'` to swap the sum over
(p ∈ A, d ∈ σ(p)) into a sum over (x ∈ M, d ∈ θ(x)) weighted by c_x.
The auxiliary lemmas `mem_σ_iff_subset_inter` and `c_eq_card_homogeneous_subsets`
are proven and provide the key bijections.

### Hardness.lean: exact_AM_scoring_is_hard
Need to prove the actual inequality:
  c (testExemplar n) (encodeDatabase n family) (embedFin Finset.univ) =
  2^n − (unionComplementPowersets Finset.univ (family.image (fun S => Finset.univ \ S))).card

This requires:
1. Showing homogeneous subsets of x_A = embedFin Finset.univ in the constructed database
   correspond exactly to vertex covers of the complement-edge graph.
2. Applying counting_equation from Basic.lean.
3. Combining with representation_theorem to get the reduction.

## Key references
- Johnsen & Johansson (2005): "Efficient Modeling of Analogy"
  - §3: definitions of L, M, θ, σ, δ, homogeneity, A
  - §4: Propositions 1+2, Theorem 1 (representation theorem)
  - §4.3: Monte Carlo for c_x (because #⋃℘ is hard)
- Greenhill (2000): #VERTEX-COVER is #P-hard
- Valiant (1979): introduced #P
- Toda (1991): PH ⊆ P^#P

## Notes
- `open Classical` is used in Basic.lean to avoid `DecidablePred (IsVertexCover)`.
  In the AM files, homogeneity will have the same issue. Accept this for now.
- The lattice L = ℘(τ) is a Boolean algebra; Mathlib's `BooleanAlgebra` typeclass
  applies, but we work with `Finset` concretely rather than through the abstraction.
- σ antitone on L is key for many proofs; prove it early as a standalone lemma.
- The hardness reduction uses `Fin (n+1)` for the feature type and `Fin 2` for outcomes.
