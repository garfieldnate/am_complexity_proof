import CountUnionFamilyPowersetsProof.AM.Basic

set_option linter.style.openClassical false
open Classical

/-!
## Analogical Modeling — Core Functions

Formalizes θ, σ, κ, δ, and the match set M from Johnsen & Johansson (2005), §3.

The five key objects:
- `matchSet τ D`  — M: the set of feature intersections { τ ∩ d | d ∈ D }
- `θ τ D a`       — partition of D by which element of M each exemplar produces
- `σ D m`         — support: all exemplars whose features contain m
- `κ r s`         — 1 if r and s disagree on outcome, else 0
- `δ D m`         — total disagreement within σ(m)
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! ### Match Set M -/

/-- M = { τ ∩ d.features | d ∈ D }: all ways τ can overlap with database exemplars. -/
def matchSet (τ : Finset α) (D : Database α β) : Finset (Finset α) :=
  D.image (fun d => τ ∩ d.features)

lemma matchSet_subset_lattice (τ : Finset α) (D : Database α β) :
    matchSet τ D ⊆ lattice τ := by
  intro m hm
  simp only [matchSet, Finset.mem_image] at hm
  obtain ⟨d, _, rfl⟩ := hm
  exact inter_mem_lattice τ d.features

@[simp]
lemma mem_matchSet {τ : Finset α} {D : Database α β} {m : Finset α} :
    m ∈ matchSet τ D ↔ ∃ d ∈ D, τ ∩ d.features = m :=
  Finset.mem_image

/-! ### θ: Partition of D -/

/-- θ(a) = { d ∈ D | τ ∩ d.features = a }.
    The sets θ(a) for a ∈ M partition D (Proposition 1 of the paper). -/
def θ (τ : Finset α) (D : Database α β) (a : Finset α) : Finset (Exemplar α β) :=
  D.filter (fun d => τ ∩ d.features = a)

lemma mem_θ {τ : Finset α} {D : Database α β} {a : Finset α} {d : Exemplar α β} :
    d ∈ θ τ D a ↔ d ∈ D ∧ τ ∩ d.features = a :=
  Finset.mem_filter

lemma θ_subset (τ : Finset α) (D : Database α β) (a : Finset α) : θ τ D a ⊆ D :=
  Finset.filter_subset _ _

/-- **Proposition 1**: θ(x) and θ(y) are disjoint when x ≠ y. -/
theorem θ_disjoint {τ : Finset α} {D : Database α β} {x y : Finset α} (hxy : x ≠ y) :
    Disjoint (θ τ D x) (θ τ D y) := by
  rw [Finset.disjoint_left]
  intro d hdx hdy
  rw [mem_θ] at hdx hdy
  exact hxy (hdx.2.symm.trans hdy.2)

/-- D is exactly covered by the θ-fibers over the match set. -/
lemma D_eq_biUnion_θ (τ : Finset α) (D : Database α β) :
    D = (matchSet τ D).biUnion (θ τ D) := by
  ext d
  simp only [Finset.mem_biUnion, mem_matchSet, mem_θ]
  constructor
  · intro hd
    exact ⟨τ ∩ d.features, ⟨d, hd, rfl⟩, hd, rfl⟩
  · rintro ⟨_, ⟨d', _, rfl⟩, hd, _⟩
    exact hd

/-! ### σ: Support Function -/

/-- σ(m) = { d ∈ D | m ⊆ d.features }: the support of pattern m.
    Antitone on L: more specific patterns have smaller support sets. -/
def σ (D : Database α β) (m : Finset α) : Finset (Exemplar α β) :=
  D.filter (fun d => m ⊆ d.features)

lemma mem_σ {D : Database α β} {m : Finset α} {d : Exemplar α β} :
    d ∈ σ D m ↔ d ∈ D ∧ m ⊆ d.features :=
  Finset.mem_filter

/-- σ is antitone: more specific patterns have smaller support. -/
theorem σ_antitone {D : Database α β} {m n : Finset α} (hmn : m ⊆ n) :
    σ D n ⊆ σ D m := by
  intro d hd
  rw [mem_σ] at hd ⊢
  exact ⟨hd.1, hmn.trans hd.2⟩

/-- θ(a) ⊆ σ(a): the θ-fiber is contained in the support. -/
lemma θ_subset_σ {τ : Finset α} {D : Database α β} (a : Finset α) :
    θ τ D a ⊆ σ D a := by
  intro d hd
  rw [mem_θ] at hd
  rw [mem_σ]
  exact ⟨hd.1, hd.2 ▸ Finset.inter_subset_right⟩

/-- **Proposition 2**: σ(p) = ⋃_{x ∈ M, p ⊆ x} θ(x), for p ∈ L (i.e. p ⊆ τ). -/
theorem σ_eq_biUnion_θ {τ : Finset α} {D : Database α β} {p : Finset α} (hp : p ⊆ τ) :
    σ D p = (matchSet τ D).biUnion (fun x => if p ⊆ x then θ τ D x else ∅) := by
  ext d
  constructor
  · -- d ∈ σ(p): witness x = τ ∩ d.features
    intro hd
    rw [mem_σ] at hd
    rw [Finset.mem_biUnion]
    refine ⟨τ ∩ d.features, ?_, ?_⟩
    · rw [mem_matchSet]; exact ⟨d, hd.1, rfl⟩
    · rw [if_pos (Finset.subset_inter hp hd.2), mem_θ]
      exact ⟨hd.1, rfl⟩
  · -- d in the union: the chosen x gives p ⊆ τ ∩ d'.features = τ ∩ d.features ⊆ d.features
    intro hd
    rw [Finset.mem_biUnion] at hd
    obtain ⟨x, hxM, hdx⟩ := hd
    rw [mem_matchSet] at hxM
    obtain ⟨d', hd'D, rfl⟩ := hxM
    rw [mem_σ]
    split_ifs at hdx with hpx
    · rw [mem_θ] at hdx
      -- hdx.2 : τ ∩ d.features = τ ∩ d'.features
      -- so τ ∩ d'.features ⊆ d.features via hdx.2.symm
      have hle : τ ∩ d'.features ⊆ d.features := by
        rw [hdx.2.symm]; exact Finset.inter_subset_right
      exact ⟨hdx.1, hpx.trans hle⟩
    · simp at hdx

/-! ### κ and δ: Disagreement -/

/-- κ(r, s) = 1 if r and s disagree on outcome, else 0. -/
def κ (r s : Exemplar α β) : ℕ :=
  if r.outcome ≠ s.outcome then 1 else 0

@[simp] lemma κ_self (d : Exemplar α β) : κ d d = 0 := by simp [κ]

lemma κ_comm (r s : Exemplar α β) : κ r s = κ s r := by
  simp only [κ, ne_eq]
  simp [ne_comm]

/-- δ(m) = Σ_{(r,s) ∈ σ(m) × σ(m)} κ(r,s): total pairwise disagreement. -/
def δ (D : Database α β) (m : Finset α) : ℕ :=
  ((σ D m) ×ˢ (σ D m)).sum (fun rs => κ rs.1 rs.2)

/-- δ = 0 iff all exemplars in the support agree on outcome. -/
theorem δ_eq_zero_iff {D : Database α β} {m : Finset α} :
    δ D m = 0 ↔ ∀ r ∈ σ D m, ∀ s ∈ σ D m, r.outcome = s.outcome := by
  simp only [δ, Finset.sum_eq_zero_iff, Finset.mem_product, κ, ne_eq, ite_eq_right_iff,
             one_ne_zero, imp_false, not_not]
  constructor
  · intro h r hr s hs
    exact h (r, s) ⟨hr, hs⟩
  · intro h (r, s) ⟨hr, hs⟩
    exact h r hr s hs

/-- A finer (more specific) pattern with non-empty support has δ ≥ 0;
    the key constraint is that homogeneity requires δ to be CONSTANT going up, not monotone. -/
lemma δ_nonneg (D : Database α β) (m : Finset α) : 0 ≤ δ D m := Nat.zero_le _
