import CountUnionFamilyPowersetsProof.AM.Functions

set_option linter.style.openClassical false
open Classical

/-!
## Analogical Modeling — Homogeneity and the Analogical Set

Formalizes homogeneity, deterministic homogeneity, and the analogical set A,
following Johnsen & Johansson (2005), §3.

Key objects:
- `IsHomogeneous τ D m`                — m has non-empty support and δ is constant
                                          on all supersets with non-empty support
- `IsDeterministicallyHomogeneous τ D m` — homogeneous with δ = 0 (all agree on outcome)
- `analogicalSet τ D`                  — A: the set of all homogeneous elements of L
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! ### Homogeneity -/

/-- m ∈ L is **homogeneous** if:
    1. σ(m) is non-empty, and
    2. every n ∈ L with m ⊆ n and σ(n) non-empty satisfies δ(n) = δ(m).

    Intuitively: moving from m to any more specific pattern in the same "homogeneous
    region" doesn't change the disagreement count. -/
def IsHomogeneous (τ : Finset α) (D : Database α β) (m : Finset α) : Prop :=
  (σ D m).Nonempty ∧
  ∀ n ∈ lattice τ, m ⊆ n → (σ D n).Nonempty → δ D n = δ D m

/-- m is **deterministically homogeneous** if it is homogeneous with δ = 0:
    all exemplars in the support agree on outcome. -/
def IsDeterministicallyHomogeneous (τ : Finset α) (D : Database α β) (m : Finset α) : Prop :=
  IsHomogeneous τ D m ∧ δ D m = 0

lemma isHomogeneous_nonempty {τ : Finset α} {D : Database α β} {m : Finset α}
    (h : IsHomogeneous τ D m) : (σ D m).Nonempty :=
  h.1

lemma isHomogeneous_δ_const {τ : Finset α} {D : Database α β} {m n : Finset α}
    (hm : IsHomogeneous τ D m) (hn : n ∈ lattice τ) (hmn : m ⊆ n) (hne : (σ D n).Nonempty) :
    δ D n = δ D m :=
  hm.2 n hn hmn hne

/-- A deterministically homogeneous pattern has empty support disagreement. -/
lemma isDetermHomogeneous_δ_zero {τ : Finset α} {D : Database α β} {m : Finset α}
    (h : IsDeterministicallyHomogeneous τ D m) : δ D m = 0 :=
  h.2

/-- All exemplars in the support of a deterministically homogeneous pattern agree on outcome. -/
lemma isDetermHomogeneous_agree {τ : Finset α} {D : Database α β} {m : Finset α}
    (h : IsDeterministicallyHomogeneous τ D m) :
    ∀ r ∈ σ D m, ∀ s ∈ σ D m, r.outcome = s.outcome :=
  δ_eq_zero_iff.mp h.2

/-! ### The Analogical Set A -/

/-- The **analogical set** A ⊆ L: all homogeneous elements of the lattice L = ℘(τ). -/
noncomputable def analogicalSet (τ : Finset α) (D : Database α β) : Finset (Finset α) :=
  τ.powerset.filter (IsHomogeneous τ D)

@[simp]
lemma mem_analogicalSet {τ : Finset α} {D : Database α β} {m : Finset α} :
    m ∈ analogicalSet τ D ↔ m ⊆ τ ∧ IsHomogeneous τ D m := by
  simp [analogicalSet, Finset.mem_filter, Finset.mem_powerset]

/-- Every element of the analogical set lies in the lattice L. -/
lemma analogicalSet_subset_lattice (τ : Finset α) (D : Database α β) :
    analogicalSet τ D ⊆ lattice τ :=
  Finset.filter_subset _ _

/-! ### Monotonicity of Homogeneity -/

/-- If m is homogeneous and n ∈ L with m ⊆ n and non-empty support,
    then δ(n) = δ(m) — the disagreement is constant going up within the
    homogeneous region. -/
lemma homogeneous_δ_eq_of_superset {τ : Finset α} {D : Database α β} {m n : Finset α}
    (hm : IsHomogeneous τ D m) (hn_lat : n ∈ lattice τ) (hmn : m ⊆ n)
    (hne : (σ D n).Nonempty) : δ D n = δ D m :=
  hm.2 n hn_lat hmn hne

/-! ### Key Structural Lemma -/

/-- If m is homogeneous and m ⊆ n ⊆ τ, and σ(n) is non-empty,
    then n is also homogeneous (with the same δ value). -/
lemma isHomogeneous_of_superset {τ : Finset α} {D : Database α β} {m n : Finset α}
    (hm : IsHomogeneous τ D m) (hn_lat : n ∈ lattice τ) (hmn : m ⊆ n)
    (hne : (σ D n).Nonempty) : IsHomogeneous τ D n := by
  constructor
  · exact hne
  · intro k hk_lat hnk hkne
    have hmk : m ⊆ k := hmn.trans hnk
    rw [hm.2 k hk_lat hmk hkne, hm.2 n hn_lat hmn hne]
