import Mathlib

set_option linter.style.openClassical false
open Classical

/-!
## Analogical Modeling — Core Data Structures

Formalizes the setup from Johnsen & Johansson (2005), §3.

An **exemplar** is a feature set paired with an outcome.
A **database** is a finite collection of exemplars.
The **lattice** L = ℘(τ) is the powerset of the test exemplar τ, ordered by ⊆.
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! ### Exemplars and Databases -/

/-- An exemplar: a set of features paired with an outcome. -/
structure Exemplar (α β : Type*) where
  features : Finset α
  outcome  : β
  deriving DecidableEq

/-- A database is a finite set of exemplars. -/
abbrev Database (α β : Type*) := Finset (Exemplar α β)

/-! ### The Lattice L -/

/-- The lattice L = ℘(τ): all possible feature subsets of the test exemplar.
    Ordered by ⊆, this is a Boolean algebra. -/
def lattice (τ : Finset α) : Finset (Finset α) := τ.powerset

@[simp]
lemma mem_lattice {τ m : Finset α} : m ∈ lattice τ ↔ m ⊆ τ :=
  Finset.mem_powerset

/-- The lattice is closed under intersection. -/
lemma lattice_inter_closed {τ : Finset α} {m n : Finset α}
    (hm : m ∈ lattice τ) (hn : n ∈ lattice τ) : m ∩ n ∈ lattice τ := by
  simp only [mem_lattice] at *
  exact Finset.inter_subset_left.trans hm

/-- Intersecting with τ maps any set into the lattice. -/
lemma inter_mem_lattice (τ s : Finset α) : τ ∩ s ∈ lattice τ := by
  simp [mem_lattice]
