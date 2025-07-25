import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Graph.Basic

open Finset

namespace Graph

variable {α β : Type*} {x y : α} {e : β}

section VertexFinset

variable {G : Graph α β} [Fintype G.vertexSet]

/--The `vertexSet` of the graph as a `Finset`.-/
abbrev vertexFinset : Finset α := Set.toFinset G.vertexSet

@[norm_cast]
theorem coe_vertexFinset : (G.vertexFinset : Set α) = G.vertexSet := Set.coe_toFinset _

theorem mem_vertexFinset : x ∈ G.vertexFinset ↔ x ∈ G.vertexSet := Set.mem_toFinset

end VertexFinset

section FiniteAt

variable {G : Graph α β}

/-- `G.incSet x` is the set of edges incident to `x` in `G`. -/
def incSet (x : α) : Set β := {e | G.Inc e x}

/-- `G.loopSet x` is the set of loops based at `x` in `G`. -/
def loopSet (x : α) : Set β := {e | G.IsLoopAt e x}

theorem Loop.inc_mem (h : e ∈ G.loopSet x) : e ∈ G.incSet x := by use x; exact h

variable (x : α) [Fintype (G.incSet x)]

/-- `G.incFinset x` is the `Finset` version of `G.incSet x` in case `G` is
locally finite at `x`. -/
def incFinset : Finset β := (G.incSet x).toFinset

theorem incFinset_def : G.incFinset x = (G.incSet x).toFinset := rfl

@[simp]
theorem mem_incFinset (e : β) : e ∈ G.incFinset x ↔ G.Inc e x := Set.mem_toFinset

variable (x : α) [Fintype (G.loopSet x)]

/-- We define `G.loopFinset x` to be the `Finset` version of `G.loopSet x`.-/
def loopFinset : Finset β := (G.loopSet x).toFinset

theorem loopFinset_def : G.loopFinset x = (G.loopSet x).toFinset := rfl

@[simp]
theorem mem_loopFinset (e : β) : e ∈ G.loopFinset x ↔ G.IsLoopAt e x := Set.mem_toFinset

variable (x : α)

/-theorem loopFinset_of_incFinset {x : α} : Fintype (G.incSet x) → Fintype (G.loopSet x) := by sorry-/

variable (x : α) [Fintype (G.incSet x)]
/-- `G.degree x` is the number of edges incident to `x`, counting loops twice. -/
def degree : ℕ := #(G.incFinset x) + #(G.loopFinset x)


end FiniteAt
