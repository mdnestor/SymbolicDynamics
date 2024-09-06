

-- testing an alternative definition

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Finite

-- let x0 in X
-- call a set N a neighborhood of x0 wrt F if
-- forall u,v : X → Y, u|S = v|S → F(u)(x0) = F(v)(x0)

def neighborhood (F: (X → Y) → X → Y) (x: X) (S: Set X): Prop :=
  ∀ u v : X → Y, Set.EqOn u v S → F u x = F v x

def minimal_neighborhood (F: (X → Y) → X → Y) (x: X): Set X :=
  Set.sInter {S: Set X | neighborhood F x S}

-- why is this not in mathlib
theorem Set.eqOn_inter (u v: X → Y) (S1 S2: Set X) (h1: Set.EqOn u v S1): Set.EqOn u v (S1 ∩ S2) := by
  intro x h
  exact h1 h.1

def neighborhood_inter (F: (X → Y) → X → Y) (x: X) (S1 S2: Set X) (h1: neighborhood F x S1) (h2: neighborhood F x S2): neighborhood F x (S1 ∩ S2) := by
  intro u v h
  rw [neighborhood] at h1
  rw [neighborhood] at h2
  specialize h1 u v
  specialize h2 u v


theorem neighborhood_minimal_neighborhood (F: (X → Y) → X → Y) (x: X): neighborhood F x (minimal_neighborhood F x) := by
  intro u v h
  rw [minimal_neighborhood] at h
  sorry

def local_rule (F: (X → Y) → X → Y): Prop :=
  ∀ x: X, Finite (minimal_neighborhood F x)
