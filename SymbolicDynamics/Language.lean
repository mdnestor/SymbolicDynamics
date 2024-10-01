

import Mathlib.Computability.Language


import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite
import Mathlib.Algebra.Group.Defs

import SymbolicDynamics.ProdiscreteTopology
import SymbolicDynamics.ShiftSpace
import SymbolicDynamics.Blocks

import Mathlib.Order.Interval.Basic

variable {X Y: Type*}

-- given a shift space on A^Z extract its set of strings


-- given a function word w: List A and an index i: Int
-- form the block whose set is {i, i+1,...i+n}
-- and whose block map is {w[i], w[i+1],...,w[i+n]
#check NonemptyInterval.mk

def interval (a b: Int): Set Int := {x | a ≤ x ∧ x < b}

def block_from_word {A: Type*} (w: List A) (i: Int): Block Int A :=
  ⟨
    interval i (i + w.length),
    by
      intro ⟨x, hx1, hx2⟩
      let n_fin: Fin w.length := {
        val := (x - i).toNat
        isLt := sorry
      }
      exact w.get n_fin
  ⟩

#check Set.restrict
def language_of_shift_space {A: Type*} (Λ: Set (Int → A)): Set (List A) :=
  {w: List A | ∃ (u: Λ) (i j: Int), appears u (block_from_word w i)}
