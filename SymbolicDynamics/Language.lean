
import Mathlib.Computability.Language

import SymbolicDynamics.ShiftSpace
import SymbolicDynamics.Blocks

variable {X Y: Type*}

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

def language_of_shift_space {A: Type*} (Λ: Set (Int → A)): Set (List A) :=
  {w: List A | ∃ (u: Λ) (i: Int), appears u (block_from_word w i)}
