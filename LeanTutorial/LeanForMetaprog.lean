import Lean
import Lean.Parser
open Lean Elab Command Term Meta Lean.Parser Lean.Core Syntax

-----  Lean as a Framework for Metaprogramming -----

syntax "solve_world_hunger" : command
-- solve_world_hunger -- If you uncomment this, it will give an error.

elab "solve_world_hunger" : command =>
  logInfo "Open McDonalds in Africa"

solve_world_hunger

syntax "plus_one" term : term
elab "plus_one" t:term : term => do
  let newTerm ← `($t + 1)
  elabTerm newTerm none

#reduce plus_one 1

declare_syntax_cat funkyop

syntax ("@" <|> "#" <|> ";") : funkyop
syntax term funkyop term : term
elab t₁:term f:funkyop t₂:term : term => do
  let term ← match f with
  | `(funkyop|@) => `($t₁ $t₂)
  | `(funkyop|#) => `($t₁ + $t₂)
  | `(funkyop|;) => `($t₁ * $t₂)
  | _ => unreachable!
  elabTerm term none

#check 1 # 2

-- Exercise 5:

inductive Tree (α : Type) : Type
  | nil : Tree α
  | cons : α → Tree α → Tree α → Tree α

/-
Implement a new syntax for trees:
`leaf` will denote a leaf.
A binary tree node will be denoted as such: `tree l : v : r`
where `l` and `r` are the left and right subtrees
and `v` is the node value.
-/


-- #reduce tree (tree leaf : 3 : leaf) : 2 : (tree leaf : 5 : leaf)
