import Lean

-----  Lean as a Programming Language -----

--- 1. Basic Syntax ---

-- This is how you define a comment in Lean.

def foo (n : Nat) := n + 1

#check foo 1 -- The #check command gives the expr's type as a log message

-- Also, this works:
def foo' n := n + 1 -- Lean can auto infer the type of `n`


-- Type with \1, \->, \fun, \mapsto
def foo₁ : Nat → Nat := λ n ↦ n + 1
#check foo₁ 1

def foo₂ (n : Nat) (m : Nat) := n + m
#check foo₂ 5 -- Functions are curried: also try `#check foo₂`.

-- α is an implicit type variable
def twice {α : Type} (f : α → α) := λ x ↦ f (f x)

#reduce (twice foo) 1 -- `#reduce` evaluates the expression
-- Here `α` is `Nat`.
-- Also try: `#reduce twice foo 1`. Why does this work?

-- Exercise 1:

/-
Implement `log : Nat → Nat`, which accepts a
natural number and returns the number of times
it can be divided by 2 before it’d be < 1.
-/
def log (n : Nat) : Nat := sorry -- fill me in!

-- If you get a weird error about termination, put this after the function:
-- decreasing_by omega; omega

#reduce log 4 -- expected: 2
#reduce log 10 -- expected: 3

/-
Implement fact : Nat → Nat which computes
the factorial of a natural number.
-/
def fact (n : Nat) : Nat := sorry -- fill me in!

-- If you get a weird error about termination, put this after the function:
-- decreasing_by omega

#reduce fact 4 -- expected: 24
#reduce fact 5 -- expected: 120

/-
Implement rep : {α : Type} → (α → α) → Nat → α → α
that accepts a function f and a
natural number n and returns a
new function that applies f on its
argument n times.
**Do not use parentheses in your implementation**.
-/
def rep {α : Type} (f : α → α) (n : Nat): α → α := sorry

#reduce rep (λ x ↦ x + 1) 3 $ 0 -- expected: 3

--- 2. ADTs ---

inductive Nat' : Type
  | zero : Nat'
  | succ : Nat' → Nat'

#reduce (0 == Nat.zero, 1 == Nat.succ Nat.zero, 2 == (Nat.succ $ Nat.succ Nat.zero))

def add (n m : Nat) : Nat := match n with
  | Nat.zero => m
  | Nat.succ n' => Nat.succ (add n' m)

#reduce (add 0 3, add 3 0)

-- Note error because of non-termination:
def add' (n m : Nat) : Nat := match n with
  | Nat.zero => m
  | Nat.succ n' => Nat.succ (add' n m)

inductive List' (α : Type) : Type
  | nil : List' α
  | cons : α → List' α → List' α

#reduce List'.cons 42 $ List'.cons 69 $ List'.cons 613 $ List'.nil

#check [1, 2, 3] -- List literals
#reduce [1, 2, 3][0] -- Indexing into a list

-- The usual niceities are all there:
#check List.map -- Ignore the {u, v} for now

#check (List.map foo []) -- Put your cursor on the []

-- Exercise 2:
/-
Implement `Tree α`, the type of binary trees with
internal nodes having value of type α.
-/
inductive Tree (α : Type) : Type
  | fillme : Tree α -- Replace this with actual constructors

/-
Implement `treesum : Tree Nat → Nat` which
computes the sum of all values in the tree.
-/
def treesum (t : Tree Nat) : Nat := sorry

/-
Implement `reverse : {α : Type} → List α → List α`
which accepts a list and returns a reversed version.
-/
def reverse {α : Type} (l : List α) : List α := sorry

#reduce reverse [1, 2, 3] -- expected: [3, 2, 1]
#reduce reverse [] -- expected: []

--- 3. Props ---

#check (1 == 2, 1 = 2)
#check ∀ (n : Nat) m r k, k > 2 → (n^k + m^k ≠ r^k)

-- Exercise 3:
/-
Define `add_assoc : Prop` which
asserts that addition is associative.
-/
def add_assoc : Prop := sorry

/-
Define `tree_decomp : Prop` which asserts
that every tree is either a leaf node or
an internal node.
-/
def tree_decomp {α : Type} : Prop := sorry

/-
Define `reverse_reverse : Prop` which asserts
that applying reverse twice on the same list
gives the original list.
-/
def reverse_reverse {α : Type} : Prop := sorry
