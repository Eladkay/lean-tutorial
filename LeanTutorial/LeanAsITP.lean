import Lean
import Aesop

-----  Lean as an Interactive Theorem Prover -----

--- 1. CIC ---

def myProp : Prop := 1 = 2
#check myProp

def myProof : 1 = 1 := rfl
#check myProof

def myProof : 1 = 1 := rfl
def noProof : 1 = 2 := sorry -- `sorry` is an escape hatch

def even n := ∃ m, n = 2 * m
def myProp₂ : ∀ n, ¬(even n) → n > 0 := sorry

def myProp₃ : 1 = 1 ∧ 2 = 2 := And.intro rfl rfl

def myProp₄ : 1 = 1 ∨ 2 = 1 := Or.inl rfl

def fermat : ∀ (n : Nat) m r k, k > 2 → (n^k + m^k ≠ r^k) := sorry

--- 2. Theorem Proving ---

-- Use your cursor to browse through the example
example : ∀ n, 0 + n = n := by {
  intro n
  induction n with
  | zero => rfl
  | succ k ih => {
    rw [← Nat.add_assoc]
    rw [ih]
  }
}

theorem zero_add : ∀ n, 0 + n = n := by {
  intro n
  induction n with
  | zero => rfl
  | succ k ih => {
    rw [← Nat.add_assoc]
    rw [ih]
  }
}
#check zero_add

--- Exercise 4:

inductive Tree (α : Type) : Type
  | nil : Tree α
  | cons : α → Tree α → Tree α → Tree α

def reverse {α : Type} (l : List α): List α := match l with
  | List.nil => List.nil
  | List.cons a l' => reverse l' ++ [a]

theorem add_assoc : ∀ (a b c : Nat), a + (b + c) = (a + b) + c := by {
  sorry
}
theorem tree_decomp {α : Type} : ∀ t : Tree α, t = Tree.nil ∨ ∃ a l r, (t = Tree.cons a l r) := by {
  sorry
}

---

theorem zero_add' : ∀ n, 0 + n = n := by aesop
