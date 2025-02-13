import Veil

/-! # Lamport's Bakery algorithm

This file formalises [Lamport's Bakery
algorithm](http://lamport.azurewebsites.net/pubs/bakery.pdf) for mutual
exclusion. This algorithm, unlike other solutions, has the advantage
that it continues to operate correctly despite the failure of any
individual component.

References:
- [A New Solution of Dijkstra's Concurrent Programming Problem](https://lamport.azurewebsites.net/pubs/bakery.pdf)
- [Towards an Automatic Proof of the Bakery Algorithm](https://members.loria.fr/SMerz/papers/2023-forte.html)
- https://github.com/aman-goel/BakeryProtocol
- https://github.com/tlaplus/Examples/tree/master/specifications/Bakery-Boulangerie


## Problem statement

Consider `N` asynchronous computers communicating with each other only
via shared memory. Each computer runs a looping program with two parts:
a **critical section** and a _non-critical section_. A problem posed by
Dijkstra (and extended by Knuth) is to write the programs run by the
`N` computers such that the following conditions are satisfied:

1. At any time, at most one computer may be in its critical section.
2. Each computer must eventually be able to enter its critical section
(unless it halts).
3. Any computer may halt in its non-critical section.

## Setting

`N` processors, each with its own memory. A processor may _read_ from
any other processor's memory, but it need only write into its own
memory.

No assumptions can be made about the running speeds of the computers.

A processor may fail at any time. When it fails, it immediately goes to
its noncritical section and halts. There may then be a period when
reading from its memory gives arbitrary values. Eventually, any read
from its memory must give a value of zero.

## Properties

The algorithm has the remarkable property that if a read and write
operation to a single memory location occur simultaneously, then only
the write operation must be performed correctly. The read may return
_any_ arbitrary value!

Moreover, the algorithm is _first-come-first-served_ in the following
sense: when a processor wants to enter its critical section, it first
executes a loop-free bkock of code--i.e. one with a fixed number of
execution steps. It is then guaranteed to enter its critical section
before any other processor which later requests service.

-/

veil module Bakery
type processor
type ticket

instantiate oP : TotalOrder processor
instantiate oT : TotalOrderWithMinimum ticket
open TotalOrder TotalOrderWithMinimum

/- `flag[i]` is in the memory of processor `i`. It is `True` when
processor `i` is entering the critical section. In the bakery analogy,
this is called `choosing` and is `True` when the customer is talking
with the baker to decide what to buy (only one customer can talk to the
baker at any one point). -/
function choosing : processor → Prop

/- `number[i]` is in the memory of processor `i`. When customers enter
the bakery, they pick up a queue number. Whilst in real life, they
would pick all pick different numbers, in a computer two different
processors might read the same value from memory (before it manages to
get incremented). If two processors read the same value, the processor
with the LOWEST processor ID gets priority. -/
function number : processor → ticket

/-
See https://github.com/aman-goel/BakeryProtocol/blob/main/Bakery/Bakery.tla
for a PlusCal specification that includes explicitly modelled failures.

```
variables choosing[i ∈ P ↦ False], number[i ∈ P ↦ 0]
process self ∈ P
    variables unread = {}, max = 0;
p1: while true:
      choosing[self] := True;
      unread := P \ { self } ; max := 0;
p2:   # computes max(number[1], ..., number[N]);
      for nxt ∈ unread:
         if number[nxt] > max then max := number[nxt];
         unread := unread \ { nxt };
p3:   number[self] := max + 1;
p4:   unread := P \ { self }; choosing[self] := False;
p5:   for nxt ∈ unread:
          await ¬ choosing[nxt];
p6:       await (num[nxt] = 0) ∨ ((num[self] < num[nxt]) ∨ (num[self] = num[nxt] ∧ self <= next))
          unread := unread \ { nxt };
cs:   enter critical section
p7:   num[self] := 0
ncs:  non-critical section
```
-/

relation unread (self : processor) (nxt : processor)
function max (self : processor) : ticket
/- For p5 await -/
relation awaited (self : processor) (nxt : processor)

relation pc_p1 (P:processor)
relation pc_p2 (P:processor)
relation pc_p3 (P:processor)
relation pc_p4 (P:processor)
relation pc_p5 (P:processor)
relation pc_p6 (P:processor)
relation pc_cs (P:processor)
relation pc_p7 (P:processor)

#gen_state

trusted invariant (pc_p1 P) ∨ (pc_p2 P) ∨ (pc_p3 P) ∨ (pc_p4 P) ∨ (pc_p5 P) ∨ (pc_p6 P) ∨ (pc_cs P) ∨ (pc_p7 P)
trusted invariant pc_p1 P  -> (             ¬pc_p2 P  ∧ ¬pc_p3 P  ∧ ¬pc_p4 P  ∧ ¬pc_p5 P  ∧ ¬pc_p6 P  ∧ ¬pc_cs P  ∧ ¬pc_p7 P  )
trusted invariant pc_p2 P  -> ( ¬pc_p1 P  ∧             ¬pc_p3 P  ∧ ¬pc_p4 P  ∧ ¬pc_p5 P  ∧ ¬pc_p6 P  ∧ ¬pc_cs P  ∧ ¬pc_p7 P  )
trusted invariant pc_p3 P  -> ( ¬pc_p1 P  ∧ ¬pc_p2 P  ∧             ¬pc_p4 P  ∧ ¬pc_p5 P  ∧ ¬pc_p6 P  ∧ ¬pc_cs P  ∧ ¬pc_p7 P  )
trusted invariant pc_p4 P  -> ( ¬pc_p1 P  ∧ ¬pc_p2 P  ∧ ¬pc_p3 P  ∧             ¬pc_p5 P  ∧ ¬pc_p6 P  ∧ ¬pc_cs P  ∧ ¬pc_p7 P  )
trusted invariant pc_p5 P  -> ( ¬pc_p1 P  ∧ ¬pc_p2 P  ∧ ¬pc_p3 P  ∧ ¬pc_p4 P  ∧             ¬pc_p6 P  ∧ ¬pc_cs P  ∧ ¬pc_p7 P  )
trusted invariant pc_p6 P  -> ( ¬pc_p1 P  ∧ ¬pc_p2 P  ∧ ¬pc_p3 P  ∧ ¬pc_p4 P  ∧ ¬pc_p5 P  ∧             ¬pc_cs P  ∧ ¬pc_p7 P  )
trusted invariant pc_cs P  -> ( ¬pc_p1 P  ∧ ¬pc_p2 P  ∧ ¬pc_p3 P  ∧ ¬pc_p4 P  ∧ ¬pc_p5 P  ∧ ¬pc_p6 P  ∧             ¬pc_p7 P  )
trusted invariant pc_p7 P  -> ( ¬pc_p1 P  ∧ ¬pc_p2 P  ∧ ¬pc_p3 P  ∧ ¬pc_p4 P  ∧ ¬pc_p5 P  ∧ ¬pc_p6 P  ∧ ¬pc_cs P              )

ghost relation ll (i j : processor) :=
  -- number j > number i OR (number i = number j AND i <= j)
   ¬ (le (number j) (number i)) ∨ (number i = number j ∧ le i j)

/-
```
variables choosing[i ∈ P ↦ False], number[i ∈ P ↦ 0]
```
-/
after_init {
  choosing I := False
  number I := zero
  pc_p1 I := True
  pc_p2 I := False
  pc_p3 I := False
  pc_p4 I := False
  pc_p5 I := False
  pc_p6 I := False
  pc_cs I := False
  pc_p7 I := False
}

/-
```
process self ∈ P
    variables unread = {}, max = 0;
p1: while true:
      choosing[self] := True;
      unread := P \ { self } ; max := 0;
```
-/

action exec_p1 (self : processor) = {
  require pc_p1 self
  choosing self := True
  unread self P := if P = self then False else True
  max self := zero
  pc_p1 self := False; pc_p2 self := True
}

#print exec_p1.tr

action p1_fail (self : processor) = {
  require pc_p1 self
  -- GEORGE: why do they model failure as flipping `choosing` rather than setting it to `False`?
  choosing self := ¬ choosing self
}

/-
```
p2:   # computes max(number[1], ..., number[N]);
      for nxt ∈ unread:
         if number[nxt] > max then max := number[nxt];
         unread := unread \ { nxt };
```
-/

action exec_p2_loop (self : processor) (nxt : processor) = {
  require pc_p2 self
  require unread self nxt
  if ¬ (le (number nxt) (max self)) then
    max self := number nxt
  unread self nxt := False
}

action exec_p2_end_loop (self : processor) = {
  require pc_p2 self
  require ∀ nxt, ¬ unread self nxt
  pc_p2 self := False; pc_p3 self := True
}

/-
```
p3:   number[self] := max + 1;
```
-/

action exec_p3 (self : processor) = {
  require pc_p3 self
  let next_number ← fresh ticket
  -- Some specifications only require that `next_number` is `>` max, but
  -- here we require that it is the successor (i.e. `max + 1`).
  require next (max self) next_number
  number self := next_number
  pc_p3 self := False; pc_p4 self := True
}

action p3_fail (self : processor) (shouldRepeat : Prop) = {
  require pc_p3 self
  require shouldRepeat
  let k ← fresh ticket
  number self := k
}
/-
```
p4:   unread := P \ { self }; choosing[self] := False;
```
-/

action exec_p4 (self : processor) = {
  require pc_p4 self
  unread self P := if P = self then False else True
  choosing self := False
  pc_p4 self := False; pc_p5 self := True
}

action p4_fail (self : processor) = {
  require pc_p4 self
  unread self P := if P = self then False else True
  choosing self := ¬ choosing self
}

/-
```
p5:   for nxt ∈ unread:
          await ¬ choosing[nxt];
p6:       await (num[nxt] = 0) ∨ ((num[self] < num[nxt]) ∨ (num[self] = num[nxt] ∧ self <= next))
          unread := unread \ { nxt };
cs:   enter critical section
```
-/

action exec_p5_loop (self : processor) (nxt : processor) = {
  require pc_p5 self
  require unread self nxt
  require ¬ choosing nxt
  awaited self P := if P = nxt then True else False
  pc_p5 self := False; pc_p6 self := True

}

action exec_p5_exit_loop (self : processor) = {
  require pc_p5 self
  require ∀ nxt, ¬ unread self nxt
  pc_p5 self := False; pc_cs self := True
}

action exec_p6 (self : processor) (nxt : processor) = {
  require pc_p6 self
  require awaited self nxt
  require number nxt = zero ∨ ll self nxt
  unread self nxt := False
  pc_p6 self := False; pc_p5 self := True
}

action exec_cs (self : processor) = {
  require pc_cs self = True
  pc_cs self := False; pc_p7 self := True
}

/-
```
p7:   num[self] := 0
ncs:  non-critical section
```
-/

action exec_p7 (self : processor) = {
  require pc_p7 self
  number self := zero
  pc_p7 self := False; pc_p1 self := True
}

action p7_fail (self : processor) (shouldRepeat : Prop) = {
  require pc_p7 self
  require shouldRepeat
  let k ← fresh ticket
  number self := k
}

safety [mutual_exclusion] ∀ pi pj, (pi ≠ pj) → ¬ (pc_cs pi ∧ pc_cs pj)

invariant [ic3po_global1_11] forall P1 , number P1 = zero -> ¬pc_p4 P1
invariant [ic3po_other3] forall P1 , number P1 = zero -> ¬pc_p5 P1
invariant [ic3po_other4] forall P1 , number P1 = zero -> ¬pc_p6 P1
invariant [ic3po_other2] forall P1 , pc_cs P1 -> ¬ number P1 = zero

invariant [ic3po_global1_23] (forall P1 , (pc_p2 P1 -> choosing P1))
invariant [ic3po_other1] (forall P1 , (pc_p3 P1 -> choosing P1))

invariant [ic3po_other24] forall P1 P2 , pc_p5 P2 ∧ choosing P1 ∧ pc_p5 P1 -> P2 = P1 ∨ unread P2 P1
invariant [ic3po_other20] forall P1 P2 , pc_p6 P2 ∧ choosing P1 ∧ pc_p5 P1 -> unread P2 P1
invariant [ic3po_other26] forall P1 P2 , pc_p6 P2 -> choosing P1 -> awaited P2 P1 -> ¬pc_p5 P1
invariant [ic3po_other28] forall P1 P2 , pc_p6 P2 ∧ choosing P1 ∧ awaited P2 P1 ∧ pc_p6 P1 -> P2 = P1
invariant [ic3po_other30] forall P1 P2 P3 , choosing P3 ∧ awaited P2 P1 ∧ pc_cs P2 ∧ pc_p5 P3 -> P3 = P1 ∨ P1 = P2
invariant [ic3po_other21] forall P1 P2 , pc_p6 P1 ∧ pc_p5 P2 ∧ choosing P1 -> unread P2 P1
invariant [ic3po_other25] forall P1 P2 , pc_p6 P2 ∧ pc_p6 P1 ∧ choosing P1 -> P2 = P1 ∨ unread P2 P1
invariant [ic3po_other31] forall P1 P2 P3 , choosing P3 ∧ awaited P2 P1 ∧ pc_cs P2 ∧ pc_p6 P3 -> P3 = P1 ∨ P1 = P2

invariant [ic3po_other27] forall P1 P2 , pc_p6 P2 ∧ pc_p2 P1 ∧ awaited P2 P1 -> unread P1 P2 ∨ le (number P2) (max P1)
invariant [ic3po_other29] forall P1 P2 , pc_p6 P2 ∧ pc_p3 P1 ∧ awaited P2 P1 ∧ choosing P1 -> le (number P2) (max P1)

invariant [ic3po_other22] forall P1 P2 , pc_p5 P2 ∧ pc_p2 P1 -> unread P2 P1 ∨ le (number P2) (max P1) ∨ unread P1 P2
invariant [ic3po_other18] forall P1 P2 , pc_p5 P1 ∧ pc_p3 P2 -> unread P1 P2 ∨ le (number P1) (max P2)
invariant [ic3po_other11] forall P1 P2 , pc_p5 P1 ∧ pc_p4 P2 -> ll P1 P2 ∨ unread P1 P2
invariant [ic3po_other15] forall P1 P2 , pc_p5 P2 ∧ pc_p5 P1 -> ll P1 P2 ∨ unread P1 P2
invariant [ic3po_other14] forall P1 P2 , pc_p6 P2 ∧ pc_p5 P1 -> ll P1 P2 ∨ unread P1 P2
invariant [ic3po_other23] forall P1 P2 , pc_p6 P2 ∧ pc_p2 P1 -> unread P1 P2 ∨ le (number P2) (max P1) ∨ unread P2 P1
invariant [ic3po_other19] forall P1 P2 , pc_p3 P2 ∧ pc_p6 P1 -> unread P1 P2 ∨ le (number P1) (max P2)
invariant [ic3po_other12] forall P1 P2 , pc_p6 P1 ∧ pc_p4 P2 -> ll P1 P2 ∨ unread P1 P2
invariant [ic3po_other13] forall P1 P2 , pc_p6 P1 ∧ pc_p5 P2 -> unread P1 P2 ∨ ll P1 P2
invariant [ic3po_other16] forall P1 P2 , pc_p6 P1 ∧ pc_p6 P2 -> unread P1 P2 ∨ ll P1 P2

invariant [ic3po_other17] forall P1 P2 , pc_cs P1 ∧ pc_p2 P2 -> unread P2 P1 ∨ le (number P1) (max P2)
invariant [ic3po_other8] forall P1 P2 , pc_p3 P2 ∧ pc_cs P1 -> le (number P1) (max P2)
invariant [ic3po_other5] forall P1 P2 , pc_cs P2 ∧ pc_p4 P1 -> ll P2 P1
invariant [ic3po_other6] forall P1 P2 , pc_cs P2 ∧ pc_p5 P1 -> ll P2 P1
invariant [ic3po_other9] forall P1 P2 , pc_p5 P2 ∧ pc_cs P1 -> unread P2 P1
invariant [ic3po_other7] forall P1 P2 , pc_cs P2 ∧ pc_p6 P1 -> ll P2 P1
invariant [ic3po_other10] forall P1 P2 , pc_p6 P2 ∧ pc_cs P1 -> unread P2 P1

#gen_spec

set_option trace.profiler true
set_option veil.smt.solver "cvc5"

-- #check_action exec_p1
-- #check_action p1_fail
-- #check_action exec_p2_loop
-- #check_action exec_p2_end_loop
-- #check_action exec_p3
-- #check_action p3_fail
-- #check_action exec_p4
-- #check_action p4_fail
-- #check_action exec_p5_loop
-- #check_action exec_p5_exit_loop
-- #check_action exec_p6
-- #check_action exec_cs
-- #check_action exec_p7
-- #check_action p7_fail

-- #check_invariants

#exit

set_option maxHeartbeats 100000000

unsat trace [cannot_immediately_enter_cs] {
  any action
  exec_cs
} by bmc


sat trace [can_eventually_enter_cs] {
  any 5 actions
  exec_cs
} by bmc_sat

sat trace {
  exec_p1
  exec_p2_end_loop
} by bmc_sat

set_option veil.smt.solver "cvc5"
sat trace {
  exec_p1
  exec_p2_loop
  exec_p2_loop
  exec_p2_end_loop
  exec_p3
  exec_p4
  exec_p5_loop
  exec_p6
} by bmc_sat


end Bakery
