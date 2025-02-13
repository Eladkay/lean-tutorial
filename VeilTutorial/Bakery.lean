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

class ProgramCounterValue (t : Type) where
  p1 : t
  p2 : t
  p3 : t
  p4 : t
  p5 : t
  p6 : t
  cs : t
  p7 : t

  -- axioms
  pcv_all_different :
    (p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p1 ≠ p5 ∧ p1 ≠ p6 ∧ p1 ≠ cs ∧ p1 ≠ p7) ∧
    (p2 ≠ p3 ∧ p2 ≠ p4 ∧ p2 ≠ p5 ∧ p2 ≠ p6 ∧ p2 ≠ cs ∧ p2 ≠ p7) ∧
    (p3 ≠ p4 ∧ p3 ≠ p5 ∧ p3 ≠ p6 ∧ p3 ≠ cs ∧ p3 ≠ p7) ∧
    (p4 ≠ p5 ∧ p4 ≠ p6 ∧ p4 ≠ cs ∧ p4 ≠ p7) ∧
    (p5 ≠ p6 ∧ p5 ≠ cs ∧ p5 ≠ p7) ∧
    (p6 ≠ cs ∧ p6 ≠ p7) ∧
    (cs ≠ p7)

  pcv_exhaustive :
    ∀ PC, PC = p1 ∨ PC = p2 ∨ PC = p3 ∨ PC = p4 ∨ PC = p5 ∨ PC = p6 ∨ PC = cs ∨ PC = p7
open ProgramCounterValue

type pcv
instantiate pc_value : ProgramCounterValue pcv
function pc : processor → pcv

#gen_state

ghost relation ticketLt (i j : processor) :=
   le (number i) (number j) ∨ (number i = number j ∧ le i j)

/-
```
variables choosing[i ∈ P ↦ False], number[i ∈ P ↦ 0]
```
-/
after_init {
  choosing I := False
  number I := zero
  pc I := p1
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
  require pc self = p1
  choosing self := True
  unread self P := if P = self then False else True
  max self := zero
  pc self := p2
}

#print exec_p1.tr

action p1_fail (self : processor) = {
  require pc self = p1
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
  require pc self = p2
  require unread self nxt
  if ¬ (le (number nxt) (max self)) then
    max self := number nxt
  unread self nxt := False
}

action exec_p2_end_loop (self : processor) = {
  require pc self = p2
  require ∀ nxt, ¬ unread self nxt
  pc self := p3
}

/-
```
p3:   number[self] := max + 1;
```
-/

action exec_p3 (self : processor) = {
  require pc self = p3
  let next_number ← fresh ticket
  -- Some specifications only require that `next_number` is `>` max, but
  -- here we require that it is the successor (i.e. `max + 1`).
  require next (max self) next_number
  number self := next_number
  pc self := p4
}

action p3_fail (self : processor) (shouldRepeat : Prop) = {
  require pc self = p3
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
  require pc self = p4
  unread self P := if P = self then False else True
  choosing self := False
  pc self := p5
}

action p4_fail (self : processor) = {
  require pc self = p4
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
  require pc self = p5
  require unread self nxt
  require ¬ choosing nxt
  awaited self P := if P = nxt then True else False
  pc self := p6

}

action exec_p5_exit_loop (self : processor) = {
  require pc self = p5
  require ∀ nxt, ¬ unread self nxt
  pc self := cs
}

action exec_p6 (self : processor) (nxt : processor) = {
  require pc self = p6
  require awaited self nxt
  require number nxt = zero ∨ ticketLt self nxt
  unread self nxt := False
  pc self := p5
}

action exec_cs (self : processor) = {
  require pc self = cs
  pc self := p7
}

/-
```
p7:   num[self] := 0
ncs:  non-critical section
```
-/

action exec_p7 (self : processor) = {
  require pc self = p7
  number self := zero
  pc self := p1
}

action p7_fail (self : processor) (shouldRepeat : Prop) = {
  require pc self = p7
  require shouldRepeat
  let k ← fresh ticket
  number self := k
}

invariant [mutual_exclusion] ∀ pi pj, (pi ≠ pj) → ¬ (pc pi = cs ∧ pc pj = cs)

#gen_spec

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

set_option veil.smt.solver "cvc5" in
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


set_option veil.smt.model.minimize true
set_option veil.printCounterexamples true

#check_invariants_tr

end Bakery
