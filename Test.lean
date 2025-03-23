import Lean
syntax "test" : command

macro_rules
  | `(command| test) => `(#print "Works")

test -- If this is blue and shows a message on hover
     -- your setup is OK!
