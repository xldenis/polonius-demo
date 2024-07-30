Todo:

1. A more precise join, the current join erases so much information its impossible to see if a borrow is used in two separate loops.
  - The issue is that we need a value to act as the fixpoint of a series of symbolic values in loops.
2. Infer loop invariants
