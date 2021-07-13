Coq proofs on RPDS-to-PDS
==========================

Formal proofs on a transformation of a register pushdown system (RPDS) A
into a pushdown system (PDS) bisimulation equivalent to A.
The proofs were constructed using the [Coq](https://coq.inria.fr)
proof assistant.

- You can see the definitions and the statements of theorems
  in [pds.html](https://ytakata69.github.io/rpds-to-pds-proof/pds.html)
  and other HTML files linked from it.
- If you like to inspect the proofs, see the `.v` files in this repository.
  - `equiv.v` - The definition of register assignments and equivalence
                relations.
  - `stack.v` - The definition of stack manipulations in RPDS and PDS.
  - `pds.v`   - The definition of state transitions in RPDS A and PDS A',
                and the main theorem which shows the bisimulation equivalence
                between A and A'.
