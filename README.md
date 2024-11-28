# Predicate-and-First-Order-Tableaux

### Program to parse propositional and first-order logical formulae, and also prove their satisfiability using a tableau expansion method.

### we use a simplified language for both types of logic:

## Propositional Logic (FMLA)

**FMLA**:
- `PROP` (Proposition)
- `~FMLA` (Negation)
- `(FMLA * FMLA)` (Binary Connective)

**PROP**:
- `p | q | r | s`
- `* := /\ | \/ | =>` (and, or, implies)

---

## First-Order Logic (FOL)

We limit our variables to **x, y, z, w**, with no function symbols, and the only predicates are binary predicates **P, Q, R, S**.

**var**:
- `x | y | z | w`

**PRED**:
- `P | Q | R | S`

**FMLA**:
- `PRED(var, var)` (Atom)
- `~FMLA` (Negation)
- `EvarFMLA` (Existentially Quantified)
- `AvarFMLA` (Universally Quantified)
- `(FMLA * FMLA)` (Binary Connective)

**Connectives**:
- `* := /\ | \/ | =>` (and, or, implies)
