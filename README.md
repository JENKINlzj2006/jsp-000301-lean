# JSP-000301 Lean 4 formalization

Lean 4 formalization of Justin Sun Prize problem **JSP-000301** (consecutive powerful numbers; Golomb 1970 counterexample 12167/12168).

**Author:** Jenkin Lu (GitHub: [JENKINlzj2006](https://github.com/JENKINlzj2006))

Problem (catalog `problems/catalog-0301-0400.md#JSP-000301`): *If two consecutive positive
integers are powerful, must at least one be a perfect square?* — Answer **No**
(Golomb 1970: 12167 = 23³, 12168 = 2³·3²·13²).

Target theorems (`Jsp000301/Main.lean`):
- `JSP000301.jsp_000301` — exact statement of formal-conjectures `Erdos365.erdos_365.parts.i`
  (same `Nat.Full`/`Powerful` definition, restated locally).
- `JSP000301.jsp_000301_elem` — same with textbook definition (∀ p prime, p ∣ n → p² ∣ n).
- `JSP000301.jsp_000301_witness` — explicit witness form.

Reproduce:
```
lake build                      # Lean v4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
lake env lean Check.lean        # #print axioms → [propext, Classical.choice, Quot.sound]
lake env leanchecker Jsp000301.Main
```
Logs: `axioms.txt`, `leanchecker.log`.
