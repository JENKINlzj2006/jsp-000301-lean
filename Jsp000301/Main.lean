/-
JSP-000301 — "If two consecutive positive integers are powerful, must at least one be a
perfect square?"  (Erdős Problem #365, first question.)

Answer: **No**.  Counterexample due to S. W. Golomb, *Powerful numbers*,
Amer. Math. Monthly 77 (1970), 848–852:
  12167 = 23³  and  12168 = 2³ · 3² · 13²
are consecutive, both powerful, and neither is a perfect square
(110² = 12100 < 12167 < 12168 < 12321 = 111²).

Formalization: Jenkin Lu (qiqi), written independently.
Toolchain: Lean 4 v4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/
import Mathlib

namespace JSP000301

/-! ## Definitions

`Full k n` / `Powerful n` agree verbatim with the definitions used in
google-deepmind/formal-conjectures (`FormalConjecturesForMathlib/Data/Nat/Full.lean`),
so that the main theorem below is literally the statement `erdos_365.parts.i`
of that project.  We also prove the statement for the textbook definition
(`PowerfulElem`) and show the two definitions coincide for positive `n`. -/

/-- `n` is `k`-full if `p ^ k ∣ n` for every prime factor `p` of `n`. -/
def Full (k n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- A powerful (square-full) number. -/
abbrev Powerful : ℕ → Prop := Full 2

/-- Textbook definition: every prime dividing `n` divides it at least twice. -/
def PowerfulElem (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

theorem powerful_iff_elem {n : ℕ} (hn : 0 < n) : Powerful n ↔ PowerfulElem n := by
  constructor
  · intro h p hp hpn
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩)
  · intro h p hp
    obtain ⟨hp, hpn, -⟩ := Nat.mem_primeFactors.mp hp
    exact h p hp hpn

/-! ## The two numbers -/

lemma prime_23 : Nat.Prime 23 := by norm_num
lemma prime_13 : Nat.Prime 13 := by norm_num

lemma factor_a : (12167 : ℕ) = 23 ^ 3 := by norm_num
lemma factor_b : (12168 : ℕ) = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num

lemma primeFactors_a : (12167 : ℕ).primeFactors = {23} := by
  rw [factor_a, Nat.primeFactors_prime_pow (by norm_num) prime_23]

lemma primeFactors_b : (12168 : ℕ).primeFactors = {2, 3, 13} := by
  rw [factor_b, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three,
    Nat.primeFactors_prime_pow (by norm_num) prime_13]
  decide

lemma powerful_a : Powerful 12167 := by
  intro p hp
  rw [primeFactors_a, Finset.mem_singleton] at hp
  subst hp
  norm_num

lemma powerful_b : Powerful 12168 := by
  intro p hp
  rw [primeFactors_b] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

/-- No integer strictly between `110²` and `111²` is a perfect square. -/
lemma not_isSquare_of_between {n : ℕ} (h1 : 110 ^ 2 < n) (h2 : n < 111 ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  have hr1 : 110 < r := by
    by_contra h
    push Not at h
    have : r * r ≤ 110 * 110 := Nat.mul_le_mul h h
    omega
  have hr2 : r < 111 := by
    by_contra h
    push Not at h
    have : 111 * 111 ≤ r * r := Nat.mul_le_mul h h
    omega
  omega

lemma not_square_a : ¬ IsSquare (12167 : ℕ) :=
  not_isSquare_of_between (by norm_num) (by norm_num)

lemma not_square_b : ¬ IsSquare (12168 : ℕ) :=
  not_isSquare_of_between (by norm_num) (by norm_num)

/-! ## Main results -/

/-- **JSP-000301 / Erdős #365 (i)**, in the exact form of
`formal-conjectures` `Erdos365.erdos_365.parts.i`: it is *not* true that whenever
`n > 0` and `n`, `n+1` are both powerful, one of them is a perfect square. -/
theorem jsp_000301 :
    ¬ ∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  rcases h 12167 (by norm_num) powerful_a powerful_b with hs | hs
  · exact not_square_a hs
  · exact not_square_b hs

/-- Same statement with the textbook definition of powerful number. -/
theorem jsp_000301_elem :
    ¬ ∀ n : ℕ, 0 < n → PowerfulElem n → PowerfulElem (n + 1) →
      IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  apply jsp_000301
  intro n hn ha hb
  exact h n hn ((powerful_iff_elem hn).mp ha) ((powerful_iff_elem (Nat.succ_pos n)).mp hb)

/-- Explicit witness form: there exist two consecutive positive powerful integers,
neither of which is a perfect square. -/
theorem jsp_000301_witness :
    ∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) :=
  ⟨12167, by norm_num, powerful_a, powerful_b, not_square_a, not_square_b⟩

end JSP000301
