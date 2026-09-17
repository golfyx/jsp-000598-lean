# JSP-000598: central binomials with the same prime divisors

Lean 4 formalization of the catalog yes/no question

> Can two distinct central binomial coefficients have exactly the same prime divisors?

as recorded in [The Justin Sun Prize](https://github.com/TheJustinSunPrize/awards) entry [JSP-000598](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000598).

The answer, as the catalog is currently worded, is **yes**. This repository machine-checks the pair

\[
\binom{174}{87}, \qquad \binom{176}{88}
\]

i.e. indices `n = 87` and `m = 88`. The two binomial coefficients are distinct 52-digit integers, and they have exactly the same prime divisors

\[
\{2,3,5,7,11,13,19,23,31,47,53,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173\}.
\]

A catalog-correction thread notes that Erdős problem #730 asks for **infinitely many** such pairs. Infinitude is out of scope. This development answers only the catalog sentence. It does not claim mathematical discovery or first-formalization priority.

## Theorems

| Name | Statement |
| --- | --- |
| `JSP000598.witness_87_88` | `C(174,87)` and `C(176,88)` have the same prime divisors |
| `JSP000598.jsp_000598` | existence of distinct indices with that property |
| `JSP000598.question_true` | the catalog existence question holds |

The binomial coefficients are defined by the integral product formula `Π_{i<k}(n-i)/(i+1)`, then matched to explicit prime-power factorizations by kernel `decide` (not `native_decide`). Euclid's lemma is proved from the core `Nat.gcd` library, as in the JSP-000301 development.

## Toolchain

- Lean `v4.34.0`
- **No Mathlib, Batteries, or other packages**
- No `sorry`, `admit`, `native_decide`, or project-declared axioms

```sh
lake build
lake env lean Audit.lean
```

## Attribution and priority

Formalization by [@golfyx](https://github.com/golfyx), with AI assistance (Cursor Grok 4.6). Solver credit remains with the catalog citations, including Erdős–Graham–Ruzsa–Straus and the later GPT Pro / Liam Price solution of the infinitude form. Observation issue #116 already records the `(87,88)` witness; this submission is a complete Mathlib-free kernel check of the existential catalog wording.

## License

Apache-2.0.
