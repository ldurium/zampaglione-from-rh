# What follows from the Riemann Hypothesis for the objects of F. Zampaglione

Author: Fortunato Zampaglione (Milan). 22 November 2026.

One Lean 4 file, `ZampaglioneFromRH.lean`: 17 theorems, each of the form

    RiemannHypothesis → (statement about one of the author's objects)

where `RiemannHypothesis` is Mathlib's statement. Given any proof `h : RiemannHypothesis`,
every theorem becomes unconditional by applying it to `h`.

| Theorem | Object (author's date) | Statement on every nontrivial zero ρ = β + iγ |
|---|---|---|
| `orbital_im`, `orbital_re`, `orbital_ge_quarter` | orbital coordinate q = ρ(1−ρ) (30 Jan 2026) | q is real, q = 1/4 + γ², q ≥ 1/4 |
| `reality_equation` | equation of reality (9 Feb 2026) | γ(1 − 2β) = 0 |
| `anchor_sq`, `zero_from_anchor` | anchors (15 Jul – 16 Oct 2026) | A² = (q − 1/4)/200 ≥ 0 and \|γ\| = √0.5 · 20 · A |
| `halving_fixed`, `halving_deviation` | halving (5 Jan 2026; 10.5281/zenodo.18604067) | H(β) = β, β − 1/2 = 0 |
| `reflection_eq_conj` | the two symmetries (1 Sep 2026) | 1 − ρ = conj ρ |
| `pythagoras_defect` | irrotational angle (23 Oct 2026) | \|1 − y\|² − (1 + \|y\|²) = 0, y = 2(ρ − 1/2) |
| `sphere_equator` | sphere (1 Nov 2026) | \|ρ\|² = \|1 − ρ\|² |
| `quartic_defect` | quartic sector (22 Aug 2026) | 8(β − 1/2)²γ² = 0 |
| `discriminant_real` | chart of the zero (22 Jul 2026) | (2ρ − 1)² = −4γ² |
| `logit_zero` | logit invariant (20 Aug 2026) | log(β/(1 − β)) = 0 |
| `lyapunov_exponent` | Lyapunov detector (10.5281/zenodo.24195450) | −β = −1/2 |
| `gate_pole_pos` | gate | pole contribution y/(y² + (x − γ)²) > 0 for y > 0 |

Verification: Lean 4.36.0 with Mathlib, exit code 0, no `sorry`; each theorem depends only on
`propext`, `Classical.choice`, `Quot.sound` (see `compile_log_lean_4.36.0.txt`).

SHA-256 of `ZampaglioneFromRH.lean`: 506b573c7c1af4d8808120b1b8ab72ce89dda004afa2e0d52bad358db6175e85

Related deposit: 10.5281/zenodo.24431336 (402 machine-checked statements, files under embargo).

© 2026 Fortunato Zampaglione. All rights reserved.
