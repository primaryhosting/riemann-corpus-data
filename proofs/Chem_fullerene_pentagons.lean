/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- **Fullerene pentagon count.**

Consider a polyhedron with `V` vertices, `E` edges and `F` faces which

* satisfies Euler's formula `V - E + F = 2` (stated additively as `V + F = E + 2`);
* is trivalent, i.e. every vertex lies on exactly three edges, so double counting
  vertex–edge incidences gives `3 * V = 2 * E`;
* has only pentagonal and hexagonal faces, say `p` pentagons and `h` hexagons, so
  `F = p + h`, and double counting edge–face incidences gives `5 * p + 6 * h = 2 * E`.

Then it has exactly `12` pentagonal faces — the combinatorial reason a fullerene
(e.g. C₆₀) always contains twelve five-membered rings. -/
theorem fullerene_pentagons
    (V E F p h : Nat)
    (euler : V + F = E + 2)
    (trivalent : 3 * V = 2 * E)
    (faces : F = p + h)
    (edge_face : 5 * p + 6 * h = 2 * E) :
    p = 12 := by
  omega

end Chem

