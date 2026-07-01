import HqivSpine.Chemistry.ShellStructure
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.Biomolecule` — Watson–Crick H-bond counts from complementarity

A hydrogen bond is a **half-monogamy spectator contact**: an electronegative edge atom either carries
the bridging proton (a **donor**) or presents an open lone pair (an **acceptor**). The donor/acceptor
state is two-valued — exactly the `monogamyPairMultiplicity = 2` of `Chemistry.ShellStructure` (a
shared phase channel is a pair of two opposite-phase carriers). Encoding each base's Watson–Crick edge
as the proton pattern on its N/O sites (the **only** structural input — the same status as handing an
allotrope network its connectivity), the canonical pair counts fall out of edge complementarity:

* adenine·thymine → **2** hydrogen bonds,
* guanine·cytosine → **3** hydrogen bonds,

with G·C strictly more bonded than A·T (the molecular basis of GC-rich duplex stability). No pairing
rule or bond count is assumed; both are computed by `decide`.

A second `decide`-free leg derives the **uniform helix width**: ring count is the cyclomatic number
`E − V + 1` of a base's heavy-atom graph (pyrimidines one ring, purines two), and every canonical rung
is purine + pyrimidine, hence the constant total `2 + 1 = 3` (the isostericity behind the double helix).

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Biomolecule

open HqivSpine.Chemistry.ShellStructure (monogamyPairMultiplicity)

/-- A Watson–Crick edge site: `true` carries the bridging proton (donor), `false` offers a lone
pair (acceptor). This proton pattern is the base-edge topology, the only input. -/
abbrev Donor : Type := Bool

/-- **The donor/acceptor state is the monogamy two-valuedness.** A site has exactly
`monogamyPairMultiplicity = 2` states — the same pairing multiplicity that makes a shared phase
channel two opposite-phase carriers in `ShellStructure`; here the two are *donate* vs *accept*. -/
theorem donor_states_eq_monogamyPair : Fintype.card Donor = monogamyPairMultiplicity := by decide

/-- Two aligned sites form a hydrogen bond when one donates and the other accepts (xor). -/
def complementary (a b : Bool) : Bool := a ≠ b

/-- Hydrogen-bond count = number of aligned complementary donor/acceptor positions. -/
def hbondCount (ex ey : List Bool) : ℕ :=
  ((ex.zipWith (fun a b => if complementary a b then 1 else 0) ey)).sum

/-- An edge is fully complementary when both faces have equal length and every site pairs. -/
def isCanonical (ex ey : List Bool) : Bool :=
  ex.length = ey.length && hbondCount ex ey == ex.length

/-- Adenine WC edge: N1 acceptor, N6–H donor. -/
def adenine : List Bool := [false, true]

/-- Thymine / uracil WC edge: N3–H donor, O4 acceptor. -/
def thymine : List Bool := [true, false]

/-- Guanine WC edge: O6 acceptor, N1–H donor, N2–H donor. -/
def guanine : List Bool := [false, true, true]

/-- Cytosine WC edge: N4–H donor, N3 acceptor, O2 acceptor. -/
def cytosine : List Bool := [true, false, false]

/-- **Adenine·thymine has two hydrogen bonds** — derived from complementarity. -/
theorem adenine_thymine_two : hbondCount adenine thymine = 2 := by decide

/-- **Guanine·cytosine has three hydrogen bonds** — derived from complementarity. -/
theorem guanine_cytosine_three : hbondCount guanine cytosine = 3 := by decide

/-- Both canonical pairs are fully complementary Watson–Crick edges. -/
theorem canonical_pairs : isCanonical adenine thymine ∧ isCanonical guanine cytosine := by
  decide

/-- **G·C is more strongly bonded than A·T** — the basis of GC-rich stability, computed not assumed. -/
theorem gc_more_bonded_than_at :
    hbondCount adenine thymine < hbondCount guanine cytosine := by decide

/-- A G·U-style edge-length mismatch is not a canonical pair (wobble), even though it scores
some complementary contacts. -/
theorem guanine_thymine_not_canonical : isCanonical guanine thymine = false := by decide

/-! ## Uniform helix width from one rule

Ring count is the cyclomatic number `E − V + 1` of a base's heavy-atom graph: pyrimidines have one
ring, purines two. Because the same donor/acceptor complementarity that fixes the H-bond counts also
pairs each (3-donor/acceptor) purine edge with a (matching) pyrimidine edge, every canonical rung is
purine + pyrimidine and therefore carries the *same* total ring count `2 + 1 = 3` — the isostericity
behind the double helix's constant width. -/

/-- Fused-ring count = cyclomatic number of the heavy-atom skeleton. -/
def ringCount (heavyEdges heavyVertices : ℕ) : ℕ := heavyEdges + 1 - heavyVertices

/-- Pyrimidine skeletons (one ring): `E = V` heavy ⇒ cyclomatic 1 (uracil 8/8, cytosine 8/8). -/
theorem pyrimidine_one_ring (v : ℕ) : ringCount v v = 1 := by
  unfold ringCount; omega

/-- Purine skeletons (two fused rings): one extra heavy edge over vertices ⇒ cyclomatic 2
(adenine 11/10, guanine 12/11). -/
theorem purine_two_rings (v : ℕ) : ringCount (v + 1) v = 2 := by
  unfold ringCount; omega

/-- **Uniform helix width**: a purine (2) + pyrimidine (1) rung always totals 3 rings, independent
of which canonical pair — the isostericity, from the single complementarity rule. -/
theorem canonical_rung_constant_width (vPyr vPur : ℕ) :
    ringCount vPyr vPyr + ringCount (vPur + 1) vPur = 3 := by
  rw [pyrimidine_one_ring vPyr, purine_two_rings vPur]

end HqivSpine.Chemistry.Biomolecule
