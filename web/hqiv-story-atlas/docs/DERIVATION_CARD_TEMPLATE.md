# HQIV Story Atlas - Derivation Card Design Template

This document defines the standard format for every chapter card in the physics-first site.

Goal: teach the physics derivation to high school / college readers first, while preserving formal provenance to Lean.

---

## 1) Audience and tone

- Primary reader: mathematically curious high school and undergraduate physics learners.
- Secondary reader: advanced learners who want formal traceability.
- Tone rule: explain the current idea now; do not lead with downstream dependencies.
- Avoid "glossary dump" intros. Start with a short teaching paragraph, then show equation.
- Keep language precise, not condescending.

---

## 2) Card anatomy (required sections)

Every card must use this exact structure and order.

1. `Title`
   - Format: `Chapter n - <topic>`
2. `Teaching description` (2-4 sentences)
   - Explain what this chapter establishes in plain physics language.
   - Do not describe where it goes next in the first paragraph.
3. `Core equation` (KaTeX block)
   - One canonical equation per card minimum.
4. `Equation phrase` (one sentence)
   - Natural-language reading of the equation using English names for symbols/operators.
5. `Interactive terms` (symbol chips + hover/click)
   - Each symbol/operator in equation maps to one term definition.
6. `Derivation steps` (2-8 steps)
   - Short step title, one math line, one explanation sentence.
7. `Canvas element(s)` (at least 1)
   - Visual that teaches the concept, not just decoration.
8. `Lean provenance` (collapsed by default)
   - Lean file path, theorem/definition link, optional source anchor.

---

## 3) Symbol interaction standard (global CSS/behavior)

All symbols/operators shown in equations use one common interaction class system so behavior is consistent across all cards.

- Use a standard class:
  - `.sym` for any interactive symbol token
  - `.sym-op` for operators (`forall`, `in`, `=>`, etc.)
  - `.sym-var` for variables (`m`, `T(m)`, `phi(m)`)
- On hover/focus:
  - show short English name
  - show one-line meaning
  - show "first introduced in" link
- On click:
  - pin the panel (keyboard and touch friendly)

Required metadata for each token:

```ts
type SymbolDef = {
  key: string;                 // unique, e.g. "forall", "m", "T(m)"
  latex: string;               // token latex
  english: string;             // e.g. "for all", "belongs to"
  meaning: string;             // contextual meaning in this card
  firstIntroducedCardId: string;
  firstIntroducedAnchor: string; // id to scroll to
};
```

---

## 4) Operator English mapping (baseline)

These must always have English names in hover text:

- `\forall` -> "for all"
- `\in` -> "belongs to"
- `\mathbb{N}` -> "natural numbers"
- `=` -> "equals"
- `>` -> "is greater than"
- `\le` -> "is less than or equal to"
- `\Rightarrow` -> "implies"

This directly addresses cases like:

`forall m in N`

which should read:

"For all shells `m` belonging to the natural numbers."

---

## 5) Intro paragraph rules

Do:

- explain the current physical object
- define only what is needed now
- defer advanced objects until earned

Do not:

- open with theorem plumbing or dependency chains
- introduce symbols that are not used in the current equation
- include term tags below equation unless they are interactive and useful

Note: the old static tags (example: `light cone`, `phi ladder`, `reference shell`) are redundant if term interactions already exist. Remove or repurpose them as interactive anchors only.

---

## 6) Canvas requirement

Each card has at least one canvas section.

Canvas types:

- `diagram`: geometry/causal sketch
- `balance`: equation-side balance visualization
- `trajectory`: shell progression or sequence
- `field`: vector/flow conceptual plot

For Chapter 1, use `diagram`:

- 2D spacetime axes (space x, time t)
- origin event at (0,0)
- lightcone boundaries at +-45 degrees
- shell markers for `m = 0..4`
- optional annotation `T(m) = 1/(m+1)` near shell markers

---

## 7) Provenance model

Lean links remain present but secondary.

- Show provenance in a collapsed "Formal source" section by default.
- Include:
  - Lean file path
  - theorem/def name
  - optional remote link when configured

Example:

- File: `Hqiv/Story/Chapter01_Foundation.lean`
- Theorem: `step01_lightConeAuxiliarySubstrate_holds`

---

## 8) Chapter 1 reference implementation (rewritten)

Use this as the model for initial cards.

### Title

`Chapter 1 - Light Cone and Shell Ladder`

### Teaching description

In this chapter, we define the shell ladder that the rest of the model uses.  
Each shell is indexed by a whole number `m`, and each shell gets a positive temperature value.  
This gives us a clean starting point: every shell is physically valid, so later dynamics are built on a consistent base.

### Core equation

`\forall m \in \mathbb{N}: T(m)=\frac{1}{m+1}>0`

### Equation phrase

For all shells `m` belonging to the natural numbers, the shell temperature is `1/(m+1)`, which is always positive.

### Interactive terms (minimum)

- `\forall`: for all
- `m`: shell index
- `\in`: belongs to
- `\mathbb{N}`: natural numbers
- `T(m)`: shell temperature at index `m`
- `1/(m+1)`: reciprocal ladder step formula
- `>`: is greater than
- `0`: positive baseline

### Derivation steps

1) Define shell index domain  
`m \in \mathbb{N}`  
Shells are counted by whole numbers starting at 0.

2) Define shell temperature  
`T(m)=\frac{1}{m+1}`  
Each step up in `m` gives a smaller positive value.

3) Prove positivity  
`m \ge 0 \Rightarrow m+1>0 \Rightarrow T(m)>0`  
The denominator is always positive, so the temperature is always positive.

### Canvas

`diagram.lightcone-shell-ladder-v1`  
(2D spacetime lightcone with shell markers and reciprocal labels)

### Formal source (collapsed)

- `Hqiv/Story/Chapter01_Foundation.lean`
- `step01_lightConeAuxiliarySubstrate`
- `step01_lightConeAuxiliarySubstrate_holds`

---

## 9) Build checklist for each new card

- [ ] Teaching description explains current chapter only
- [ ] At least one KaTeX equation
- [ ] Equation phrase in English
- [ ] Every symbol/operator has hover definition
- [ ] Every symbol links to first-introduced anchor
- [ ] At least one canvas element
- [ ] Lean provenance included and collapsed
- [ ] No orphan tags below equation

---

## 10) Immediate implementation plan

1. Replace current free-form "tags" row with symbol interaction only.
2. Add `SymbolDef` registry and shared hover component.
3. Add per-card `equationPhrase` field.
4. Add per-card `canvasSpec` field and first Chapter 1 lightcone canvas.
5. Move Lean provenance into collapsed section.

