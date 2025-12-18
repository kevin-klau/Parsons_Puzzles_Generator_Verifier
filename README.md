# Parsons Big-O Puzzle Verifier (Lean4)

This repository generates Parsons puzzles for Big-O time complexity proofs and exports Lean4 code so you can verify a student’s block ordering inside this Lean project.

## Key idea

- Students see Verifier/Question.txt + Verifier/Blocks.txt (English blocks, shuffled).
- You take their chosen ordering of block IDs.
- The script exports Verifier/Main.lean containing a proof built from the corresponding Lean snippets.
- You open Main.lean in VS Code and Lean tells you whether it checks.

## Prerequisites

- Python 3.9+
- A working Lean4 + Mathlib Lake project (this repo already is one if Mathlib is configured correctly).

If you ever see:
- unknown module prefix 'Mathlib'

then Mathlib is not available in the current project. Confirm your lakefile.toml includes Mathlib and run the setup commands below.

## One-time setup (Lean/Mathlib)

From the repo root:

lake update
lake exe cache get
lake build

Then restart VS Code (or run Lean: Restart File).

Quick sanity check:
- Open any .lean file and confirm import Mathlib has no error.

## Puzzle format: Verifier/puzzle.json

Each puzzle JSON contains:
- a human-readable question (problem)
- Lean functions for f and g (lean)
- chosen constants c and n0 (constants)
- Parsons blocks (blocks), where each block has:
  - text: English block (student-facing)
  - lean: Lean snippet (verifier-facing, pasteable after intro n hn)

Minimal schema:

{
  "puzzle_id": "P1",
  "problem": {
    "f_text": "5n^2 + 12n + 40",
    "g_text": "n^2",
    "claim_text": "Prove f(n) is O(g(n))",
    "domain_text": "for all n ≥ 1"
  },
  "lean": {
    "f": "fun n => (5:ℝ) * ((n:ℝ)^2) + (12:ℝ) * (n:ℝ) + 40",
    "g": "fun n => ((n:ℝ)^2)"
  },
  "constants": { "c": 60, "n0": 1 },
  "blocks": [
    {
      "id": "B1",
      "kind": "step",
      "text": "Convert n ≥ 1 to 1 ≤ n.",
      "lean": "have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn"
    }
  ]
}

## Generate printable question + blocks

This writes/overwrites:
- Verifier/Question.txt
- Verifier/Blocks.txt

Run:

python Verifier/parsons_export.py --json Verifier/puzzle.json --question-out Verifier/Question.txt --blocks-out Verifier/Blocks.txt

Print or share those two files with students.

## Export Lean proof from a student’s block order

When a student gives you an ordering (example):
B1,B2,B5,B3,B4,B7,B8

Generate Lean code:

python Verifier/parsons_export.py --json Verifier/puzzle.json --order B1,B2,B5,B3,B4,B7,B8 --lean-out Verifier/Main.lean

Now open Verifier/Main.lean in VS Code.
- If Lean shows no errors and the file reaches No goals, the ordering is correct.
- If Lean errors, the ordering is wrong (or a block’s Lean snippet doesn’t match its English step).

## Common issues

1) unknown module prefix 'Mathlib'
Run:
lake update
lake exe cache get
lake build

Make sure you’re opening the repo root folder in VS Code (the folder containing lakefile.toml).

2) Missing final chaining line (le_trans)
Some proofs need a final chain like:
exact le_trans hsum h57_60

If you standardize naming in your blocks (hsum, h57_60), include this as the final “step” block.

## Where to edit what

- Edit the puzzle content: Verifier/puzzle.json
- Run the exporter: Verifier/parsons_export.py
- Outputs:
  - Verifier/Question.txt
  - Verifier/Blocks.txt
  - Verifier/Main.lean

## Suggested workflow

1) Put a new puzzle into Verifier/puzzle.json
2) Generate Question.txt + Blocks.txt
3) Students solve the Parsons puzzle (provide a block ID order)
4) Export Main.lean for that order
5) Check correctness in VS Code via Lean
