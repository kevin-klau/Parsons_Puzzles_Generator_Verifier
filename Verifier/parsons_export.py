import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Union


def _as_fraction_lean(x: float, max_den: int = 1000) -> str:
    fr = Fraction(x).limit_denominator(max_den)
    return f"(({fr.numerator} : ℝ) / ({fr.denominator} : ℝ))"


def _c_to_lean(c: Union[int, float, str, Dict[str, Any]]) -> str:
    if isinstance(c, int):
        return f"({c} : ℝ)"
    if isinstance(c, float):
        return _as_fraction_lean(c)
    if isinstance(c, str):
        return c.strip()
    if isinstance(c, dict) and isinstance(c.get("lean"), str):
        return c["lean"].strip()
    raise ValueError(f"Unsupported constants.c format: {c!r}")


def _get_block_map(puzzle: Dict[str, Any]) -> Dict[str, Dict[str, Any]]:
    blocks = puzzle.get("blocks", [])
    if not isinstance(blocks, list):
        raise ValueError("puzzle.blocks must be a list")
    out: Dict[str, Dict[str, Any]] = {}
    for b in blocks:
        bid = str(b.get("id", "")).strip()
        if not bid:
            continue
        out[bid] = b
    return out


def render_question_text(puzzle: Dict[str, Any], show_constants: bool = False) -> str:
    prob = puzzle.get("problem", {})
    f_text = prob.get("f_text", "(missing f_text)")
    g_text = prob.get("g_text", "(missing g_text)")
    claim = prob.get("claim_text", "Prove f(n) is O(g(n))")
    domain = prob.get("domain_text", "")

    lines = []
    lines.append(f"Puzzle ID: {puzzle.get('puzzle_id','(no id)')}\n")
    lines.append("Question\n")
    lines.append("--------\n")
    lines.append(f"f(n) = {f_text}\n")
    lines.append(f"g(n) = {g_text}\n")
    lines.append(f"{claim} {domain}".strip() + "\n")

    if show_constants:
        consts = puzzle.get("constants", {})
        lines.append("\n(Given constants for verification)\n")
        lines.append(f"c = {consts.get('c')}\n")
        lines.append(f"n0 = {consts.get('n0')}\n")

    return "".join(lines)


def render_blocks_for_learners(
    puzzle: Dict[str, Any],
    include_kind: bool = False,
    shuffle_note: bool = True
) -> str:
    blocks = puzzle.get("blocks", [])
    lines: List[str] = []
    lines.append("Blocks (cut into cards and shuffle)\n")
    lines.append("---------------------------------\n")
    if shuffle_note:
        lines.append("(Note: some blocks may be distractors.)\n\n")

    for b in blocks:
        bid = str(b.get("id", "")).strip()
        text = str(b.get("text", "")).strip()
        kind = str(b.get("kind", "")).strip()

        if include_kind and kind:
            lines.append(f"[{bid}] ({kind}) {text}\n")
        else:
            lines.append(f"[{bid}] {text}\n")

    return "".join(lines)


def render_lean_from_order(
    puzzle: Dict[str, Any],
    order: List[str],
    theorem_name: str = "puzzle",
    auto_close: bool = True,
) -> str:
    lean = puzzle.get("lean", {})
    if not isinstance(lean, dict):
        raise ValueError("puzzle.lean must be an object")

    f_lean = str(lean.get("f", "")).strip()
    g_lean = str(lean.get("g", "")).strip()
    if not f_lean or not g_lean:
        raise ValueError("puzzle.lean.f and puzzle.lean.g must be non-empty strings")

    consts = puzzle.get("constants", {})
    if not isinstance(consts, dict):
        raise ValueError("puzzle.constants must be an object")

    c_lean = _c_to_lean(consts.get("c"))
    n0 = int(consts.get("n0"))

    block_map = _get_block_map(puzzle)

    stitched: List[str] = []
    for bid in order:
        if bid not in block_map:
            raise KeyError(f"Block id not found: {bid}")
        code = block_map[bid].get("lean", "")
        if not isinstance(code, str) or not code.strip():
            raise ValueError(f"Block {bid} missing non-empty 'lean' field")
        stitched.append(code.rstrip())
    
    if auto_close:
          all_code = "\n".join(stitched)
          already_has_close = "exact le_trans hsum h57_60" in all_code
          has_hsum = "hsum" in all_code
          has_h57 = "h57_60" in all_code
          if (not already_has_close) and has_hsum and has_h57:
               stitched.append("exact le_trans hsum h57_60")

    bigo_def = """def BigO (f g : ℕ → ℝ) : Prop :=
  ∃ c > (0:ℝ), ∃ n0 : ℕ, ∀ n ≥ n0, f n ≤ c * g n
"""

    out: List[str] = []
    out.append("import Mathlib\n\n")
    out.append(bigo_def)
    out.append("\nnamespace Parsons\n\n")
    out.append(f"def f : ℕ → ℝ := {f_lean}\n")
    out.append(f"def g : ℕ → ℝ := {g_lean}\n\n")
    out.append(f"theorem {theorem_name} : BigO f g := by\n")
    out.append(f"  refine ⟨{c_lean}, ?_, {n0}, ?_⟩\n")
    out.append("  · nlinarith\n")
    out.append("  · intro n hn\n")
    for block in stitched:
        for ln in block.splitlines():
            out.append(f"    {ln}\n")
    out.append("\nend Parsons\n")
    return "".join(out)





def get_default_order(puzzle: Dict[str, Any]) -> List[str]:
    # 1) Prefer an explicit correct_order if present
    co = puzzle.get("correct_order")
    if isinstance(co, list) and all(isinstance(x, (str, int)) for x in co):
        return [str(x) for x in co]

    # 2) Otherwise use all "step" blocks in file order
    blocks = puzzle.get("blocks", [])
    if isinstance(blocks, list):
        step_ids = [str(b.get("id")) for b in blocks if b.get("kind") == "step" and b.get("id") is not None]
        if step_ids:
            return step_ids

        # 3) Fallback: all blocks in file order
        all_ids = [str(b.get("id")) for b in blocks if b.get("id") is not None]
        if all_ids:
            return all_ids

    raise ValueError("No blocks found to form a default order.")

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", required=True, help="Path to single-puzzle JSON")

    # defaults: generate everything with one command
    ap.add_argument("--question-out", default="Question.txt", help="Write question text here")
    ap.add_argument("--blocks-out", default="Blocks.txt", help="Write learner blocks here")
    ap.add_argument("--lean-out", default="Main.lean", help="Write Lean code here")


    ap.add_argument("--include-kind", action="store_true", help="Include (step/distractor) in Blocks.txt")
    ap.add_argument("--show-constants", action="store_true", help="Include c and n0 in Question.txt")

    # order is OPTIONAL now
    ap.add_argument("--order", default="", help="Comma-separated block ids for a chosen solution order")
    ap.add_argument("--theorem-name", default="puzzle", help="Lean theorem name")

    args = ap.parse_args()

    puzzle = json.loads(Path(args.json).read_text(encoding="utf-8"))

    # 1) Question
    qtxt = render_question_text(puzzle, show_constants=args.show_constants)
    Path(args.question_out).write_text(qtxt, encoding="utf-8")

    # 2) Blocks (English)
    btxt = render_blocks_for_learners(puzzle, include_kind=args.include_kind)
    Path(args.blocks_out).write_text(btxt, encoding="utf-8")

    # 3) Lean (default order unless specified)
    if args.order.strip():
        order = [s.strip() for s in args.order.split(",") if s.strip()]
    else:
        order = get_default_order(puzzle)

    lean_src = render_lean_from_order(puzzle, order, theorem_name=args.theorem_name)
    Path(args.lean_out).write_text(lean_src, encoding="utf-8")

    print(f"Wrote {args.question_out}")
    print(f"Wrote {args.blocks_out}")
    print(f"Wrote {args.lean_out}")

if __name__ == "__main__":
    main()
