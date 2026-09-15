#!/usr/bin/env python3
"""Split a q=9 LRAT trace into module-sized segments.

Each boundary is after a complete LRAT record.  The generated Lean source
imports the preceding stage, seeds the live derived clauses from its export
theorem, and exports the next live set.  This is intentionally deterministic:
IDs are sorted in the conjunction order and the original trace is never
overwritten.
"""

from pathlib import Path
import argparse


def parse_add(line):
    tok = line.split()
    if len(tok) >= 2 and tok[1] != "d":
        try:
            j = tok.index("0", 1)
            return int(tok[0]), [int(x) for x in tok[1:j]]
        except (ValueError, IndexError):
            pass
    return None


def parse_refs(line):
    """Return LRAT clause ids used by an addition record.

    An addition has two zero-terminated fields: literals, then proof hints.
    Only the second field is relevant when deciding which clauses must be
    imported from the preceding stage.  Keeping this dependency set minimal
    avoids exporting/rehydrating unrelated live clauses at every checkpoint.
    """
    tok = line.split()
    if len(tok) < 2 or tok[1] == "d":
        return []
    try:
        first = tok.index("0", 1)
        second = tok.index("0", first + 1)
    except (ValueError, IndexError):
        return []
    return [int(x) for x in tok[first + 1:second]]


def lean_int(x):
    return str(x) if x >= 0 else f"({x} : Int)"


def lean_seed(entries, export_order=None):
    if not entries:
        return "[]"
    if export_order is None:
        export_order = [ident for ident, _lits in entries]
    positions = {ident: idx for idx, ident in enumerate(export_order)}
    rows = []
    for ident, lits in entries:
        vals = ", ".join(lean_int(x) for x in lits)
        idx = positions[ident]
        chunk, index = divmod(idx, 64)
        rows.append(f"{{ id := {ident}, lits := #[{vals}], chunk := {chunk}, index := {index}, size := {min(64, len(export_order) - chunk * 64)} }}")
    return "[" + ", ".join(rows) + "]"


def write_stage_source(path, stage, seg_path, seed, ids, previous, previous_export_order, has_empty, chunk_size):
    seed_name = f"q9_r4_stage{stage}_seed"
    ids_name = f"q9_r4_stage{stage}_export_ids"
    export_name = f"q9_r4_stage{stage}_export"
    prev_import = f"import Q9R4Stage{previous}\n" if previous is not None else ""
    prev_export = f"q9_r4_stage{previous}_export" if previous is not None else "q9_r4_stage0_dummy_export"
    seed_text = lean_seed(seed, previous_export_order)
    ids_text = "[" + ", ".join(str(x) for x in ids) + "]"
    audit = f"#print axioms q9_r4_stage{stage}" if has_empty else (f"#print axioms {export_name}.chunk0" if ids else "")
    text = f'''import Q9PartitionInclusionR4
{prev_import}
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

namespace Erdos811Q9NoInfR4CNF

open Mathlib.Tactic.Sat

def {seed_name} : List Mathlib.Tactic.Sat.SegmentSeed := {seed_text}
def {ids_name} : List Nat := {ids_text}

lrat_proof_chunked_segment_with_partitioned_chunk_proofs_from_files q9_r4_stage{stage}
  "certificates/q9/q9_noinf_r4.cnf"
  "certificates/q9/stages/{seg_path.name}"
  context q9_noinf_r4_ctx subsumes q9_full_partition
  ranges q9_r4_partition_ranges chunk_proofs q9_full_partition
  seed {seed_name} proof_export {prev_export}
  export_ids {ids_name} export {export_name} chunk_size {chunk_size}

{audit}

end Erdos811Q9NoInfR4CNF
'''
    path.write_text(text)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("proof", type=Path)
    ap.add_argument("out", type=Path)
    ap.add_argument("--additions", type=int, default=1000)
    ap.add_argument("--initial", type=int, default=96219)
    ap.add_argument("--stages", type=int, default=1)
    ap.add_argument("--chunk-size", type=int, default=100)
    ap.add_argument(
        "--from-stage",
        type=int,
        default=0,
        help="recompute state through this stage but only rewrite its suffix",
    )
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    lines = args.proof.read_text().splitlines(keepends=True)
    active = {}
    segments = []
    begin = 0
    adds = 0
    for idx, line in enumerate(lines):
        add = parse_add(line)
        if add is not None:
            active[add[0]] = add[1]
            adds += 1
        elif line.split()[1:2] == ["d"]:
            for x in line.split()[2:]:
                if x == "0":
                    break
                active.pop(int(x), None)
        if adds >= args.additions:
            segment_lines = lines[begin:idx + 1]
            has_empty = any((a is not None and not a[1]) for a in (parse_add(x) for x in segment_lines))
            segments.append((begin, idx + 1, dict(active), has_empty))
            begin = idx + 1
            adds = 0
            if len(segments) >= args.stages:
                break
    if begin < len(lines) and len(segments) < args.stages:
        segment_lines = lines[begin:]
        has_empty = any((a is not None and not a[1]) for a in (parse_add(x) for x in segment_lines))
        segments.append((begin, len(lines), dict(active), has_empty))
    previous = None
    previous_active = {}
    previous_export_order = None
    for stage, (lo, hi, live, has_empty) in enumerate(segments):
        if stage < args.from_stage:
            previous = stage
            previous_active = live
            # Existing prefix sources were generated with all live clauses in
            # their export list.  Preserve that order as the projection map
            # when the sparse suffix starts at a later stage.
            previous_export_order = sorted(k for k in live if k > args.initial)
            continue
        seg_path = args.out / f"q9_noinf_r4_stage{stage}.lrat"
        seg_path.write_text("".join(lines[lo:hi]))
        segment_refs = {
            ref
            for line in lines[lo:hi]
            for ref in parse_refs(line)
        }
        if has_empty or stage + 1 >= len(segments):
            ids = []
        else:
            # Keep a carried clause available until its *next use*, not just
            # for the immediately following segment.  A proof may leave an
            # old clause untouched for several segments and then cite it;
            # exporting only next-segment references would drop it at the
            # intermediate boundary and make the later seed impossible.
            future_refs = {
                ref
                for _future_lo, _future_hi, _future_live, _future_empty in segments[stage + 1:]
                for line in lines[_future_lo:_future_hi]
                for ref in parse_refs(line)
            }
            ids = sorted(k for k in live if k > args.initial and k in future_refs)
        # A live clause that is untouched in this segment still has to be
        # available if it is exported for the next segment.  Include those
        # carry-through IDs together with clauses directly referenced by the
        # current proof; this is the minimal seed closed under replay/export.
        required = set(segment_refs)
        required.update(ids)
        derived = {
            k: v
            for k, v in previous_active.items()
            if k > args.initial and k in required
        }
        src = args.out.parent.parent.parent / f"Q9R4Stage{stage}.lean"
        write_stage_source(
            src, stage, seg_path, sorted(derived.items()), ids, previous,
            previous_export_order, has_empty, args.chunk_size,
        )
        previous = stage
        previous_active = live
        previous_export_order = ids
    print(f"generated {len(segments)} stage(s) under {args.out}")


if __name__ == "__main__":
    main()
