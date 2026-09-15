#!/usr/bin/env python3
"""Generate chained Lean replay modules for the q=9, r=5 LRAT trace."""

from pathlib import Path
import argparse


def parse_add(line):
    tok = line.split()
    if len(tok) < 2 or tok[1] == "d":
        return None
    try:
        j = tok.index("0", 1)
    except (ValueError, IndexError):
        return None
    return int(tok[0]), [int(x) for x in tok[1:j]]


def lean_int(x):
    return str(x) if x >= 0 else f"({x} : Int)"


def lean_seed(entries):
    rows = []
    for idx, (ident, lits) in enumerate(entries):
        vals = ", ".join(lean_int(x) for x in lits)
        chunk, index = divmod(idx, 64)
        rows.append(
            f"{{ id := {ident}, lits := #[{vals}], chunk := {chunk}, "
            f"index := {index}, size := {min(64, len(entries) - chunk * 64)} }}"
        )
    return "[" + ", ".join(rows) + "]" if rows else "[]"


def write_stage(path, stage, seg_path, seed, ids, previous, has_empty, chunk_size):
    prev_import = f"import Q9R5Stage{previous}\n" if previous is not None else ""
    prev_export = (
        f"q9_r5_stage{previous}_export"
        if previous is not None
        else "q9_r5_stage0_dummy_export"
    )
    export_name = f"q9_r5_stage{stage}_export"
    audit = (
        f"#print axioms q9_r5_stage{stage}"
        if has_empty
        else (f"#print axioms {export_name}.chunk0" if ids else "")
    )
    text = f'''import Q9PartitionInclusionR5
{prev_import}
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

namespace Erdos811Q9NoInfR5CNF

open Mathlib.Tactic.Sat

def q9_r5_stage{stage}_seed : List Mathlib.Tactic.Sat.SegmentSeed := {lean_seed(seed)}
def q9_r5_stage{stage}_export_ids : List Nat := [{", ".join(str(x) for x in ids)}]

lrat_proof_chunked_segment_with_partitioned_chunk_proofs_from_files q9_r5_stage{stage}
  "certificates/q9/q9_noinf_r5.cnf"
  "certificates/q9/stages_r5/q9_noinf_r5_stage{stage}.lrat"
  context q9_noinf_r5_ctx subsumes q9_full_partition
  ranges q9_r5_partition_ranges chunk_proofs q9_full_partition
  seed q9_r5_stage{stage}_seed proof_export {prev_export}
  export_ids q9_r5_stage{stage}_export_ids export {export_name} chunk_size {chunk_size}

{audit}

end Erdos811Q9NoInfR5CNF
'''
    path.write_text(text)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("proof", type=Path)
    ap.add_argument("out", type=Path)
    ap.add_argument("--additions", type=int, default=1000)
    ap.add_argument("--initial", type=int, default=96327)
    ap.add_argument("--chunk-size", type=int, default=1)
    args = ap.parse_args()
    if args.additions <= 0:
        raise ValueError("--additions must be positive")
    if args.initial < 0:
        raise ValueError("--initial must be nonnegative")
    if args.chunk_size <= 0:
        raise ValueError("--chunk-size must be positive")
    args.out.mkdir(parents=True, exist_ok=True)
    lines = args.proof.read_text().splitlines(keepends=True)
    first_record = next((line for line in lines if line.strip()), None)
    if first_record is None:
        raise ValueError("LRAT trace is empty")
    first_tokens = first_record.split()
    if len(first_tokens) < 2 or first_tokens[1] != "d":
        raise ValueError("expected the first LRAT record to delete the initial clause database")
    if int(first_tokens[0]) != args.initial:
        raise ValueError(
            f"--initial={args.initial} does not match first deletion id {first_tokens[0]}"
        )
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
            seg = lines[begin : idx + 1]
            has_empty = any(
                (a is not None and not a[1])
                for a in (parse_add(x) for x in seg)
            )
            segments.append((begin, idx + 1, dict(active), has_empty))
            begin = idx + 1
            adds = 0
    if begin < len(lines):
        seg = lines[begin:]
        has_empty = any(
            (a is not None and not a[1]) for a in (parse_add(x) for x in seg)
        )
        segments.append((begin, len(lines), dict(active), has_empty))

    previous = None
    previous_active = {}
    root = args.out.parent.parent.parent
    for stage, (lo, hi, live, has_empty) in enumerate(segments):
        seg_path = args.out / f"q9_noinf_r5_stage{stage}.lrat"
        seg_path.write_text("".join(lines[lo:hi]))
        derived = {k: v for k, v in previous_active.items() if k > args.initial}
        ids = sorted(k for k in live if k > args.initial)
        write_stage(
            root / f"Q9R5Stage{stage}.lean",
            stage,
            seg_path,
            sorted(derived.items()),
            ids,
            previous,
            has_empty,
            args.chunk_size,
        )
        previous = stage
        previous_active = live
    if not segments:
        raise ValueError("LRAT trace produced no replay segments")
    print(f"generated {len(segments)} r=5 stages under {args.out}")


if __name__ == "__main__":
    main()
