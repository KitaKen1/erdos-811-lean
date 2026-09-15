#!/usr/bin/env python3
"""Audit generated q=9 LRAT segments without invoking Lean.

The staged Lean files carry a seed (the live derived clauses at the start of
the segment) and an export-id list (the live derived clauses at its end).  This
script independently streams the original LRAT trace, checks that the stage
files are an exact byte-for-byte partition, and compares those two boundary
lists—including clause literals—with the replay state computed from the trace.
It is deliberately a source/certificate audit only; it does not establish the
LRAT inference rule, which remains the job of the Lean kernel replay.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class Family:
    name: str
    stage_prefix: str
    stage_dir: str
    original: str
    initial_id: int
    expected_stages: int


FAMILIES = {
    "r4": Family("r4", "Q9R4Stage", "stages", "q9_noinf_r4.lrat", 96219, 198),
    "r5": Family("r5", "Q9R5Stage", "stages_r5", "q9_noinf_r5.lrat", 96327, 128),
}


def sha256_file(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
            size += len(chunk)
    return digest.hexdigest(), size


def parse_addition(line: str) -> tuple[int, list[int]] | None:
    tokens = line.split()
    if len(tokens) < 2 or tokens[1] == "d":
        return None
    try:
        ident = int(tokens[0])
        end = tokens.index("0", 1)
    except (ValueError, IndexError):
        return None
    try:
        lits = [int(token) for token in tokens[1:end]]
    except ValueError:
        return None
    return ident, lits


def apply_line(line: str, active: dict[int, tuple[int, ...]]) -> None:
    addition = parse_addition(line)
    if addition is not None:
        ident, lits = addition
        active[ident] = tuple(lits)
        return
    tokens = line.split()
    if len(tokens) < 2 or tokens[1] != "d":
        return
    for token in tokens[2:]:
        if token == "0":
            break
        try:
            active.pop(int(token), None)
        except ValueError:
            raise ValueError(f"invalid deletion token {token!r} in LRAT line")


def parse_source(path: Path, family: Family, stage: int) -> tuple[list[tuple[int, tuple[int, ...]]], list[int], str]:
    text = path.read_text()
    base = f"q9_{family.name}"
    seed_name = f"{base}_stage{stage}_seed"
    ids_name = f"{base}_stage{stage}_export_ids"

    seed_match = re.search(
        rf"def {re.escape(seed_name)}\b.*?:=\s*(.*?)\n"
        rf"def {re.escape(ids_name)}\b",
        text,
        re.DOTALL,
    )
    if seed_match is None:
        raise ValueError(f"{path}: missing seed definition")
    seed_text = seed_match.group(1)
    seed: list[tuple[int, tuple[int, ...]]] = []
    for match in re.finditer(r"\{\s*id\s*:=\s*(\d+)\s*,\s*lits\s*:=\s*#\[([^]]*)\]", seed_text):
        ident = int(match.group(1))
        lits = tuple(int(token) for token in re.findall(r"-?\d+", match.group(2)))
        seed.append((ident, lits))
    if seed_text.strip() != "[]" and not seed:
        raise ValueError(f"{path}: seed text was nonempty but no entries parsed")

    ids_match = re.search(
        rf"def {re.escape(ids_name)}\b.*?:=\s*\[([^]]*)\]",
        text,
        re.DOTALL,
    )
    if ids_match is None:
        raise ValueError(f"{path}: missing export-id definition")
    export_ids = [int(token) for token in re.findall(r"\d+", ids_match.group(1))]

    segment_match = re.search(
        rf"certificates/q9/{re.escape(family.stage_dir)}/"
        rf"q9_noinf_{re.escape(family.name)}_stage{stage}\.lrat",
        text,
    )
    if segment_match is None:
        raise ValueError(f"{path}: source does not reference its stage LRAT segment")
    return seed, export_ids, segment_match.group(0)


def audit_family(lean_dir: Path, cert_dir: Path, family: Family, last: int | None, check_olean: bool) -> None:
    stage_dir = cert_dir / family.stage_dir
    original = cert_dir / family.original
    if not original.is_file():
        raise FileNotFoundError(original)

    discovered = sorted(
        (int(match.group(1)), path)
        for path in stage_dir.glob(f"q9_noinf_{family.name}_stage*.lrat")
        if (match := re.fullmatch(rf"q9_noinf_{family.name}_stage(\d+)\.lrat", path.name))
    )
    if not discovered:
        raise FileNotFoundError(f"no {family.name} stage LRAT files in {stage_dir}")
    if [stage for stage, _ in discovered] != list(range(discovered[-1][0] + 1)):
        raise ValueError(f"{family.name}: stage LRAT files are not contiguous")
    available_last = discovered[-1][0]
    requested_last = available_last if last is None else last
    if requested_last >= len(discovered):
        raise ValueError(f"{family.name}: requested last stage {requested_last} is unavailable")
    full_trace_requested = requested_last == available_last
    if requested_last + 1 < len(discovered):
        discovered = discovered[: requested_last + 1]
    if last is None and requested_last + 1 != family.expected_stages:
        raise ValueError(
            f"{family.name}: expected {family.expected_stages} stages, found {requested_last + 1}"
        )

    original_hash = hashlib.sha256()
    with original.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            original_hash.update(chunk)

    concatenated_hash = hashlib.sha256()
    concatenated_bytes = 0
    active: dict[int, tuple[int, ...]] = {}
    exported: dict[int, tuple[int, ...]] = {}
    additions = 0
    deletions = 0

    for stage, segment in discovered:
        source = lean_dir / f"{family.stage_prefix}{stage}.lean"
        if not source.is_file():
            raise FileNotFoundError(source)
        seed, export_ids, _ = parse_source(source, family, stage)
        invalid_seed = [
            (ident, lits)
            for ident, lits in seed
            if exported.get(ident) != lits
        ]
        if invalid_seed:
            raise ValueError(
                f"{family.name} stage {stage}: seed is not a valid subset of "
                f"the previous export: {invalid_seed[:4]}"
            )
        stage_active = dict(seed)

        if check_olean:
            output = lean_dir / ".lake" / "build" / "lib" / "lean" / f"{family.stage_prefix}{stage}.olean"
            if not output.is_file():
                raise FileNotFoundError(output)

        with segment.open("rb") as stream:
            while chunk := stream.read(1024 * 1024):
                concatenated_hash.update(chunk)
                concatenated_bytes += len(chunk)
        with segment.open("r") as stream:
            for line in stream:
                addition = parse_addition(line)
                if addition is not None:
                    additions += 1
                elif line.split()[1:2] == ["d"]:
                    deletions += 1
                apply_line(line, active)
                apply_line(line, stage_active)

        missing_export = [ident for ident in export_ids if ident not in stage_active]
        if missing_export:
            raise ValueError(
                f"{family.name} stage {stage}: exported inactive clauses: "
                f"{missing_export[:8]}"
            )
        exported = {ident: stage_active[ident] for ident in export_ids}

    source_hash, source_bytes = sha256_file(original)
    expected_bytes = source_bytes
    expected_hash = original_hash.digest()
    if not full_trace_requested:
        prefix_hash = hashlib.sha256()
        remaining = concatenated_bytes
        with original.open("rb") as stream:
            while remaining:
                chunk = stream.read(min(1024 * 1024, remaining))
                if not chunk:
                    raise ValueError(f"{family.name}: original LRAT ended before audited prefix")
                prefix_hash.update(chunk)
                remaining -= len(chunk)
        expected_bytes = concatenated_bytes
        expected_hash = prefix_hash.digest()
    if concatenated_bytes != expected_bytes or concatenated_hash.digest() != expected_hash:
        raise ValueError(
            f"{family.name}: concatenated stage bytes do not equal original "
            f"prefix ({concatenated_bytes} vs {expected_bytes} bytes)"
        )
    print(
        f"{family.name}: {requested_last + 1} segments, {additions} additions, {deletions} deletions, "
        f"{source_bytes} bytes, sha256={source_hash}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["r4", "r5", "all"], default="all")
    parser.add_argument("--last", type=int, help="audit only stages 0..LAST")
    parser.add_argument("--check-olean", action="store_true")
    args = parser.parse_args()
    lean_dir = Path(__file__).resolve().parents[2]
    cert_dir = lean_dir / "certificates" / "q9"
    names = ["r4", "r5"] if args.family == "all" else [args.family]
    for name in names:
        audit_family(lean_dir, cert_dir, FAMILIES[name], args.last, args.check_olean)


if __name__ == "__main__":
    main()
