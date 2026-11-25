#!/usr/bin/env python3
"""Audit extracted Lean code and handwritten proof modules for soundness.

    audit.py              static checks: generated files, external stubs, forbidden
                          tokens, root imports, `cfg(aeneas_extract)` usage
    audit.py --axioms     the above, and the compiled modules of the project (run
                          after `lake build`): every constant of `YoctoCore` and of
                          the modules of `YoctoSpec` it imports is sent to the kernel
                          again, and the axioms of every one are computed from the
                          declarations in the `.olean` files
    audit.py --self-test  the above, and a check that the audit of compiled modules
                          finds theorems a line-based scan would miss, and refuses
                          `sorry`, an axiom, a theorem the kernel never saw, a
                          forged `#print axioms`, a name that is the text of a
                          line of the report, a dependency that is not read from
                          where the dependencies are, and files of a module that
                          are missing or left over
    audit.py --all        everything

The compiled modules are read by `proofs-yata/scripts/check_olean.lean`, a program
that imports `Lean` and no module of the project: no source of the project is
elaborated for the audit. It is started without `LEAN_PATH` (Lean reads it before
the library of the toolchain, so a file of the project could answer what the
program imports) and is told where the modules are.
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

PROOFS_DIR = Path(__file__).resolve().parent.parent
REPO_ROOT = PROOFS_DIR.parent

sys.dont_write_bytecode = True
CODE_DIR = PROOFS_DIR / "YoctoCore" / "Code"
PROPS_DIR = PROOFS_DIR / "YoctoCore" / "Properties"
ROOT_LEAN = PROOFS_DIR / "YoctoCore.lean"
CORE_SRC_DIR = REPO_ROOT / "y-octo-core" / "src"

# The program that audits compiled modules, the module it starts from, the roots
# of the modules under audit (the rest of what they import is a dependency), and
# the modules whose theorems are listed.
CHECKER = REPO_ROOT / "proofs-yata" / "scripts" / "check_olean.lean"
ENTRY_MODULE = "YoctoCore"
AUDITED_ROOTS = ("YoctoCore", "YoctoSpec")
THEOREM_MODULE_PREFIX = "YoctoCore.Properties"
# The packages of `lake-manifest.json` whose modules are under audit. The build
# directory of every other package is a place a dependency may be read from.
AUDITED_PACKAGES = frozenset({"yocto-spec"})
# The dependencies, by the first component of their module names: the toolchain,
# Aeneas, and Mathlib with what it builds on. Anything else fails.
DEPENDENCY_ROOTS = frozenset(
    {
        "Init",
        "Std",
        "Lean",
        "Lake",
        "Aeneas",
        "AeneasMeta",
        "Mathlib",
        "Batteries",
        "Aesop",
        "Qq",
        "Plausible",
        "ProofWidgets",
        "ImportGraph",
        "LeanSearchClient",
    }
)

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Required milestone theorems (L0.1-L0.6, M4-M5). Missing or un-audited declarations fail CI.
REQUIRED_MILESTONE_THEOREMS: tuple[str, ...] = (
    # L0.1 Varint
    "YoctoCore.Properties.Varint.decode_var_u64_total",
    "YoctoCore.Properties.Varint.encode_var_u64_buf_spec",
    "YoctoCore.Properties.Varint.encode_var_u64_total",
    "YoctoCore.Properties.Varint.decode_encode_var_u64_buf_roundtrip",
    "YoctoCore.Properties.Varint.decode_encode_var_u64_roundtrip",
    "YoctoCore.Properties.Varint.decode_var_i32_with_sign_total",
    "YoctoCore.Properties.Varint.decode_var_i32_total",
    "YoctoCore.Properties.Varint.encode_var_i32_buf_spec",
    "YoctoCore.Properties.Varint.encode_var_i32_total",
    "YoctoCore.Properties.Varint.encode_var_i32_loop_prefix",
    "YoctoCore.Properties.Varint.encode_var_i32_prefix",
    # L0.2 ClockSearch
    "YoctoCore.Properties.ClockSearch.find_clock_segment_total",
    "YoctoCore.Properties.ClockSearch.find_clock_segment_sound",
    "YoctoCore.Properties.ClockSearch.find_clock_segment_wf_spec",
    "YoctoCore.Properties.ClockSearch.find_clock_segment_loop_complete",
    # L0.3 OrderRange & DeleteSet
    "YoctoCore.Properties.OrderRange.new_spec",
    "YoctoCore.Properties.OrderRange.contains_spec",
    "YoctoCore.Properties.OrderRange.insert_spec",
    "YoctoCore.Properties.OrderRange.merge_spec",
    "YoctoCore.Properties.OrderRange.merge_comm",
    "YoctoCore.Properties.OrderRange.merge_idem",
    "YoctoCore.Properties.DeleteSet.new_spec",
    "YoctoCore.Properties.DeleteSet.find_index_spec",
    "YoctoCore.Properties.DeleteSet.contains_spec",
    "YoctoCore.Properties.DeleteSet.insert_spec",
    "YoctoCore.Properties.DeleteSet.merge_spec",
    "YoctoCore.Properties.DeleteSet.merge_comm",
    "YoctoCore.Properties.DeleteSet.merge_idem",
    # L0.4 StateVector
    "YoctoCore.Properties.StateVector.new_spec",
    "YoctoCore.Properties.StateVector.find_index_spec",
    "YoctoCore.Properties.StateVector.get_spec",
    "YoctoCore.Properties.StateVector.contains_spec",
    "YoctoCore.Properties.StateVector.set_spec",
    "YoctoCore.Properties.StateVector.set_max_spec",
    "YoctoCore.Properties.StateVector.set_min_spec",
    "YoctoCore.Properties.StateVector.set_max_mono",
    "YoctoCore.Properties.StateVector.set_max_comm",
    "YoctoCore.Properties.StateVector.set_max_idem",
    "YoctoCore.Properties.StateVector.merge_with_spec",
    "YoctoCore.Properties.StateVector.merge_max_spec",
    "YoctoCore.Properties.StateVector.merge_max_comm",
    "YoctoCore.Properties.StateVector.merge_max_idem",
    # L0.5 Utf16
    "YoctoCore.Properties.Utf16.is_valid_utf8_total",
    "YoctoCore.Properties.Utf16.is_valid_utf8_spec",
    "YoctoCore.Properties.Utf16.utf16_len_total",
    "YoctoCore.Properties.Utf16.utf16_len_spec",
    "YoctoCore.Properties.Utf16.utf16_len_append_of_valid",
    "YoctoCore.Properties.Utf16.utf16_split_byte_offset_total",
    "YoctoCore.Properties.Utf16.utf16_split_byte_offset_spec",
    # L0.6 DecoderV1
    "YoctoCore.Properties.DecoderV1.read_state_vector_v1_total",
    "YoctoCore.Properties.DecoderV1.decode_state_vector_v1_total",
    "YoctoCore.Properties.DecoderV1.read_delete_set_v1_total",
    "YoctoCore.Properties.DecoderV1.skip_any_v1_total",
    "YoctoCore.Properties.DecoderV1.read_struct_frame_total",
    "YoctoCore.Properties.DecoderV1.read_client_structs_total",
    "YoctoCore.Properties.DecoderV1.decode_one_client_block_total",
    "YoctoCore.Properties.DecoderV1.decode_update_v1_frame_total",
    # M4 ClientBlocks: totality and I1
    "YoctoCore.Properties.ClientBlocks.new_spec",
    "YoctoCore.Properties.ClientBlocks.len_spec",
    "YoctoCore.Properties.ClientBlocks.is_empty_spec",
    "YoctoCore.Properties.ClientBlocks.continues_spec",
    "YoctoCore.Properties.ClientBlocks.append_spec",
    "YoctoCore.Properties.ClientBlocks.append_wf",
    "YoctoCore.Properties.ClientBlocks.range_spec",
    "YoctoCore.Properties.ClientBlocks.find_loop_spec",
    "YoctoCore.Properties.ClientBlocks.find_spec",
    "YoctoCore.Properties.ClientBlocks.split_boundary_spec",
    "YoctoCore.Properties.ClientBlocks.split_boundary_wf",
    "YoctoCore.Properties.ClientBlocks.mark_deleted_spec",
    "YoctoCore.Properties.ClientBlocks.mark_gc_spec",
    "YoctoCore.Properties.ClientBlocks.set_kind_wf",
    "YoctoCore.Properties.ClientBlocks.merge_adjacent_spec",
    "YoctoCore.Properties.ClientBlocks.merge_adjacent_wf",
    # M4 the pure model of the store and its refinement of `YoctoSpec`
    "YoctoCore.Properties.YataModel.splitNode_spec",
    "YoctoCore.Properties.YataModel.blocks_splitNode",
    "YoctoCore.Properties.YataModel.linkNew_spec",
    "YoctoCore.Properties.YataModel.blocks_linkNew",
    "YoctoCore.Properties.YataModel.scanM_spec",
    "YoctoCore.Properties.YataModel.integrate_scan",
    "YoctoCore.Properties.YataModel.integrate_compose",
    "YoctoCore.Properties.YataModel.gcAll_spec",
    "YoctoCore.Properties.YataModel.markDeleted_spec",
    "YoctoCore.Properties.YataModel.markDeleted_grows",
    "YoctoCore.Properties.YataModel.payload_blocks",
    "YoctoCore.Properties.YataModel.held_iff",
    "YoctoCore.Properties.YataModel.dead_iff",
    "YoctoCore.Properties.YataModel.dead_markDeleted",
    "YoctoCore.Properties.YataModel.splitNode_noStraddle",
    "YoctoCore.Properties.YataModel.Marking.mark",
    "YoctoCore.Properties.YataModel.Marking.final",
    "YoctoCore.Properties.YataModel.sep_of_canIntegrate",
    # M4 YataStore: totality, the invariant, and what every function does on the model
    "YoctoCore.Properties.YataStore.id_eq_spec",
    "YoctoCore.Properties.YataStore.opt_id_eq_spec",
    "YoctoCore.Properties.YataStore.opt_slot_eq_spec",
    "YoctoCore.Properties.YataStore.slot_is_spec",
    "YoctoCore.Properties.YataStore.check_origin_spec",
    "YoctoCore.Properties.YataStore.ids_contain_spec",
    "YoctoCore.Properties.YataStore.new_spec",
    "YoctoCore.Properties.YataStore.client_index_spec",
    "YoctoCore.Properties.YataStore.get_state_spec",
    "YoctoCore.Properties.YataStore.locate_spec",
    "YoctoCore.Properties.YataStore.node_id_spec",
    "YoctoCore.Properties.YataStore.set_left_spec",
    "YoctoCore.Properties.YataStore.set_next_spec",
    "YoctoCore.Properties.YataStore.next_of_spec",
    "YoctoCore.Properties.YataStore.split_node_spec",
    "YoctoCore.Properties.YataStore.split_spec",
    "YoctoCore.Properties.YataStore.split_after_spec",
    "YoctoCore.Properties.YataStore.scan_step_spec",
    "YoctoCore.Properties.YataStore.find_conflict_left_loop_spec",
    "YoctoCore.Properties.YataStore.needs_scan_spec",
    "YoctoCore.Properties.YataStore.conflict_left_spec",
    "YoctoCore.Properties.YataStore.check_append_spec",
    "YoctoCore.Properties.YataStore.ensure_client_spec",
    "YoctoCore.Properties.YataStore.repair_left_spec",
    "YoctoCore.Properties.YataStore.repair_right_spec",
    "YoctoCore.Properties.YataStore.link_spec",
    "YoctoCore.Properties.YataStore.integrate_spec",
    "YoctoCore.Properties.YataStore.check_append_accepts",
    "YoctoCore.Properties.YataStore.integrate_root_spec",
    "YoctoCore.Properties.YataStore.gc_spec",
    "YoctoCore.Properties.YataStore.split_inside_spec",
    "YoctoCore.Properties.YataStore.delete_block_spec",
    "YoctoCore.Properties.YataStore.delete_range_loop_spec",
    "YoctoCore.Properties.YataStore.delete_range_spec",
    # M5 L3: the extracted store refines `YoctoSpec`, end to end
    "YoctoCore.Properties.Refinement.coreRun_sound",
    "YoctoCore.Properties.Refinement.core_sec",
    "YoctoCore.Properties.Refinement.core_sec_ids",
    "YoctoCore.Properties.Refinement.core_witness",
    "YoctoCore.Properties.Refinement.core_witness_sec",
    "YoctoCore.Properties.Refinement.core_sec_visible",
)

# The forbidden words are searched in the raw text of the sources: comments
# and strings count, nothing decides what is code. A word is a run of ASCII
# letters, digits and `_`; a run that starts with a digit, or follows a `#`,
# is searched for the words too (`f 0xFFsorry` is a number and then a word).
BAD_WORDS = (
    "sorry",
    "admit",
    "axiom",
    "native_decide",
    "sorryAx",
    "ofReduceBool",
    "ofReduceNat",
    "implemented_by",
    "unsafe",
    "skipKernelTC",
)
WORD_RE = re.compile(r"(#?)([A-Za-z0-9_]+)")
BAD_INSIDE_RE = re.compile("|".join(BAD_WORDS))
NATIVE_RE = re.compile(r"\+native(?![A-Za-z0-9_])")


def bad_tokens(text: str) -> list[str]:
    """The forbidden words of a raw source text."""
    found = [m.group(0) for m in NATIVE_RE.finditer(text)]
    for m in WORD_RE.finditer(text):
        hash_before, word = m.groups()
        if word in BAD_WORDS:
            found.append(word)
        elif (word[0].isdigit() or hash_before) and BAD_INSIDE_RE.search(word):
            found.append(word)
    return found


def fail(msg: str) -> None:
    print(f"AUDIT FAILURE: {msg}", file=sys.stderr)
    sys.exit(1)


def check_scan() -> None:
    """The word scan finds what a comment lexer or a word boundary lets through."""
    refused = [
        "theorem t : 1 = 2 := ⟨sorry⟩",
        "theorem t : 1 = 2 := by exact x.sorry",
        "-- sorry",
        'def s := "sorry"',
        "def a : Char × Char := ⟨' ','\"'⟩ /- -/ theorem t : 1 = 2 := sorry",
        "theorem t (f : Nat → 1 = 2 → 1 = 2) : 1 = 2 := f 0xFFsorry",
        "theorem t : 1 = 2 := id«sorryAx» _",
        "example := #evalsorry",
        "example : 1 = 1 := by decide +native",
        "set_option debug.skipKernelTC true",
        "axiom made_up : False",
    ]
    for source in refused:
        if not bad_tokens(source):
            fail(f"The word scan lets through: {source}")
    clean = "theorem sorry_free : unsafe_code = axioms := admits native_decides"
    if bad_tokens(clean):
        fail(f"The word scan refuses other words: {bad_tokens(clean)}")


def iter_project_lean_files() -> list[Path]:
    files: list[Path] = []
    for lf in sorted(PROOFS_DIR.rglob("*.lean")):
        rel_parts = lf.relative_to(PROOFS_DIR).parts
        if any(part in {".lake", "logs"} for part in rel_parts):
            continue
        files.append(lf)
    return files


def check_files() -> None:
    if not CODE_DIR.exists():
        fail(f"Missing generated directory: {CODE_DIR}")

    templates = [
        p
        for p in PROOFS_DIR.rglob("*External_Template.lean")
        if ".lake" not in p.relative_to(PROOFS_DIR).parts
    ]
    if templates:
        fail(f"Unexpected external templates (unmodeled Rust items): {templates}")

    externals = [
        p
        for p in PROOFS_DIR.rglob("*External.lean")
        if ".lake" not in p.relative_to(PROOFS_DIR).parts
    ]
    if externals:
        fail(f"Unexpected external stub files (zero externals expected): {externals}")

    for required in [CODE_DIR / "Types.lean", CODE_DIR / "Funs.lean"]:
        if not required.exists():
            fail(f"Missing generated file: {required}")

    # the root file: imports and nothing else, so that no comment hides one
    root_text = ROOT_LEAN.read_text() if ROOT_LEAN.exists() else ""
    stray = [line for line in root_text.splitlines() if line and not re.fullmatch(r"import [A-Za-z0-9_.]+", line)]
    if stray:
        fail(f"Root file {ROOT_LEAN}: only `import <module>` lines are allowed: {stray[:3]}")
    root_imports = set(re.findall(r"^import (\S+)$", root_text, re.M))
    modules = property_modules()
    if not modules:
        fail(f"No property proof files found in {PROPS_DIR}")
    for mod in modules:
        if mod not in root_imports:
            fail(f"Root file {ROOT_LEAN} does not import {mod}")

    lean_files = iter_project_lean_files()
    if not lean_files:
        fail(f"No .lean files found under {PROOFS_DIR}")

    for lf in lean_files:
        text = lf.read_text()
        # as it is, and with the `«` and `»` of quoted names taken out
        for token in bad_tokens(text) + bad_tokens(text.replace("«", "").replace("»", "")):
            fail(f"Disallowed token '{token}' in {lf.relative_to(PROOFS_DIR)}")


def property_modules() -> list[str]:
    """The module of every `.lean` file below `YoctoCore/Properties`, at any depth."""
    if not PROPS_DIR.exists():
        return []
    return sorted(
        ".".join(pf.relative_to(PROOFS_DIR).with_suffix("").parts) for pf in PROPS_DIR.rglob("*.lean")
    )


AENEAS_DERIVE_RE = re.compile(r"#\[cfg_attr\(\s*not\(\s*aeneas_extract\s*\)\s*,\s*derive\([^()]*\)\s*\)\]")


def check_aeneas_extract_cfg() -> None:
    """`cfg(aeneas_extract)` may only take derives away: extraction and the compiled
    crate run the same code. Anything else that names the flag fails, comments included."""
    sources = sorted(CORE_SRC_DIR.rglob("*.rs"))
    if not sources:
        fail(f"No Rust sources found in {CORE_SRC_DIR}")
    for source in sources:
        rest = AENEAS_DERIVE_RE.sub("", source.read_text())
        for number, line in enumerate(rest.splitlines(), 1):
            if "aeneas_extract" in line:
                fail(
                    f"{source.relative_to(REPO_ROOT)}:{number}: `aeneas_extract` outside "
                    f"`#[cfg_attr(not(aeneas_extract), derive(...))]`: {line.strip()}"
                )


class Report:
    """What `check_olean.lean` printed for a set of compiled modules."""

    def __init__(self) -> None:
        self.status = 0
        self.dependencies: dict[str, int] = {}
        self.modules: set[str] = set()
        # (module, name) of the axioms the modules under audit declare
        self.axioms: list[tuple[str, str]] = []
        # name -> (kind, module, axioms it depends on); kind is `public` for a
        # theorem under a name others can use, `aux` for a private or generated one
        self.theorems: dict[str, tuple[str, str, set[str]]] = {}
        # (module, name) of the unsafe and partial constants, which the kernel
        # does not check
        self.skipped: list[tuple[str, str]] = []
        # (constants the kernel accepted, constants it does not check, ms)
        self.kernel: tuple[int, int, int] | None = None
        self.refusals: list[str] = []


def lean_search_path() -> str:
    """Where Lake has the modules of the project and of its packages: its
    `LEAN_PATH`, read as text and handed to the audit program as an argument."""
    res = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=PROOFS_DIR, capture_output=True, text=True)
    if res.returncode != 0 or not res.stdout.strip():
        fail(f"`lake env printenv LEAN_PATH` failed:\n{res.stdout}\n{res.stderr}")
    return res.stdout.strip()


def dependency_paths() -> list[Path]:
    """Where a dependency may be read from, besides the toolchain: the build
    directory of every package of `lake-manifest.json` that is not under audit.
    A module called `Mathlib.X` in the build directory of the project is not one
    of Mathlib."""
    manifest = json.loads((PROOFS_DIR / "lake-manifest.json").read_text())
    packages_dir = PROOFS_DIR / manifest.get("packagesDir", ".lake/packages")
    paths: list[Path] = []
    for package in manifest["packages"]:
        name = package["name"].strip("«»")
        if name in AUDITED_PACKAGES:
            continue
        if package["type"] == "path":
            directory = PROOFS_DIR / package["dir"]
        elif package["type"] == "git":
            directory = packages_dir / name / (package.get("subDir") or "")
        else:
            fail(f"lake-manifest.json: package {name} of unknown type {package['type']!r}")
        lib = directory / ".lake" / "build" / "lib" / "lean"
        if lib.is_dir():
            paths.append(lib)
    return paths


def refused_character(c: str) -> bool:
    """A character no field of the report has: a control character, a line
    separator."""
    return ord(c) < 0x20 or 0x7F <= ord(c) < 0xA0 or c in (chr(0x2028), chr(0x2029))


def check_olean(
    entries: list[str],
    roots: list[str],
    search_path: str,
    dependencies: list[Path],
    required: list[str] | None = None,
) -> Report:
    """Runs the audit of compiled modules on the modules `entries` import that are
    below `roots`. They are looked up in the toolchain, then in `search_path`;
    a module that is not below `roots` has to be read from the toolchain or from
    one of `dependencies`. `required` are theorems that have to be there."""
    arguments = ["--run", str(CHECKER), "--search-path", search_path]
    for directory in dependencies:
        arguments += ["--dependency-path", str(directory)]
    for root in roots:
        arguments += ["--audit", root]
    # Lean reads `LEAN_PATH` before the library of the toolchain: without it, what
    # the program imports is the toolchain's. No `lake env` here.
    environment = {key: value for key, value in os.environ.items() if key != "LEAN_PATH"}
    with tempfile.TemporaryDirectory() as tmp_name:
        if required is not None:
            listing = Path(tmp_name) / "required"
            listing.write_text("".join(f"{name}\n" for name in required))
            arguments += ["--required", str(listing)]
        res = subprocess.run(
            ["lean", *arguments, *entries], cwd=PROOFS_DIR, capture_output=True, env=environment
        )
    # bytes, and no translation of line ends: a carriage return is a character
    # the report does not have
    if res.stderr.strip():
        print(res.stdout.decode(errors="replace"))
        fail(f"Unexpected stderr from the audit of compiled modules:\n{res.stderr.decode(errors='replace')}")
    try:
        output = res.stdout.decode("utf-8")
    except UnicodeDecodeError as error:
        fail(f"The audit of compiled modules did not print UTF-8: {error}")
    if output and not output.endswith("\n"):
        fail("The report of the audit of compiled modules stops in the middle of a line")

    report = Report()
    report.status = res.returncode
    for line in output.split("\n")[:-1]:
        fields = line.split("\t")
        if any(refused_character(c) for field in fields for c in field) or "" in fields[:4]:
            fail(f"Unexpected characters or an empty field in the report of the audit: {line!r}")
        if fields[0] == "D" and len(fields) == 3 and fields[2].isdigit():
            report.dependencies[fields[1]] = int(fields[2])
        elif fields[0] == "M" and len(fields) == 2:
            report.modules.add(fields[1])
        elif fields[0] == "A" and len(fields) == 3:
            report.axioms.append((fields[1], fields[2]))
        elif fields[0] == "S" and len(fields) == 3:
            report.skipped.append((fields[1], fields[2]))
        elif fields[0] == "T" and len(fields) == 5 and fields[1] in {"public", "aux"}:
            if fields[3] in report.theorems:
                fail(f"Theorem reported twice: {fields[3]}")
            report.theorems[fields[3]] = (fields[1], fields[2], set(fields[4].split(" ")) - {""})
        elif fields[0] == "K" and len(fields) == 4 and all(f.isdigit() for f in fields[1:]) and not report.kernel:
            report.kernel = (int(fields[1]), int(fields[2]), int(fields[3]))
        elif fields[0] == "E" and len(fields) == 2:
            report.refusals.append(fields[1])
        else:
            fail(f"Unexpected line from the audit of compiled modules: {line!r}")
    if (report.status == 0) != (not report.refusals) or report.status not in (0, 1):
        fail(f"The audit of compiled modules exited with {report.status} and {len(report.refusals)} refusals")
    if report.kernel is not None:
        # no more theorems and axioms than constants the kernel was given, and
        # the constants it does not check are the ones that are listed
        constants, skipped, _ = report.kernel
        if len(report.theorems) + len(report.axioms) > constants + skipped:
            fail(
                f"The report has {len(report.theorems)} theorems and {len(report.axioms)} axioms "
                f"for {constants + skipped} constants"
            )
        if len(report.skipped) != skipped:
            fail(f"The report lists {len(report.skipped)} constants the kernel does not check, and counts {skipped}")
    return report


def check_theorems(theorems: dict[str, tuple[str, str, set[str]]], axioms: list[tuple[str, str]]) -> list[str]:
    """The problems of a report: declared axioms, and theorems that depend on
    anything but the allowed ones."""
    problems = [f"axiom '{name}' declared in {module}" for module, name in axioms]
    for name, (_, module, used) in sorted(theorems.items()):
        disallowed = used - ALLOWED_AXIOMS
        if disallowed:
            problems.append(f"'{name}' ({module}) depends on {sorted(disallowed)}")
    return problems


def module_of(lean_file: Path) -> str:
    return ".".join(lean_file.relative_to(PROOFS_DIR).with_suffix("").parts)


def check_axioms() -> None:
    twice = sorted({name for name in REQUIRED_MILESTONE_THEOREMS if REQUIRED_MILESTONE_THEOREMS.count(name) > 1})
    if twice:
        fail(f"Milestone theorems listed twice: {twice}")
    # the program checks the milestone theorems itself, by name; they are
    # looked up in its report once more below
    report = check_olean(
        [ENTRY_MODULE],
        list(AUDITED_ROOTS),
        lean_search_path(),
        dependency_paths(),
        required=list(REQUIRED_MILESTONE_THEOREMS),
    )
    # what the program refuses, and the same from its report once more
    problems = report.refusals + check_theorems(report.theorems, report.axioms)
    if problems:
        fail("Audit of compiled modules:\n  " + "\n  ".join(problems))
    if report.kernel is None:
        fail("The kernel did not check the constants of the compiled modules")
    unexpected_roots = sorted(set(report.dependencies) - DEPENDENCY_ROOTS)
    if unexpected_roots:
        fail(f"The project imports modules of unexpected libraries: {unexpected_roots}")

    # every file of the project was read, and no other module passes for one
    on_disk = {module_of(lf) for lf in iter_project_lean_files()}
    on_disk = {module for module in on_disk if module.split(".")[0] == ENTRY_MODULE}
    loaded = {module for module in report.modules if module.split(".")[0] == ENTRY_MODULE}
    if loaded != on_disk:
        fail(
            "Modules of the compiled project and on disk differ: "
            f"only compiled={sorted(loaded - on_disk)}, only on disk={sorted(on_disk - loaded)}"
        )

    def in_properties(module: str) -> bool:
        return (module + ".").startswith(THEOREM_MODULE_PREFIX + ".")

    expected_modules = set(property_modules())
    modules = {module for module in report.modules if in_properties(module)}
    if modules != expected_modules:
        fail(
            "Property modules in the compiled project and on disk differ: "
            f"only compiled={sorted(modules - expected_modules)}, only on disk={sorted(expected_modules - modules)}"
        )
    theorems = {name: entry for name, entry in report.theorems.items() if in_properties(entry[1])}
    public = sorted(name for name, (kind, _, _) in theorems.items() if kind == "public")
    if not public:
        fail("No public theorems found in the property modules")
    missing_required = sorted(set(REQUIRED_MILESTONE_THEOREMS) - set(public))
    if missing_required:
        fail(f"Missing required milestone theorems: {missing_required}")

    listing = PROOFS_DIR / "logs" / "theorems.txt"
    listing.parent.mkdir(parents=True, exist_ok=True)
    listing.write_text("".join(f"{name}\t{' '.join(sorted(theorems[name][2])) or '-'}\n" for name in public))
    constants, skipped, ms = report.kernel
    print(
        f"Kernel replay passed for {constants} constants of {len(report.modules)} compiled modules "
        f"({', '.join(AUDITED_ROOTS)}; {skipped} unsafe or partial ones are not checked) in {ms / 1000:.1f} s."
    )
    print(
        f"Axiom audit passed for {len(public)} public theorems of {len(modules)} modules "
        f"(and {len(report.theorems) - len(public)} private, generated or imported ones; "
        f"{len(REQUIRED_MILESTONE_THEOREMS)} required milestone theorems present; "
        f"only {sorted(ALLOWED_AXIOMS)} allowed). List: {listing.relative_to(PROOFS_DIR)}"
    )


# Modules no audit of the sources reads right, compiled outside the project and
# read from their `.olean` files.
PROBE_ROOT = "YoctoCoreAuditProbe"
# A signature that starts on the line after `theorem`, a name outside the
# namespace of its file, a private lemma, a theorem that is not proved, and an
# axiom; in a subdirectory of its root.
PROBE_MODULE = f"{PROBE_ROOT}.Properties.Sub.Probe"
PROBE_SOURCE = """
namespace YoctoCoreAuditProbe.Properties.Sub

theorem
  wrapped_signature
    (n : Nat) :
    True := trivial

private theorem hidden_helper : True := trivial

theorem not_proved : 1 = 1 := sorry

axiom made_up : False

theorem from_axiom : False := made_up

end YoctoCoreAuditProbe.Properties.Sub

theorem
  outsideTheNamespace : True := trivial
"""
# Nothing to refuse: the audit has to accept it, with the kernel.
CLEAN_MODULE = f"{PROBE_ROOT}.Clean"
CLEAN_SOURCE = """
theorem YoctoCoreAuditProbe.one : 1 = 1 := rfl
theorem YoctoCoreAuditProbe.em (p : Prop) : p ∨ ¬p := Classical.em p
def YoctoCoreAuditProbe.double (n : Nat) : Nat := n + n
"""
# A theorem the kernel never saw: it has no axiom and no `sorry`, and its proof
# is none.
UNCHECKED_MODULE = f"{PROBE_ROOT}.Unchecked"
UNCHECKED_SOURCE = """
set_option debug.skipKernelTC true in
theorem YoctoCoreAuditProbe.unchecked : 1 = 2 := by decide +kernel
"""
# A forged report of `#print axioms`, which an audit that elaborates the module
# and reads what it prints would believe.
FORGED_MODULE = f"{PROBE_ROOT}.Forged"
FORGED_SOURCE = """
open Lean in macro_rules | `(#print axioms $x:ident) => `(#eval IO.println ("'" ++ $(quote (toString x.getId)) ++ "' depends on axioms: [propext]"))
theorem YoctoCoreAuditProbe.forged : 1 = 2 := sorry
#print axioms YoctoCoreAuditProbe.forged
"""
# A theorem whose name is the text of a report: a `»`, after which Lean prints
# a name as it is, the end of a line, and a line that says a theorem that does
# not exist is there. The audit of the milestone theorems reads such lines.
LINE_MODULE = f"{PROBE_ROOT}.Line"
LINE_SOURCE = r"""
import Lean
open Lean Elab Command in
run_cmd liftCoreM do
  addDecl <| .thmDecl
    { name := .str (.str .anonymous "YoctoCoreAuditProbe") "»a\t\nT\tpublic\tYoctoCoreAuditProbe.Line\tYoctoCoreAuditProbe.absent",
      levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
theorem YoctoCoreAuditProbe.plain : True := trivial
"""
# A false theorem in a module that is called like one of Mathlib and is none: it
# is not under audit, so nothing sends it to the kernel, and the theorem that
# uses it has no axiom and no hole. Only where it is read from tells.
FAKE_DEPENDENCY_MODULE = "Mathlib.YoctoCoreAuditProbe"
FAKE_DEPENDENCY_SOURCE = """
set_option debug.skipKernelTC true in
theorem Mathlib.yoctoCoreAuditProbe : 1 = 2 := by decide +kernel
"""
TRUSTING_MODULE = f"{PROBE_ROOT}.Trusting"
TRUSTING_SOURCE = f"""
import {FAKE_DEPENDENCY_MODULE}
theorem YoctoCoreAuditProbe.trusting : 1 = 2 := Mathlib.yoctoCoreAuditProbe
"""
# A module of the module system, which Lean saves in three files; then the same
# without the file that has every constant, and a module that is none with such
# a file next to it. (`proofs-yata/scripts/audit.sh` also rewrites the parts so
# that they do not agree.)
PARTS_MODULE = f"{PROBE_ROOT}.Parts"
PARTS_SOURCE = """
module
public theorem YoctoCoreAuditProbe.shown : True := trivial
theorem YoctoCoreAuditProbe.kept : 1 = 1 := rfl
public def YoctoCoreAuditProbe.twice (n : Nat) : Nat := n + n
"""
NO_PRIVATE_MODULE = f"{PROBE_ROOT}.NoPrivate"
STALE_MODULE = f"{PROBE_ROOT}.Stale"


def olean_of(tmp: Path, module: str) -> Path:
    return (tmp / "lib").joinpath(*module.split(".")).with_suffix(".olean")


def compile_probe(tmp: Path, module: str, text: str) -> None:
    """Compiles `text` as `module` into `tmp/lib`, on the toolchain and the probes
    that are there already."""
    olean = olean_of(tmp, module)
    olean.parent.mkdir(parents=True, exist_ok=True)
    # Lean names a module after its path below the root it is given.
    root = tmp / "src"
    source = root.joinpath(*module.split(".")).with_suffix(".lean")
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(text)
    res = subprocess.run(
        ["lean", f"--root={root}", "-o", str(olean), str(source)],
        cwd=PROOFS_DIR,
        capture_output=True,
        text=True,
        env={**os.environ, "LEAN_PATH": str(tmp / "lib")},
    )
    if res.returncode != 0 or not olean.exists():
        print(res.stdout)
        print(res.stderr, file=sys.stderr)
        fail(f"Self-test: the probe module {module} did not compile")


def self_test() -> None:
    absent = f"{PROBE_ROOT}.absent"
    with tempfile.TemporaryDirectory() as tmp_name:
        tmp = Path(tmp_name)
        probes = {
            PROBE_MODULE: PROBE_SOURCE,
            CLEAN_MODULE: CLEAN_SOURCE,
            UNCHECKED_MODULE: UNCHECKED_SOURCE,
            FORGED_MODULE: FORGED_SOURCE,
            LINE_MODULE: LINE_SOURCE,
            FAKE_DEPENDENCY_MODULE: FAKE_DEPENDENCY_SOURCE,
            TRUSTING_MODULE: TRUSTING_SOURCE,
            PARTS_MODULE: PARTS_SOURCE,
        }
        for module, text in probes.items():
            compile_probe(tmp, module, text)
        parts = olean_of(tmp, PARTS_MODULE)
        sides = [parts.with_name(parts.name + suffix) for suffix in (".server", ".private")]
        if not all(side.exists() for side in sides):
            fail("Self-test: the module of the module system was not saved in three files")
        no_private = olean_of(tmp, NO_PRIVATE_MODULE)
        shutil.copy(parts, no_private)
        shutil.copy(sides[0], no_private.with_name(no_private.name + ".server"))
        stale = olean_of(tmp, STALE_MODULE)
        shutil.copy(olean_of(tmp, CLEAN_MODULE), stale)
        shutil.copy(sides[1], stale.with_name(stale.name + ".private"))

        # the probes are below `tmp/lib`; the dependencies are where the ones of
        # the project are
        lib, dependencies = str(tmp / "lib"), dependency_paths()
        clean = check_olean(
            [CLEAN_MODULE, PARTS_MODULE], [PROBE_ROOT], lib, dependencies, required=[f"{PROBE_ROOT}.shown"]
        )
        refused_modules = [PROBE_MODULE, FORGED_MODULE, LINE_MODULE, TRUSTING_MODULE, NO_PRIVATE_MODULE]
        probe = check_olean(
            [*refused_modules, STALE_MODULE, UNCHECKED_MODULE], [PROBE_ROOT], lib, dependencies, required=[absent]
        )

    def refused(report: Report, needle: str) -> None:
        if report.status == 0 or not any(needle in refusal for refusal in report.refusals):
            fail(f"Self-test: the audit did not refuse a probe with {needle!r}: {report.refusals}")

    no_axioms: tuple[str, str, set[str]] = ("", "", set())
    if clean.status != 0 or clean.kernel is None or check_theorems(clean.theorems, clean.axioms):
        fail(f"Self-test: the audit refuses a clean module: {clean.refusals}")
    if clean.theorems.get("YoctoCoreAuditProbe.em", no_axioms)[2] != ALLOWED_AXIOMS:
        fail(f"Self-test: the axioms of a classical theorem: {clean.theorems}")
    if clean.theorems.get("YoctoCoreAuditProbe.shown", no_axioms)[:2] != ("public", PARTS_MODULE):
        fail(f"Self-test: the theorem of a module of the module system: {clean.theorems}")

    sub = "YoctoCoreAuditProbe.Properties.Sub"
    # the module without its `.olean.private` is not read
    expected_modules = {PROBE_MODULE, FORGED_MODULE, LINE_MODULE, TRUSTING_MODULE, STALE_MODULE, UNCHECKED_MODULE}
    if probe.modules != expected_modules:
        fail(f"Self-test: modules {sorted(probe.modules)}")
    public = {name for name, (kind, _, _) in probe.theorems.items() if kind == "public"}
    expected_public = {
        f"{sub}.wrapped_signature",
        f"{sub}.not_proved",
        f"{sub}.from_axiom",
        "outsideTheNamespace",
        "YoctoCoreAuditProbe.forged",
        "YoctoCoreAuditProbe.unchecked",
        "YoctoCoreAuditProbe.plain",
        "YoctoCoreAuditProbe.trusting",
        # the module with a part left next to it is a copy of the clean one
        "YoctoCoreAuditProbe.one",
        "YoctoCoreAuditProbe.em",
    }
    if public != expected_public:
        fail(f"Self-test: public theorems {sorted(public)}, expected {sorted(expected_public)}")
    if not any(name.endswith("hidden_helper") and kind == "aux" for name, (kind, _, _) in probe.theorems.items()):
        fail("Self-test: the private theorem was not enumerated")
    if probe.axioms != [(PROBE_MODULE, f"{sub}.made_up")]:
        fail(f"Self-test: declared axioms {probe.axioms}")
    if probe.theorems.get("YoctoCoreAuditProbe.forged", no_axioms)[2] != {"sorryAx"}:
        fail(f"Self-test: the forged report was believed: {probe.theorems}")
    problems = check_theorems(probe.theorems, probe.axioms)
    for needle in ["made_up' declared", "not_proved'", "sorryAx", "from_axiom'", "forged'"]:
        if not any(needle in problem for problem in problems):
            fail(f"Self-test: the audit did not report {needle!r}: {problems}")
        refused(probe, needle)
    proved = ["wrapped_signature", "outsideTheNamespace", "hidden_helper"]
    # no axiom is reported for the unchecked theorem: only the kernel tells; and
    # none for the one that uses the false theorem of a dependency
    for name in [*proved, "unchecked", "trusting"]:
        if any(name in problem for problem in problems):
            fail(f"Self-test: a theorem without refused axioms was reported: {problems}")
    refused(probe, "the kernel refuses the constants: while replaying declaration 'YoctoCoreAuditProbe.unchecked")
    if probe.kernel is not None:
        fail("Self-test: the kernel accepted a theorem that is not proved")
    if any(any(name in refusal for name in [*proved, "trusting"]) for refusal in probe.refusals):
        fail(f"Self-test: a proved theorem was refused: {probe.refusals}")
    # the name that is a line: refused, and the theorem it announces is not there
    refused(probe, "has a name that cannot be printed: YoctoCoreAuditProbe.»a\\t\\nT\\tpublic\\t")
    refused(probe, f"required theorem missing: {absent}")
    if absent in probe.theorems:
        fail(f"Self-test: a name that is the text of a line put a theorem in the report: {probe.theorems[absent]}")
    # the module that is called like one of Mathlib: its name passes, where it is does not
    if not set(probe.dependencies) <= DEPENDENCY_ROOTS or "Mathlib" not in probe.dependencies:
        fail(f"Self-test: the dependencies of the probes: {probe.dependencies}")
    refused(probe, f"the dependency {FAKE_DEPENDENCY_MODULE} is read from")
    # the files of a module
    refused(probe, f"{NO_PRIVATE_MODULE} is a module of the module system, and there is no file")
    refused(probe, f"{STALE_MODULE} is no module of the module system, and there is a file")

    print(
        "Self-test passed: wrapped signatures, submodules, private theorems, `sorry` and axioms are found; "
        "a theorem the kernel never saw, a forged `#print axioms`, a name that is a line of the report, "
        "a dependency outside the dependency paths and missing or left over parts of a module are refused."
    )


def main() -> None:
    args = set(sys.argv[1:])
    unknown = args - {"--axioms", "--self-test", "--all"}
    if unknown:
        fail(f"Unknown arguments: {sorted(unknown)}")
    check_scan()
    check_files()
    check_aeneas_extract_cfg()
    print("Static file, hole and cfg(aeneas_extract) audit passed.")
    if args & {"--axioms", "--all"}:
        check_axioms()
    if args & {"--self-test", "--all"}:
        self_test()


if __name__ == "__main__":
    main()
