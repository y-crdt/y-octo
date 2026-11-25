#!/usr/bin/env bash
# Audit of the Lean sources and of what they are compiled to.
#
# The sources are read as raw text: comments and strings count, nothing decides
# what is code. A word is a run of ASCII letters, digits and `_`; a run that
# starts with a digit, or follows a `#`, is searched for the words too
# (`f 0xFFsorry` is a number and then a word). The text is read twice, as it is
# and with the `«` and `»` of quoted names taken out. Fails if
# - any `.lean` file below this directory, but the audit program
#   `scripts/check_olean.lean`, has one of the words `sorry`, `admit`,
#   `native_decide`, `axiom`, an escape hatch of the compiler (`unsafe`,
#   `partial`, `opaque`, `implemented_by`, `extern`), a word that extends the
#   syntax (`macro`, `syntax`, `elab`, `notation`, …), or the word `debug` or
#   `bootstrap` anywhere after a `set_option`;
# - a file other than `Main.lean` (the oracle, which no module of `YoctoSpec`
#   imports), so every file of `YoctoSpec`,
#   - has an attribute other than `@[simp]`, or the word `attribute`,
#   - has a `#` that is not followed by a space or another `#` (no `#eval`,
#     `#print`, … command; the titles of the doc comments stay),
#   - has one of the words `set_option`, `run_cmd`, `run_elab`, `run_meta`,
#     `Lean`,
#   - has a line with `import` in it that is not, as a whole,
#     `import YoctoSpec.<module>`;
# - `scripts/check_olean.lean` imports anything but `Lean.Replay`, or has a
#   NUL byte;
# - `lean-toolchain` is not the pinned one;
# - the package is configured by anything but the few plain lines of
#   `lakefile.toml` below (no `lakefile.lean`, no compiler or linker
#   arguments, no options, no external libraries, no dependencies);
# - a source has a NUL byte (some `awk` stop reading a line there), or there
#   is a symbolic link below this directory (`find` does not look behind one).
# Before it reads the sources it runs the scan on sources written to get past
# a scan (below) and fails unless every one of them is refused.
#
# The compiled modules are read by `scripts/check_olean.lean`, a program that
# imports `Lean` and nothing of the project: it loads the `.olean` files of
# `YoctoSpec` as data, sends every constant in them to the kernel again and
# computes the axioms of every one from the declarations. No source of the
# project is elaborated for it and no output of `#print axioms` is parsed. It
# is started without `LEAN_PATH`, so that what it imports is the toolchain's,
# and is told where the modules are. Fails if
# - the kernel refuses a constant of `YoctoSpec`;
# - a module of `YoctoSpec` declares an axiom, or one of its constants (a
#   theorem or not) depends on an axiom other than `propext`,
#   `Classical.choice` and `Quot.sound`;
# - a theorem of the list below is not a theorem of `YoctoSpec`, or is listed
#   twice;
# - `YoctoSpec` imports a module that is not read from the toolchain, or the
#   modules that were read are not the files of `YoctoSpec` on disk;
# - the files of a module are not the ones Lean writes for it: parts of a
#   module of the module system that are missing, left next to a module that
#   is none, or that do not agree on what the module exports;
# - a name of the report has a control character or a `»` in it, or the
#   report has more theorems than the kernel was given constants.
# Before it reads `YoctoSpec` it compiles modules written to get past an audit
# (a theorem that is not proved, an axiom, a theorem the kernel never saw, a
# forged `#print axioms`, a `native_decide`, a missing theorem, a theorem
# whose name is the text of a line of the report, a false theorem in a
# dependency outside the toolchain, files of a module that were taken away,
# added or rewritten) and fails unless the program refuses every one of them,
# for the right reason, and accepts the clean ones.
#
#   audit.sh --static   everything above that reads text: the sources and the
#                       package. It runs no Lean and needs no build: CI runs it
#                       before the first file of `YoctoSpec` is built, since a
#                       source could run code at build time.
#   audit.sh            the same, then the compiled modules. Run after
#                       `lake build`.
set -euo pipefail
cd "$(dirname "$0")/.."
# bytes, not characters, and one order for every list below
export LC_ALL=C

static=0
case "$#:${1:-}" in
0:) ;;
1:--static) static=1 ;;
*)
  echo "usage: audit.sh [--static]" >&2
  exit 2
  ;;
esac
checker=scripts/check_olean.lean

required=$(sort <<'REQUIRED'
YoctoSpec.scan_spec
YoctoSpec.legal_integrate
YoctoSpec.stable
YoctoSpec.legal_unique
YoctoSpec.precedes_iff
YoctoSpec.precedes_irrefl
YoctoSpec.precedes_asymm
YoctoSpec.precedes_trans
YoctoSpec.precedes_total
YoctoSpec.precedes_stable
YoctoSpec.Reachable.inv
YoctoSpec.sec
YoctoSpec.sec_ids
YoctoSpec.sec_doc
YoctoSpec.sec_visible
YoctoSpec.DeleteSet.union_idem
YoctoSpec.DeleteSet.union_comm
YoctoSpec.DeleteSet.union_assoc
YoctoSpec.Doc.delete_integrate
YoctoSpec.Doc.delete_comm
YoctoSpec.Doc.delete_idem
YoctoSpec.Doc.deleteAll_comm
YoctoSpec.Doc.visible_delete
YoctoSpec.flatten_split
YoctoSpec.toDoc_split
YoctoSpec.flatten_mergeAt
YoctoSpec.toDoc_mergeAt
YoctoSpec.toDoc_mergeAll
YoctoSpec.toDoc_gcContent
YoctoSpec.visible_gcContent
YoctoSpec.visible_gcNodeAt
YoctoSpec.sim
YoctoSpec.flatten_integrateBlock
YoctoSpec.drain_spec
YoctoSpec.drain_minimal
YoctoSpec.applyUpdate_pending_minimal
YoctoSpec.mem_deletedSet_deleteRange
YoctoSpec.BInv.integrate
YoctoSpec.BInv.deletes
YoctoSpec.brun_sound
YoctoSpec.BInv.sec
YoctoSpec.BInv.sec_ids
YoctoSpec.bsec
YoctoSpec.bsec_ids
YoctoSpec.bsec_visible_ids
YoctoSpec.visible_eq_map
YoctoSpec.BInv.sec_visible
YoctoSpec.bsec_visible
REQUIRED
)

fail() {
  echo "audit: $*" >&2
  exit 1
}

BASE_WORDS='sorry|sorryAx|admit|native_decide|axiom|unsafe|partial|opaque|implemented_by|extern'
EXTENSION_WORDS='macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|declare_syntax_cat|binder_predicate|initialize|builtin_initialize'
STRICT_WORDS='set_option|run_cmd|run_elab|run_meta|attribute|Lean'

# scan_text NAME KIND: the findings in the raw text on stdin, one a line, as
# `what: name:line: text`. KIND is `strict` for a file of `YoctoSpec`, `base`
# for the oracle.
scan_text() {
  awk -v name="$1" -v kind="$2" -v base="$BASE_WORDS" -v extension="$EXTENSION_WORDS" \
    -v strict="$STRICT_WORDS" '
    function found(what) { print what ": " name ":" NR ": " $0 }
    # the word is one of `words`, or a number or a `#` command with one glued to it
    function has(word, before, words) {
      if (word ~ ("^(" words ")$")) return 1
      return (word ~ /^[0-9]/ || before == "#") && word ~ ("(" words ")")
    }
    {
      rest = $0
      while (match(rest, /[A-Za-z0-9_]+/)) {
        word = substr(rest, RSTART, RLENGTH)
        before = RSTART > 1 ? substr(rest, RSTART - 1, 1) : ""
        rest = substr(rest, RSTART + RLENGTH)
        if (has(word, before, base)) found("forbidden word")
        if (has(word, before, extension)) found("syntax extension")
        if (option && word ~ /^(debug|bootstrap)$/) found("kernel checking or debug option")
        if (word == "set_option") option = 1
        if (kind == "strict" && has(word, before, strict)) found("word not allowed in YoctoSpec")
      }
      if (kind != "strict") next
      rest = $0
      gsub(/@\[simp\]/, "", rest)
      if (index(rest, "@[")) found("attribute other than @[simp]")
      if ($0 ~ /#([^# ]|$)/) found("# command")
      if (index($0, "import") && $0 !~ /^import YoctoSpec(\.[A-Za-z0-9_]+)*$/) found("import line")
    }'
}

# has_nul FILE NAME: the finding when the file has a NUL byte.
has_nul() {
  if [ "$(tr -d '\000' <"$1" | wc -c)" -ne "$(wc -c <"$1")" ]; then
    echo "NUL byte: $2: the file has a NUL byte"
  fi
}

# scan_file FILE NAME KIND: the text as it is, and without `«` and `»`.
scan_file() {
  has_nul "$1" "$2"
  {
    scan_text "$2" "$3" <"$1"
    sed "s/$(printf '\302\253')//g; s/$(printf '\302\273')//g" "$1" | scan_text "$2" "$3"
  } | sort -u
}

# The scan refuses the sources that got past earlier versions of this audit:
# each hides a `sorry`, forges what `#print axioms` prints, turns kernel
# checking off or runs code at build time.
probe_dir=$(mktemp -d)
trap 'rm -rf "$probe_dir"' EXIT
probe() {
  local name="$1" expected="$2" found
  cat >"$probe_dir/$name.lean"
  found=$(scan_file "$probe_dir/$name.lean" "$name" strict | sed -E 's/: .*$//' | sort -u | tr '\n' ';')
  case "$expected" in
  none) [ -z "$found" ] || fail "the scan refuses the clean probe $name: $found" ;;
  *) case ";$found" in
    *";$expected;"*) ;;
    *) fail "the scan reports '$found' for the probe $name, expected '$expected'" ;;
    esac ;;
  esac
}
# strings, characters and comments written to hide a `sorry` from a lexer
probe A "forbidden word" <<'PROBE'
def a7 : String × String := ⟨r"\" /- "
" -/ , ""⟩
def b7 := "/-"
open Lean in macro_rules | `(#print axioms $x:ident) => `(#eval IO.println ("'" ++ $(quote (toString x.getId)) ++ "' depends on axioms: [propext]"))
theorem t7 : 1 = 2 := sorry
def c7 := "-/" -- "
#print axioms t7
PROBE
probe A2 "forbidden word" <<'PROBE'
def a11 (foo : String → String) : String := foo⟨r"\" /- "
" -/ ⟩
theorem t11 : 1 = 2 := sorry
def c11 := "-/" -- "
#print axioms t11
PROBE
probe B "forbidden word" <<'PROBE'
instance : Coe String Bool := ⟨fun _ => true⟩
def g10 : Nat := assert!"{ /- "; 0
theorem t10 : 1 = 2 := sorry
def c10 := " -/ }"
#print axioms t10
PROBE
probe C1 "forbidden word" <<'PROBE'
def g8 (x : Nat) : Nat := dbg_trace "{x /- }" -/}"; x
def b8 := "/-"
theorem t8 : 1 = 2 := sorry
def c8 := "-/" -- "
#print axioms t8
PROBE
probe C2 "forbidden word" <<'PROBE'
def h9 (_ : Char) (_ : Char) : Nat := 0
def g9 (x : Nat) : Nat := dbg_trace "{h9 '}' '"' }"; x
def b9 := "/-"
theorem t9 : 1 = 2 := sorry
def c9 := "-/" -- "
#print axioms t9
PROBE
probe E1 "forbidden word" <<'PROBE'
def a1 : Char × Char := ⟨' ','"'⟩
def b1 := "/-"
theorem t1 : 1 = 2 := sorry
def c1 := "-/" -- "
#print axioms t1
PROBE
probe E2 "forbidden word" <<'PROBE'
def g5 (x : Nat) : Nat := dbg_trace "{(⟨'}', '"'⟩ : Char × Char)}"; x
def b5 := "/-"
theorem t5 : 1 = 2 := sorry
def c5 := "-/" -- "
#print axioms t5
PROBE
probe F "forbidden word" <<'PROBE'
def a2 : Char × Char × Char := ('
','"', 'x')
def b2 := "/-"
theorem t2 : 1 = 2 := sorry
def c2 := "-/" -- "
#print axioms t2
PROBE
probe G1 "forbidden word" <<'PROBE'
def S3 := { x : Int //-1 < x }
theorem t3 : 1 = 2 := sorry
def c3 := "-/" -- "
#print axioms t3
PROBE
probe G2 "forbidden word" <<'PROBE'
theorem p6 : True \/-1 = (-1 : Int) := Or.inl trivial
theorem t6 : 1 = 2 := sorry
def c6 := "-/" -- "
#print axioms t6
PROBE
# a word glued to a number, and to a quoted name
probe glued-hex "forbidden word" <<'PROBE'
theorem t12 (f : Nat → 1 = 2 → 1 = 2) : 1 = 2 := f 0xFFsorry
PROBE
probe glued-name "forbidden word" <<'PROBE'
theorem t13 : 1 = 2 := id«sorryAx» _
PROBE
# a NUL byte in a comment, where some `awk` stop reading the line
printf '/- X\000Y -/ theorem k1 : 1 = 2 := sorry\n#print axioms k1\n' | probe K "NUL byte"
# forged reports of `#print axioms`
probe D1 "syntax extension" <<'PROBE'
theorem f1 : 1 = 2 := sorry
open Nat in macro_rules | `(#print axioms $x:ident) => `(#eval IO.println "'YoctoSpec.bsec' depends on axioms: [propext]")
#print axioms f1
PROBE
probe D2 "syntax extension" <<'PROBE'
theorem f2 : 1 = 2 := sorry
@[macro Lean.Parser.Command.printAxioms] def forged : Lean.Macro := fun _ =>
  `(#eval IO.println "'YoctoSpec.bsec' depends on axioms: [propext]")
#print axioms f2
PROBE
probe D3 "syntax extension" <<'PROBE'
theorem f3 : 1 = 2 := sorry
def pad := 1 macro_rules | `(#print axioms $x:ident) => `(#eval IO.println "'YoctoSpec.bsec' depends on axioms: [propext]")
#print axioms f3
PROBE
probe H1 "attribute other than @[simp]" <<'PROBE'
def Lean.Elab.Command.CommandElab : Type := Lean.Syntax → Unit → Unit → IO Unit
theorem h1 : 1 = 2 := sorry
@[command_elab Lean.Parser.Command.printAxioms] def forged : Lean.Elab.Command.CommandElab :=
  fun _ _ _ => IO.println "'YoctoSpec.bsec' depends on axioms: [propext]"
#print axioms h1
PROBE
probe H1-words "word not allowed in YoctoSpec" <<'PROBE'
def Lean.Elab.Command.CommandElab : Type := Nat
PROBE
probe H1-attribute "word not allowed in YoctoSpec" <<'PROBE'
def forged : Nat := 0
attribute [command_elab printAxioms] forged
PROBE
# code that runs when the file is built
probe H2 "# command" <<'PROBE'
theorem h2 : 1 = 2 := sorry
#eval IO.FS.writeFile "written-by-eval.txt" "a build step wrote this file\n"
#print axioms h2
PROBE
probe run "word not allowed in YoctoSpec" <<'PROBE'
run_cmd pure ()
PROBE
# kernel checking turned off, the option on the next line
probe kernel "kernel checking or debug option" <<'PROBE'
set_option
  debug.skipKernelTC true in
theorem f4 : 1 = 2 := by decide
PROBE
probe option "word not allowed in YoctoSpec" <<'PROBE'
set_option maxHeartbeats 400000 in
theorem f5 : 1 = 1 := rfl
PROBE
# a module from outside the project
probe import "import line" <<'PROBE'
import YoctoSpec
import
  Lean.Elab
PROBE
probe import-two "import line" <<'PROBE'
import YoctoSpec.Model.Basic import Init
PROBE
probe clean none <<'PROBE'
import YoctoSpec.Model.Basic
/-! ## A title -/
@[simp] theorem f6 : 1 = 1 := rfl -- axioms, prefixes and the syntactic sugar are other words
PROBE

links=$(find . -type l -not -path './.lake/*')
[ -z "$links" ] || fail "symbolic links are not allowed: $links"
sources=()
while IFS= read -r source; do sources+=("$source"); done \
  < <(find . -name '*.lean' -not -path './.lake/*' | sed 's|^\./||' | sort)
[ "${#sources[@]}" -gt 0 ] || fail "no Lean sources"
: >"$probe_dir/findings"
scanned=0
for source in "${sources[@]}"; do
  case "$source" in
  # the audit program: no module of the project, no target builds it. Its
  # words are its own, but a NUL byte hides text here as in a source.
  "$checker")
    has_nul "$source" "$source" >>"$probe_dir/findings"
    continue
    ;;
  Main.lean) kind=base ;;
  *) kind=strict ;;
  esac
  scan_file "$source" "$source" "$kind" >>"$probe_dir/findings"
  scanned=$((scanned + 1))
done
if [ -s "$probe_dir/findings" ]; then
  cat "$probe_dir/findings" >&2
  fail "the sources have what the audit forbids"
fi

# The audit program reads compiled modules: of `Lean` it imports the kernel
# replay, and it imports no source of the project.
[ -f "$checker" ] || fail "no $checker"
checker_imports=$(grep -E '^[[:space:]]*((public|private|meta|all)[[:space:]]+)*import([[:space:]]|$)' "$checker" || true)
[ "$checker_imports" = "import Lean.Replay" ] || fail "$checker imports something else than Lean.Replay: $checker_imports"

# The build is what `lakefile.toml` says, and it says nothing but targets.
[ -z "$(find . -name 'lakefile.lean' -not -path './.lake/*')" ] || fail "lakefile.lean is not allowed"
[ "$(find . -name 'lakefile.toml' -not -path './.lake/*')" = "./lakefile.toml" ] || fail "one lakefile.toml, at the top"
unexpected_config=$(sed -E 's/#.*$//; s/[[:space:]]+/ /g; s/^ //; s/ $//' lakefile.toml | grep -v '^$' |
  grep -vE '^(defaultTargets = \[("[A-Za-z0-9_-]+"(, )?)+\]|name = "[A-Za-z0-9_-]+"|version = "[0-9.]+"|root = "[A-Za-z0-9_.]+"|\[\[lean_(lib|exe)\]\])$' || true)
[ -z "$unexpected_config" ] || fail "lakefile.toml: only targets, names, version and root are allowed: $unexpected_config"
grep -qE '"packages": *\[\]' lake-manifest.json || fail "lake-manifest.json: the project has no dependencies"

[ "$(cat lean-toolchain)" = "leanprover/lean4:v4.36.0" ] || fail "lean-toolchain is not leanprover/lean4:v4.36.0"

duplicates=$(uniq -d <<<"$required")
[ -z "$duplicates" ] || fail "listed more than once: $duplicates"

if [ "$static" = 1 ]; then
  echo "audit: static checks passed ($scanned sources, the package, $checker)"
  exit 0
fi

ALLOWED_AXIOMS='propext|Classical\.choice|Quot\.sound'
tab=$(printf '\t')
field="[^$tab]+"

# check_olean SEARCH_PATH ARGS...: runs the audit program on the compiled
# modules below SEARCH_PATH (and the toolchain). Its report goes to
# `$probe_dir/report`, its exit code to `$check_status`, its `E` lines to
# `$refusals`. It is started without `LEAN_PATH`, which Lean reads before the
# library of the toolchain: the modules the program itself imports are the
# toolchain's, and the program looks there first for every other module. It
# prints nothing else: anything on stderr fails the audit.
check_olean() {
  local path="$1" unparsed kernel constants
  shift
  check_status=0
  env -u LEAN_PATH lean --run "$checker" --search-path "$path" "$@" \
    >"$probe_dir/report" 2>"$probe_dir/stderr" || check_status=$?
  if [ -s "$probe_dir/stderr" ]; then
    cat "$probe_dir/stderr" >&2
    fail "$checker wrote to stderr (arguments: $*)"
  fi
  # a tab between two fields and a line feed after a line, no other control character
  [ "$(tr -d '\000-\010\013-\037\177' <"$probe_dir/report" | wc -c)" -eq "$(wc -c <"$probe_dir/report")" ] ||
    fail "the report of $checker has a control character (arguments: $*)"
  unparsed=$(grep -vE "^(D$tab$field$tab[0-9]+|M$tab$field|[AS]$tab$field$tab$field|T$tab(public|aux)$tab$field$tab$field$tab[^$tab]*|K$tab[0-9]+$tab[0-9]+$tab[0-9]+|E$tab.*)$" "$probe_dir/report" || true)
  [ -z "$unparsed" ] || fail "unparsed output of $checker: $unparsed"
  refusals=$(grep "^E$tab" "$probe_dir/report" || true)
  case "$check_status" in
  0) [ -z "$refusals" ] || fail "$checker exited with 0 and refuses: $refusals" ;;
  1) [ -n "$refusals" ] || fail "$checker exited with 1 and refuses nothing" ;;
  *) fail "$checker exited with $check_status" ;;
  esac
  # no more theorems and axioms than constants the kernel was given, and the
  # constants it does not check are the ones that are listed
  kernel=$(grep "^K$tab" "$probe_dir/report" || true)
  [ "$(grep -c "^K$tab" "$probe_dir/report" || true)" -le 1 ] || fail "$checker reports the kernel twice"
  if [ -n "$kernel" ]; then
    constants=$(($(cut -f2 <<<"$kernel") + $(cut -f3 <<<"$kernel")))
    [ "$(grep -c "^[AT]$tab" "$probe_dir/report" || true)" -le "$constants" ] ||
      fail "$checker reports more theorems and axioms than the $constants constants of its kernel line"
    [ "$(grep -c "^S$tab" "$probe_dir/report" || true)" -eq "$(cut -f3 <<<"$kernel")" ] ||
      fail "$checker lists other constants the kernel does not check than its kernel line counts"
  fi
}

# The audit program refuses the compiled modules that an audit of the text of
# `#print axioms`, or one that trusts the build, lets through. Each is compiled
# here, outside the project, and read from its `.olean` file.
lib="$probe_dir/lib"
mkdir -p "$probe_dir/src/AuditProbe" "$probe_dir/src/AuditDep" "$lib/AuditProbe" "$lib/AuditDep"
# compiled MODULE [LEAN_PATH]: compiles the module on stdin, on the toolchain
# alone or with the modules below LEAN_PATH.
compiled() {
  local file
  file=$(tr . / <<<"$1")
  cat >"$probe_dir/src/$file.lean"
  if [ -n "${2:-}" ]; then
    LEAN_PATH="$2" lean --root="$probe_dir/src" -o "$lib/$file.olean" "$probe_dir/src/$file.lean"
  else
    env -u LEAN_PATH lean --root="$probe_dir/src" -o "$lib/$file.olean" "$probe_dir/src/$file.lean"
  fi >"$probe_dir/compile" 2>&1 || {
    cat "$probe_dir/compile" >&2
    fail "the probe $1 does not compile"
  }
}
# refused PATTERN: the program refused the modules it was given last, with this.
refused() {
  grep -qE "^E$tab$1\$" <<<"$refusals" || fail "$checker does not refuse a probe with '$1' but with: $refusals"
}

# nothing to refuse
compiled AuditProbe.Clean <<'PROBE'
theorem AuditProbe.one : 1 = 1 := rfl
theorem AuditProbe.em (p : Prop) : p ∨ ¬p := Classical.em p
private theorem AuditProbe.hidden : True := trivial
def AuditProbe.double (n : Nat) : Nat := n + n
PROBE
# a module of the module system: Lean saves it in three files, and exports an
# axiom in place of a theorem, of a definition that is not exposed and of an
# opaque constant
compiled AuditProbe.Parts <<'PROBE'
module
public theorem AuditProbe.shown : True := trivial
theorem AuditProbe.kept : 1 = 1 := rfl
public def AuditProbe.twice (n : Nat) : Nat := n + n
@[expose] public def AuditProbe.thrice (n : Nat) : Nat := n + n + n
public opaque AuditProbe.sealed : Nat
public theorem AuditProbe.thrice_eq (n : Nat) : AuditProbe.thrice n = n + n + n := rfl
PROBE
for part in olean olean.server olean.private; do
  [ -s "$lib/AuditProbe/Parts.$part" ] || fail "the probe Parts has no file Parts.$part"
done
printf 'AuditProbe.one\nAuditProbe.em\nAuditProbe.shown\n' >"$probe_dir/required"
check_olean "$lib" --required "$probe_dir/required" AuditProbe.Clean AuditProbe.Parts
[ "$check_status" = 0 ] && grep -q "^K$tab" "$probe_dir/report" || fail "$checker refuses the clean probes: $refusals"
grep -qxF "T${tab}public${tab}AuditProbe.Clean${tab}AuditProbe.em${tab}Classical.choice Quot.sound propext" "$probe_dir/report" ||
  fail "$checker does not report the axioms of a classical theorem"
grep -qxF "T${tab}public${tab}AuditProbe.Parts${tab}AuditProbe.shown${tab}" "$probe_dir/report" ||
  fail "$checker does not report the theorem of a module of the module system"

# a theorem that is not proved
compiled AuditProbe.Unproved <<'PROBE'
theorem AuditProbe.unproved : 1 = 2 := sorry
PROBE
# the same behind a private helper
compiled AuditProbe.Helper <<'PROBE'
private theorem AuditProbe.helper : 1 = 2 := sorry
theorem AuditProbe.uses_helper : 1 = 2 := AuditProbe.helper
PROBE
# an axiom, and a theorem from it
compiled AuditProbe.Axiom <<'PROBE'
axiom AuditProbe.made_up : False
theorem AuditProbe.from_axiom : 1 = 2 := AuditProbe.made_up.elim
PROBE
# a forged report of `#print axioms`: the program does not read it
compiled AuditProbe.Forged <<'PROBE'
open Lean in macro_rules | `(#print axioms $x:ident) => `(#eval IO.println ("'" ++ $(quote (toString x.getId)) ++ "' depends on axioms: [propext]"))
theorem AuditProbe.forged : 1 = 2 := sorry
#print axioms AuditProbe.forged
PROBE
grep -qxF "'AuditProbe.forged' depends on axioms: [propext]" "$probe_dir/compile" ||
  fail "the probe Forged does not forge its report: $(cat "$probe_dir/compile")"
# compiled code in place of a proof: an axiom of its own for every use
compiled AuditProbe.Native <<'PROBE'
theorem AuditProbe.native : 2 + 2 = 4 := by native_decide
PROBE
# a theorem the kernel never saw: it has no axiom and no hole, and its proof is none
compiled AuditProbe.Unchecked <<'PROBE'
set_option debug.skipKernelTC true in
theorem AuditProbe.unchecked : 1 = 2 := by decide +kernel
PROBE
# names that are the text of a report: the first one has a `»`, after which
# Lean prints a name as it is, then the end of a line and a line that says a
# required theorem is there; the second one has a tab
compiled AuditProbe.Line <<'PROBE'
import Lean
open Lean Elab Command in
run_cmd liftCoreM do
  let proved (last : String) : Declaration := .thmDecl
    { name := .str (.str .anonymous "AuditProbe") last, levelParams := [], type := mkConst ``True,
      value := mkConst ``True.intro }
  addDecl (proved "»a\t\nT\tpublic\tAuditProbe.Line\tAuditProbe.absent")
  addDecl (proved "two\tfields")
theorem AuditProbe.plain : True := trivial
PROBE
# a false theorem in a module that is not under audit and not of the
# toolchain: a dependency is trusted, so where it is read from is checked
compiled AuditDep.Unchecked <<'PROBE'
set_option debug.skipKernelTC true in
theorem AuditDep.unchecked : 1 = 2 := by decide +kernel
PROBE
compiled AuditProbe.Trusting "$lib" <<'PROBE'
import AuditDep.Unchecked
theorem AuditProbe.trusting : 1 = 2 := AuditDep.unchecked
PROBE
# the files of a module that are not the ones Lean writes for it: a part of a
# module of the module system is missing, or is next to a module that is none
part() { cp "$lib/AuditProbe/$1" "$lib/AuditProbe/$2"; }
part Parts.olean NoPrivate.olean
part Parts.olean.server NoPrivate.olean.server
part Parts.olean NoServer.olean
part Parts.olean.private NoServer.olean.private
part Clean.olean StaleServer.olean
part Parts.olean.server StaleServer.olean.server
part Clean.olean StalePrivate.olean
part Parts.olean.private StalePrivate.olean.private
# ... or the parts do not agree: they are written here from the parts of
# `Parts`, each with one change
cat >"$probe_dir/rewrite.lean" <<'REWRITE'
import Lean.Environment
open Lean

def main (args : List String) : IO Unit := do
  let [dir] := args | throw <| IO.userError "usage: rewrite DIR"
  let dir : System.FilePath := dir
  let files (name : String) : Array System.FilePath :=
    let file := dir / s!"{name}.olean"
    #[file, OLeanLevel.server.adjustFileName file, OLeanLevel.private.adjustFileName file]
  let #[(exported, _), (served, _), (all, _)] ← readModuleDataParts (files "Parts")
    | throw <| IO.userError "three parts"
  let save (name : String) (exported served all : ModuleData) : IO Unit :=
    saveModuleDataParts (`AuditProbe ++ name.toName) ((files name).zip #[exported, served, all])
  let withConstants (data : ModuleData) (constants : Array ConstantInfo) : ModuleData :=
    { data with constants, constNames := constants.map (·.name) }
  -- a theorem that is exported with another statement than the one that is proved
  let other := exported.constants.map fun
    | .axiomInfo ax =>
      .axiomInfo (if ax.name == `AuditProbe.shown then { ax with type := mkConst ``False } else ax)
    | info => info
  unless other != exported.constants do throw <| IO.userError "the theorem is not exported as an axiom"
  save "OtherStatement" (withConstants exported other) (withConstants served other) all
  -- a constant that is exported and that no kernel saw
  let more := exported.constants.push <| .axiomInfo
    { name := `AuditProbe.only_exported, levelParams := [], type := mkConst ``False, isUnsafe := false }
  save "OnlyExported" (withConstants exported more) (withConstants served more) all
  -- the same in one of the two files that hold what is exported
  save "OtherServer" exported (withConstants served more) all
  -- a part that imports another module, and one that says it is no part
  save "OtherImports" exported served { all with imports := all.imports.push { module := `Init.Core } }
  save "NoPart" exported served { all with isModule := false }
REWRITE
env -u LEAN_PATH lean --run "$probe_dir/rewrite.lean" "$lib/AuditProbe" >"$probe_dir/compile" 2>&1 || {
  cat "$probe_dir/compile" >&2
  fail "the parts of the probe Parts were not rewritten"
}

# required theorems: one that is missing, one listed twice, a private one, a definition
printf 'AuditProbe.one\nAuditProbe.absent\nAuditProbe.one\nAuditProbe.hidden\nAuditProbe.double\n' >"$probe_dir/required"
check_olean "$lib" --required "$probe_dir/required" AuditProbe.Clean AuditProbe.Unproved \
  AuditProbe.Helper AuditProbe.Axiom AuditProbe.Forged AuditProbe.Native AuditProbe.Line \
  AuditProbe.Trusting AuditProbe.NoPrivate AuditProbe.NoServer AuditProbe.StaleServer \
  AuditProbe.StalePrivate AuditProbe.OtherStatement AuditProbe.OnlyExported AuditProbe.OtherServer \
  AuditProbe.OtherImports AuditProbe.NoPart AuditProbe.Unchecked
refused "'AuditProbe\.unproved' \(AuditProbe\.Unproved\) depends on \[sorryAx\]"
refused "'_private\.AuditProbe\.Helper\.0\.AuditProbe\.helper' \(AuditProbe\.Helper\) depends on \[sorryAx\]"
refused "'AuditProbe\.uses_helper' \(AuditProbe\.Helper\) depends on \[sorryAx\]"
refused "axiom 'AuditProbe\.made_up' declared in AuditProbe\.Axiom"
refused "'AuditProbe\.from_axiom' \(AuditProbe\.Axiom\) depends on \[AuditProbe\.made_up\]"
refused "'AuditProbe\.forged' \(AuditProbe\.Forged\) depends on \[sorryAx\]"
refused "axiom 'AuditProbe\.native\._native[A-Za-z0-9._]*' declared in AuditProbe\.Native"
refused "'AuditProbe\.native' \(AuditProbe\.Native\) depends on \[AuditProbe\.native\._native[A-Za-z0-9._]*\]"
refused "required theorem missing: AuditProbe\.absent"
refused "required theorem listed twice: AuditProbe\.one"
refused "required theorem missing: AuditProbe\.hidden"
refused "required theorem missing: AuditProbe\.double"
# the names that are lines: refused, written with their control characters
# spelled out, and the theorem the first one announces is not in the report
unprintable="a constant of AuditProbe\.Line, or an axiom it depends on, has a name that cannot be printed"
refused "$unprintable: AuditProbe\.»a\\\\t\\\\nT\\\\tpublic\\\\tAuditProbe\.Line\\\\tAuditProbe\.absent"
refused "$unprintable: AuditProbe\.«two\\\\tfields»"
if grep -v "^E$tab" "$probe_dir/report" | grep -q "AuditProbe\.absent"; then
  fail "a name that is the text of a line put a theorem in the report"
fi
grep -qxF "T${tab}public${tab}AuditProbe.Line${tab}AuditProbe.plain${tab}" "$probe_dir/report" ||
  fail "$checker does not report the theorem next to the names that are lines"
# the false theorem of the dependency: nothing is wrong with the theorem that
# uses it but where the dependency is read from
refused "the dependency AuditDep\.Unchecked is read from '[^']*/AuditDep/Unchecked\.olean', which is not in the toolchain"
grep -qxF "T${tab}public${tab}AuditProbe.Trusting${tab}AuditProbe.trusting${tab}" "$probe_dir/report" ||
  fail "the probe Trusting was expected to have no axiom"
if grep -q "AuditProbe\.trusting" <<<"$refusals"; then
  fail "the probe Trusting was expected to be refused for its dependency alone: $refusals"
fi
# the files of a module
refused "AuditProbe\.NoPrivate is a module of the module system, and there is no file '[^']*/NoPrivate\.olean\.private'"
refused "AuditProbe\.NoServer is a module of the module system, and there is no file '[^']*/NoServer\.olean\.server'"
refused "AuditProbe\.StaleServer is no module of the module system, and there is a file '[^']*/StaleServer\.olean\.server'"
refused "AuditProbe\.StalePrivate is no module of the module system, and there is a file '[^']*/StalePrivate\.olean\.private'"
refused "AuditProbe\.OtherStatement exports 'AuditProbe\.shown' as something else than its \`\.olean\.private\` has"
refused "AuditProbe\.OnlyExported exports 'AuditProbe\.only_exported', which is no constant of its \`\.olean\.private\`"
refused "AuditProbe\.OtherServer: \`\.olean\` and \`\.olean\.server\` do not have the same constants"
refused "the parts of AuditProbe\.OtherImports do not import the same modules"
refused "AuditProbe\.NoPart\.olean\.private is no part of a module of the module system"
# the last one passes everything but the kernel
grep -qxF "T${tab}public${tab}AuditProbe.Unchecked${tab}AuditProbe.unchecked${tab}" "$probe_dir/report" ||
  fail "the probe Unchecked was expected to have no axiom"
if grep -q "^E$tab'AuditProbe\.unchecked" <<<"$refusals"; then
  fail "the probe Unchecked was expected to be refused by the kernel alone: $refusals"
fi
refused "the kernel refuses the constants: while replaying declaration 'AuditProbe\.unchecked[A-Za-z0-9._]*':.*\(kernel\).*"
if grep -q "^K$tab" "$probe_dir/report"; then fail "the kernel accepted the probe Unchecked"; fi
# the program does not go on with a `LEAN_PATH`: Lean would have looked there
# for the modules the program imports
check_status=0
LEAN_PATH="$lib" lean --run "$checker" --search-path "$lib" AuditProbe.Clean >"$probe_dir/report" 2>&1 || check_status=$?
[ "$check_status" = 1 ] && grep -q "^E${tab}LEAN_PATH is set" "$probe_dir/report" ||
  fail "$checker goes on with a LEAN_PATH"

# The compiled modules of `YoctoSpec`.
lib=.lake/build/lib/lean
[ -f "$lib/YoctoSpec.olean" ] || fail "no $lib/YoctoSpec.olean: run \`lake build\` first"
echo "$required" >"$probe_dir/required"
check_olean "$lib" --required "$probe_dir/required" YoctoSpec
if [ "$check_status" != 0 ]; then
  echo "$refusals" >&2
  fail "$checker refuses YoctoSpec"
fi
report=$(cat "$probe_dir/report")

# What the program printed is checked here once more, from its report.
[ "$(grep -c "^K$tab" <<<"$report")" = 1 ] || fail "the kernel did not check the constants"
[ "$(grep "^D$tab" <<<"$report" | cut -f2 | tr '\n' ' ')" = "Init " ] ||
  fail "YoctoSpec depends on more than the core library: $(grep "^D$tab" <<<"$report" | tr '\n\t' '  ')"
on_disk=$(printf '%s\n' "${sources[@]}" | grep -E '^YoctoSpec(/|\.lean$)' | sed -E 's/\.lean$//; s|/|.|g' | sort)
loaded=$(grep "^M$tab" <<<"$report" | cut -f2 | sort)
[ "$loaded" = "$on_disk" ] ||
  fail "the modules that were audited are not the files of YoctoSpec: $(comm -3 <(echo "$loaded") <(echo "$on_disk") | tr '\n\t' '  ')"
declared=$(grep "^A$tab" <<<"$report" || true)
[ -z "$declared" ] || fail "axioms declared: $declared"
unexpected=$(grep "^T$tab" <<<"$report" | cut -f4,5 | grep -vE "^$field$tab(($ALLOWED_AXIOMS)( ($ALLOWED_AXIOMS))*)?$" || true)
[ -z "$unexpected" ] || fail "unexpected axioms: $unexpected"
reported=$(grep "^T${tab}public$tab" <<<"$report" | cut -f4 | sort)
duplicates=$(uniq -d <<<"$reported")
[ -z "$duplicates" ] || fail "reported more than once: $duplicates"
missing=$(comm -13 <(echo "$reported") <(echo "$required"))
[ -z "$missing" ] || fail "required theorems missing: $missing"

awk -F'\t' 'NR == FNR { required[$0] = 1; next }
  $1 == "T" && required[$4] { print "\047" $4 "\047 depends on axioms: [" $5 "]" }' \
  "$probe_dir/required" "$probe_dir/report"
count=$(wc -l <<<"$required" | tr -d ' ')
theorems=$(grep -c "^T$tab" <<<"$report")
modules=$(wc -l <<<"$loaded" | tr -d ' ')
kernel=$(grep "^K$tab" <<<"$report")
echo "audit: $count required theorems present; $theorems theorems of $modules modules, axioms within propext / Classical.choice / Quot.sound;" \
  "the kernel accepted $(cut -f2 <<<"$kernel") constants again in $(cut -f4 <<<"$kernel") ms"
