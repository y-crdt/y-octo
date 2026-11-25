import Lean.Replay

/-!
The audit of compiled modules. It reads `.olean` files and nothing else of the
project under audit: this file imports `Lean` only, so no source of the project
is elaborated here and none of its syntax, attributes or environment extensions
can change what the audit does or prints. (Of `Lean` it imports `Lean.Replay`,
the kernel replay with what that builds on, and not all of it: the modules it
imports are loaded a second time when a project under audit depends on them,
and the whole library costs 1.7 GiB of memory more.) It is run by `audit.sh` (for
`YoctoSpec`) and by `proofs/scripts/audit.py` (for `YoctoCore` and `YoctoSpec`),
is no part of `YoctoSpec` and is built by no target; like the two scripts it is
reviewed in the diff.

    env -u LEAN_PATH lean --run check_olean.lean [--search-path PATH]...
        [--dependency-path DIR]... [--audit ROOT]... [--required FILE] MODULE...

It is started without `LEAN_PATH`, which Lean reads before the library of the
toolchain: with it, the `import` above could be answered by a file of the
project. The program refuses to go on when the variable is set. Where the
modules are comes as an argument: they are looked up in the library of the
toolchain first, then in every PATH (directories separated by `:`), in order.

The modules under audit are the ones that MODULE... import, directly or not,
whose first name component is the one of a MODULE or a ROOT. Every other module
they import is trusted: a dependency.

1. The `.olean` files of the modules under audit are read as data
   (`readModuleData`, `readModuleDataParts`). Their initializers and environment
   extensions are not run. The dependencies are imported with
   `loadExts := false`, which does not run theirs either.
2. A module is saved in one file, or, when it is a module of the module system
   (`isModule`), in three: `.olean` (what it exports), `.olean.server` and
   `.olean.private` (every constant of the kernel). Which of the two it is, is
   what the first file says, not which files there are. A module that is none
   has no `.olean.server` and no `.olean.private` next to it; a module that is
   one has both, and
   - the three parts say `isModule` and import the same modules;
   - `.olean` and `.olean.server` have the same constants;
   - every constant of `.olean` is a constant of `.olean.private`: the same
     one, or the axiom Lean exports in place of a theorem, a definition or an
     opaque constant (same name, universe parameters and type).
   The constants of `.olean.private` are the ones that are audited. In every
   part a constant is filed under its name, once.
3. Every file of a dependency (its `.olean`, and the `.olean.server` and
   `.olean.private` next to it) is, with symbolic links resolved, in the
   library of the toolchain or below a DIR. Without `--dependency-path` the
   dependencies are modules of the toolchain.
4. No constant of a module under audit is declared a second time, by another
   module under audit or by a dependency. The one exception is the one Lean
   makes when it imports modules: a theorem may be proved again, with the same
   statement (Lean proves the equation lemmas of a function in the module that
   first uses them, so two modules may each hold one). Such a second proof is
   audited as a theorem of its own, under the name `<name>._again.<n>`: its
   axioms are computed and the kernel checks it like every other constant.
5. For every constant of a module under audit, of any kind, the axioms it
   depends on are computed from the declarations (types, values, constructors),
   through the dependencies as well. Only `propext`, `Classical.choice` and
   `Quot.sound` are allowed, and they have to be the ones of the toolchain. A
   module under audit declares no axiom.
6. Every constant of the modules under audit is sent to the kernel again
   (`Lean.Kernel.Environment.replay`), in an environment that holds the
   dependencies only. The environment the kernel builds then holds every one
   of these constants as the file has it. So a constant of these files is one
   the kernel of this toolchain accepts on top of the dependencies: a
   declaration that was added without a kernel check (`debug.skipKernelTC`),
   or one that was changed in the file into something the kernel does not
   accept, is refused here.
7. With `--required FILE`, every name in FILE (one a line) is a theorem of a
   module under audit, under a name others can use, and no name is listed
   twice. Names are compared as names, not as text.
8. No name that is printed (a module, a constant, an axiom) has a control
   character, a line separator or a `»` in it (`Name.toString` does not quote
   a component with a `»`, so such a name could be printed as the text of
   another line), no two constants are printed alike, and the name of a
   theorem others can use reads back from its text as the same name.

What this does not decide:
- that the files are what the sources compile to (that is Lake's, in the build
  before the audit), or that a file was not replaced by another one whose
  constants the kernel accepts as well: what a theorem says is read from the
  source;
- anything in a file but its imports and its constants (the entries of
  environment extensions, the compiled code);
- that Lean reads a file right. The files are mapped into memory by Lean
  (`CompactedRegion`), which trusts their layout: a file that is no output of
  Lean can make the program crash, which fails the audit, or misread it.
- the dependencies, which are trusted as they are on disk in the places above.

Output, on stdout, fields separated by tabs:

    D <root> <modules>              the dependencies, by first name component
    M <module>                      a module under audit
    A <module> <name>               an axiom it declares
    T <kind> <module> <name> <axioms>
                                    a theorem and the axioms it depends on,
                                    separated by spaces; kind is `public`, or
                                    `aux` for a private or generated one
    S <module> <name>               an unsafe or partial constant: the kernel
                                    does not check these, and refuses a theorem
                                    that refers to one
    K <constants> <skipped> <ms>    the kernel accepted the constants, but the
                                    skipped ones (the `S` lines)
    E <what>                        something the audit refuses; a control
                                    character in it is written as `\n`, `\t`,
                                    `\r` or `\u{..}`, a `\` as `\\`

The exit code is 0 when there is no `E` line, 1 otherwise. The other lines are
printed in both cases; the `A`, `M`, `S` and `T` lines are sorted. No field of
them has a tab or another control character in it: a line that would is an `E`
line instead.
-/

open Lean

namespace CheckOlean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

structure Config where
  entries : Array Name := #[]
  roots : Array Name := #[]
  required : Option System.FilePath := none
  searchPath : System.SearchPath := []
  dependencyPaths : Array System.FilePath := #[]

def usage : String :=
  "usage: env -u LEAN_PATH lean --run check_olean.lean [--search-path PATH]... [--dependency-path DIR]... [--audit ROOT]... [--required FILE] MODULE..."

def parseName (s : String) : IO Name := do
  let name := s.toName
  if name.isAnonymous then
    throw <| IO.userError s!"not a name: '{s}'"
  return name

def parseArgs (cfg : Config) : List String → IO Config
  | [] => do
    if cfg.entries.isEmpty then
      throw <| IO.userError usage
    return cfg
  | "--search-path" :: path :: rest =>
    parseArgs { cfg with searchPath := cfg.searchPath ++ System.SearchPath.parse path } rest
  | "--dependency-path" :: dir :: rest =>
    parseArgs { cfg with dependencyPaths := cfg.dependencyPaths.push dir } rest
  | "--audit" :: root :: rest => do
    parseArgs { cfg with roots := cfg.roots.push (← parseName root) } rest
  | "--required" :: file :: rest => parseArgs { cfg with required := some file } rest
  | arg :: rest => do
    if arg.startsWith "-" then
      throw <| IO.userError s!"unknown option '{arg}'\n{usage}"
    let name ← parseName arg
    parseArgs { cfg with entries := cfg.entries.push name, roots := cfg.roots.push name.getRoot } rest

/-- A character no field of the report may have: a control character (tab, line
feed and carriage return among them), a line or paragraph separator, or the `»`
that ends a quoted name component. -/
def refusedChar (c : Char) : Bool :=
  c.val < 0x20 || (0x7f ≤ c.val && c.val < 0xa0) || c.val == 0x2028 || c.val == 0x2029 || c == '»'

def printable : Name → Bool
  | .anonymous => true
  | .str p s => !s.any refusedChar && printable p
  | .num p _ => printable p

/-- The text of an `E` line: no character of it ends the line or the field. -/
def escaped (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c == '\\' then out := out ++ "\\\\"
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\t' then out := out ++ "\\t"
    else if c == '\r' then out := out ++ "\\r"
    else if refusedChar c && c != '»' then
      out := (Nat.toDigits 16 c.toNat).foldl (·.push ·) (out ++ "\\u{") ++ "}"
    else out := out.push c
  return out

/-- A module under audit: its imports and every constant of the kernel it
declares. -/
structure Audited where
  name : Name
  imports : Array Name
  constants : Array (Name × ConstantInfo)

/-- What is wrong with the constant table of a part: a constant is filed under
its name, once. -/
def tableProblems (what : String) (data : ModuleData) : Array String := Id.run do
  if data.constNames.size != data.constants.size then
    return #[s!"{what}: {data.constNames.size} names for {data.constants.size} constants"]
  let mut problems := #[]
  let mut seen : NameSet := {}
  for name in data.constNames, info in data.constants do
    if name != info.name then
      problems := problems.push s!"{what}: the constant {info.name} is filed under {name}"
    if seen.contains name then
      problems := problems.push s!"{what}: '{name}' is there twice"
    seen := seen.insert name
  return problems

/-- What a module of the module system exports of a constant: the constant, or
an axiom with its name, universe parameters and type in place of a theorem, of
a definition whose body is not exposed, or of an opaque constant (`addDecl`). -/
def exportedOf («public» all : ConstantInfo) : Bool :=
  «public» == all ||
    match «public», all with
    | .axiomInfo ax, .thmInfo thm => ax.toConstantVal == thm.toConstantVal && !ax.isUnsafe
    | .axiomInfo ax, .defnInfo defn =>
      ax.toConstantVal == defn.toConstantVal && ax.isUnsafe == (defn.safety != .safe)
    | .axiomInfo ax, .opaqueInfo op => ax.toConstantVal == op.toConstantVal && ax.isUnsafe == op.isUnsafe
    | _, _ => false

/-- The files a module is saved in next to its `.olean`, where they exist. -/
def sideFiles (file : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  for side in [OLeanLevel.server.adjustFileName file, OLeanLevel.private.adjustFileName file] do
    if ← side.pathExists then
      files := files.push side
  return files

/-- Reads a module under audit, with what is wrong with its files. Without the
module when its constants cannot be read whole. -/
def readAudited (name : Name) : IO (Option Audited × Array String) := do
  let file ← findOLean name
  unless ← file.pathExists do
    return (none, #[s!"no file '{file}' for the module {name}"])
  let server := OLeanLevel.server.adjustFileName file
  let «private» := OLeanLevel.private.adjustFileName file
  let (main, _) ← readModuleData file
  let audited (data : ModuleData) : Audited :=
    { name, imports := data.imports.map (·.module), constants := data.constNames.zip data.constants }
  let mut problems := #[]
  unless main.isModule do
    -- one file; a part next to it is left of another build, and Lean does not read it
    for side in ← sideFiles file do
      problems := problems.push
        s!"{name} is no module of the module system, and there is a file '{side}'"
    return (some (audited main), problems ++ tableProblems s!"{name}" main)
  for side in [server, «private»] do
    unless ← side.pathExists do
      problems := problems.push s!"{name} is a module of the module system, and there is no file '{side}'"
  unless problems.isEmpty do
    return (none, problems)
  let parts ← readModuleDataParts #[file, server, «private»]
  let #[(exported, _), (served, _), (all, _)] := parts
    | return (none, #[s!"{name}: {parts.size} parts were read"])
  for (part, data) in [("olean", exported), ("olean.server", served), ("olean.private", all)] do
    unless data.isModule do
      problems := problems.push s!"{name}.{part} is no part of a module of the module system"
    problems := problems ++ tableProblems s!"{name}.{part}" data
  unless exported.imports == served.imports && exported.imports == all.imports do
    problems := problems.push s!"the parts of {name} do not import the same modules"
  unless exported.constNames == served.constNames && exported.constants == served.constants do
    problems := problems.push s!"{name}: `.olean` and `.olean.server` do not have the same constants"
  let mut kernel : Std.HashMap Name ConstantInfo := {}
  for info in all.constants do
    kernel := kernel.insert info.name info
  for info in exported.constants do
    match kernel[info.name]? with
    | none =>
      problems := problems.push
        s!"{name} exports '{info.name}', which is no constant of its `.olean.private`"
    | some full =>
      unless exportedOf info full do
        problems := problems.push
          s!"{name} exports '{info.name}' as something else than its `.olean.private` has"
  return (some (audited all), problems)

/-- The modules under audit that `entries` import, the dependencies they
import, and what is wrong with the files that were read. -/
def readClosure (roots : Array Name) (entries : Array Name) :
    IO (Array Audited × Array Name × Array String) := do
  let mut audited : Array Audited := #[]
  let mut dependencies : Array Name := #[]
  let mut problems : Array String := #[]
  let mut seen : NameSet := {}
  let mut todo := entries.reverse
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    if roots.contains name.getRoot then
      let (module?, found) ← readAudited name
      problems := problems ++ found
      if let some module := module? then
        audited := audited.push module
        todo := todo ++ module.imports.reverse
    else
      dependencies := dependencies.push name
  return (audited, dependencies, problems)

def kindOf (name : Name) : String :=
  if isPrivateName name || name.isInternalDetail then "aux" else "public"

def sorted (names : Array Name) : Array String :=
  (names.map toString).qsort (· < ·)

/-- The constants `names` use, directly or not, and for each of them the bits of
the axioms it depends on: bit `i` stands for the `i`-th axiom of the answer. The
dependencies of a constant are the constants of its type and of its value; an
inductive type depends on its constructors, a recursor on its inductive types. -/
def axiomBits (find : Name → Option ConstantInfo) (names : Array Name) :
    Std.HashMap Name Nat × Array Name × Array Name := Id.run do
  let mut index : Std.HashMap Name Nat := {}
  let mut users : Array (Array Nat) := #[]
  let mut order : Array Name := #[]
  let mut axioms : Array Name := #[]
  let mut unknown : Array Name := #[]
  let mut bits : Array Nat := #[]
  -- the constants that are reached, numbered, and for each the ones that use it
  for name in names do
    unless index.contains name do
      index := index.insert name order.size
      order := order.push name
      users := users.push #[]
      bits := bits.push 0
  let mut next := 0
  while next < order.size do
    let name := order[next]!
    match find name with
    | none => unknown := unknown.push name
    | some info =>
      if info matches .axiomInfo _ then
        bits := bits.set! next (1 <<< axioms.size)
        axioms := axioms.push name
      for used in info.getUsedConstantsAsSet do
        unless index.contains used do
          index := index.insert used order.size
          order := order.push used
          users := users.push #[]
          bits := bits.push 0
        users := users.modify (index.getD used 0) (·.push next)
    next := next + 1
  -- the bits of a constant go to the constants that use it, until nothing changes
  let mut queue : Array Nat := #[]
  for i in [0:order.size] do
    if bits[i]! != 0 then
      queue := queue.push i
  while !queue.isEmpty do
    let i := queue.back!
    queue := queue.pop
    let mine := bits[i]!
    for user in users[i]! do
      let theirs := bits[user]!
      let both := theirs ||| mine
      if both != theirs then
        bits := bits.set! user both
        queue := queue.push user
  let mut answer : Std.HashMap Name Nat := {}
  for i in [0:order.size] do
    answer := answer.insert order[i]! bits[i]!
  return (answer, axioms, unknown)

def axiomsOfBits (axioms : Array Name) (bits : Nat) : Array Name := Id.run do
  let mut found := #[]
  for i in [0:axioms.size] do
    if bits &&& (1 <<< i) != 0 then
      found := found.push axioms[i]!
  return found

def run (cfg : Config) : IO UInt32 := do
  let mut errors : Array String := #[]
  -- the lines of the report but the `E` lines, as fields
  let mut lines : Array (List String) := #[]

  if (← IO.getEnv "LEAN_PATH").isSome then
    errors := errors.push "LEAN_PATH is set: the modules this program imports may not be the ones of the toolchain"
  -- the library of the toolchain first, then where the caller says the modules are
  let toolchainLib ← IO.FS.realPath (← getLibDir (← getBuildDir))
  searchPathRef.set (toolchainLib :: cfg.searchPath)
  let below (dir : System.FilePath) : String :=
    dir.toString ++ System.FilePath.pathSeparator.toString
  let toolchain := below toolchainLib
  let mut trusted := #[toolchain]
  for dir in cfg.dependencyPaths do
    trusted := trusted.push (below (← IO.FS.realPath dir))
  -- every file of the module is below one of `places`, symbolic links resolved
  let filesWithin (places : Array String) (module : Name) : IO (Option System.FilePath) := do
    let file ← findOLean module
    for part in #[file] ++ (← sideFiles file) do
      let real := (← IO.FS.realPath part).toString
      unless places.any (real.startsWith ·) do
        return some part
    return none

  let (audited, dependencies, problems) ← readClosure cfg.roots cfg.entries
  errors := errors ++ problems
  -- the dependencies, in an environment of their own
  let baseEnv ← importModules (dependencies.map ({ module := · })) {} (trustLevel := 0)
    (loadExts := false)
  let base := baseEnv.toKernelEnv
  let moduleNames := baseEnv.header.moduleNames
  let mut dependencyRoots : Std.HashMap String Nat := {}
  for module in moduleNames do
    unless printable module do
      errors := errors.push s!"the name of a dependency cannot be printed: {module}"
      continue
    let root := toString module.getRoot
    if cfg.roots.contains module.getRoot then
      errors := errors.push s!"the dependencies import {module}, a module under audit"
    dependencyRoots := dependencyRoots.insert root (dependencyRoots.getD root 0 + 1)
    if let some file ← filesWithin trusted module then
      errors := errors.push <|
        s!"the dependency {module} is read from '{file}', which is not in the toolchain"
          ++ (if cfg.dependencyPaths.isEmpty then "" else " and not below a dependency path")
  for (root, modules) in dependencyRoots.toArray.qsort (·.1 < ·.1) do
    lines := lines.push ["D", root, toString modules]
  for name in allowedAxioms do
    match base.find? name, baseEnv.getModuleIdxFor? name with
    | some (.axiomInfo _), some idx =>
      if (← filesWithin #[toolchain] moduleNames[idx.toNat]!).isSome then
        errors := errors.push s!"the axiom {name} is not the one of the toolchain"
    | _, _ => errors := errors.push s!"the axiom {name} is not declared by the toolchain"

  -- every constant of the modules under audit, once; a second proof of a
  -- theorem under a name of its own
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut declared : Array (Name × Name × ConstantInfo) := #[]
  let mut moduleOf : Std.HashMap Name Name := {}
  for module in audited.qsort (toString ·.name < toString ·.name) do
    for (name, info) in module.constants do
      let other? := moduleOf[name]? <|> (baseEnv.getModuleIdxFor? name).map (moduleNames[·.toNat]!)
      match constants[name]? <|> base.find? name, info with
      | none, _ =>
        constants := constants.insert name info
        declared := declared.push (module.name, name, info)
        moduleOf := moduleOf.insert name module.name
      | some (.thmInfo first), .thmInfo again =>
        let alias := Name.mkNum (name.str "_again") declared.size
        if first.type == again.type && first.levelParams == again.levelParams
            && first.all == [name] && again.all == [name]
            && !constants.contains alias && (base.find? alias).isNone then
          let info := ConstantInfo.thmInfo { again with name := alias, all := [alias] }
          constants := constants.insert alias info
          declared := declared.push (module.name, alias, info)
        else
          errors := errors.push
            s!"'{name}' is declared by {other?.getD .anonymous} and, with another statement, by {module.name}"
      | some _, _ =>
        errors := errors.push s!"'{name}' is declared by {other?.getD .anonymous} and by {module.name}"

  -- axioms
  let find (name : Name) : Option ConstantInfo := constants[name]? <|> base.find? name
  let names := constants.toArray.map (·.1)
  let (bits, axioms, unknown) := axiomBits find names
  for name in sorted unknown do
    errors := errors.push s!"unknown constant '{name}'"
  let mut theorems : Std.HashMap Name String := {}
  let mut printed : Std.HashSet String := {}
  let mut skipped := 0
  let mut constantLines : Array (List String) := #[]
  for module in audited do
    if printable module.name then
      constantLines := constantLines.push ["M", toString module.name]
    else
      errors := errors.push s!"the name of a module under audit cannot be printed: {module.name}"
  for (module, name, info) in declared do
    let used := axiomsOfBits axioms (bits.getD name 0)
    let refused := used.filter (!allowedAxioms.contains ·)
    let text := toString name
    -- a name that cannot be told from the rest of a line, or from another name
    let shown := printable name && printable module && used.all printable
    unless shown do
      errors := errors.push s!"a constant of {module}, or an axiom it depends on, has a name that cannot be printed: {name}"
    if printed.contains text then
      errors := errors.push s!"two constants are printed as '{text}'"
    printed := printed.insert text
    match info with
    | .axiomInfo _ =>
      if shown then
        constantLines := constantLines.push ["A", toString module, text]
      errors := errors.push s!"axiom '{name}' declared in {module}"
    | .thmInfo _ =>
      if kindOf name == "public" && text.toName != name then
        errors := errors.push s!"the name of the theorem '{name}' ({module}) does not read back from its text"
      else if shown then
        constantLines := constantLines.push
          ["T", kindOf name, toString module, text, " ".intercalate (sorted used).toList]
        theorems := theorems.insert name (kindOf name)
    | _ => pure ()
    if info.isUnsafe || info.isPartial then
      skipped := skipped + 1
      if shown then
        constantLines := constantLines.push ["S", toString module, text]
    unless refused.isEmpty || info matches .axiomInfo _ do
      errors := errors.push s!"'{name}' ({module}) depends on {(sorted refused).toList}"
  lines := lines ++ constantLines.qsort (fun a b => "\t".intercalate a < "\t".intercalate b)

  -- the kernel
  let start ← IO.monoMsNow
  try
    let checked ← base.replay constants
    let mut same := true
    for (name, info) in constants do
      unless info.isUnsafe || info.isPartial || checked.find? name == some info do
        same := false
        errors := errors.push s!"'{name}' is not in the environment of the kernel as its file has it"
    if same then
      lines := lines.push
        ["K", toString (constants.size - skipped), toString skipped, toString ((← IO.monoMsNow) - start)]
  catch e =>
    errors := errors.push s!"the kernel refuses the constants: {e}"

  -- the required theorems
  if let some file := cfg.required then
    let required := ((← IO.FS.readFile file).splitOn "\n").filter (· != "")
    let mut listed : Std.HashSet String := {}
    for text in required do
      if listed.contains text then
        errors := errors.push s!"required theorem listed twice: {text}"
      listed := listed.insert text
      match theorems[text.toName]? with
      | some "public" => pure ()
      | some _ => errors := errors.push s!"required theorem is private or generated: {text}"
      | none => errors := errors.push s!"required theorem missing: {text}"

  let out ← IO.getStdout
  for fields in lines do
    -- no field ends a field or a line; an empty one is the last, a theorem without axioms
    if fields.any (·.any refusedChar) then
      errors := errors.push s!"a line of the report has a character that is not allowed: {" ".intercalate fields}"
    else
      out.putStrLn ("\t".intercalate fields)
  for error in errors do
    out.putStrLn s!"E\t{escaped error}"
  out.flush
  return if errors.isEmpty then 0 else 1

end CheckOlean

def main (args : List String) : IO UInt32 := do
  try
    CheckOlean.run (← CheckOlean.parseArgs {} args)
  catch e =>
    IO.println s!"E\t{CheckOlean.escaped (toString e)}"
    return 1
