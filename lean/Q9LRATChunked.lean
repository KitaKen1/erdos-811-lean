import Mathlib.Tactic.Sat.FromLRAT

/-! Experimental chunked LRAT elaboration.

`lrat_proof` builds one enormous proof expression.  This command keeps the
same LRAT checker but periodically packages derived clause proofs in an
`And` theorem, so later chunks refer to projections instead of retaining the
whole proof term in one elaboration step.
-/

open Lean
open Std (HashMap)
open Std.Internal
open Std.Internal.Parsec String

namespace Mathlib.Tactic.Sat

/- An irreducible append wrapper keeps very large generated formulas opaque to
   the native compiler while exposing a small kernel theorem for membership
   splitting.  This is used only for structural CNF assembly; it carries no
   evaluator or external-proof trust. -/
@[irreducible] def fmlaAppend (a b : _root_.Sat.Fmla) : _root_.Sat.Fmla := a ++ b

lemma fmlaAppend_mem {c : _root_.Sat.Clause} {a b : _root_.Sat.Fmla} :
    c ∈ fmlaAppend a b ↔ c ∈ a ∨ c ∈ b := by
  simp [fmlaAppend]

/- A balanced binary representation of a formula.  This is used for
   executable audits of very large clause prefixes: reducing a conjunction
   tree keeps recursion depth logarithmic instead of traversing a 96k-element
   list linearly. -/
inductive FmlaTree where
  | leaf (c : _root_.Sat.Clause)
  | fork (left right : FmlaTree)

/- A path is a compact membership certificate for one leaf.  Unlike an index
   lookup, it does not recompute subtree sizes: a generated certificate only
   stores the left/right choices made by the balanced-tree builder.  The path
   is deliberately non-dependent, so a proof term contains no duplicated
   copies of the large left/right subtrees. -/
inductive FmlaPath where
  | here
  | left (p : FmlaPath)
  | right (p : FmlaPath)

def FmlaPath.clauseAt : FmlaPath → FmlaTree → Option _root_.Sat.Clause
  | .here, .leaf c => some c
  | .left p, .fork l _ => FmlaPath.clauseAt p l
  | .right p, .fork _ r => FmlaPath.clauseAt p r
  | _, _ => none

/- Structural flattening for a balanced clause tree.  It is public so a parsed
   collision slice can be defined directly from the same tree, avoiding a
   second 94k-element list normalization when proving slice identity. -/
def fmlaTreeFlatten : FmlaTree → _root_.Sat.Fmla
  | .leaf c => [c]
  | .fork l r => fmlaTreeFlatten l ++ fmlaTreeFlatten r

lemma fmlaTreeFlatten_mem_path {t : FmlaTree} (p : FmlaPath)
    {c : _root_.Sat.Clause}
    (h : FmlaPath.clauseAt p t = some c) :
    c ∈ fmlaTreeFlatten t := by
  induction p generalizing t with
  | here =>
      cases t with
      | leaf d =>
          simp [FmlaPath.clauseAt] at h
          subst c
          simp [fmlaTreeFlatten]
      | fork l r => simp [FmlaPath.clauseAt] at h
  | left p ih =>
      cases t with
      | leaf d => simp [FmlaPath.clauseAt] at h
      | fork l r =>
          simp only [FmlaPath.clauseAt] at h
          simp only [fmlaTreeFlatten, List.mem_append]
          exact Or.inl (ih h)
  | right p ih =>
      cases t with
      | leaf d => simp [FmlaPath.clauseAt] at h
      | fork l r =>
          simp only [FmlaPath.clauseAt] at h
          simp only [fmlaTreeFlatten, List.mem_append]
          exact Or.inr (ih h)

/- Opaque boundary for consumers that only need the identity of a generated
   tree.  The regular flattening function remains available for semantic
   induction; this wrapper prevents `rfl` from normalizing a 96k-leaf tree
   when a parsed CNF merely names the same tree. -/
@[irreducible] def fmlaTreeFlattenOpaque (t : FmlaTree) : _root_.Sat.Fmla :=
  fmlaTreeFlatten t

lemma fmlaTreeFlattenOpaque_eq (t : FmlaTree) :
    fmlaTreeFlattenOpaque t = fmlaTreeFlatten t := by
  simp only [fmlaTreeFlattenOpaque]

lemma fmlaTreeFlattenOpaque_subsumes (t : FmlaTree) :
    (fmlaTreeFlattenOpaque t).subsumes (fmlaTreeFlatten t) := by
  rw [fmlaTreeFlattenOpaque_eq]
  exact _root_.Sat.Fmla.subsumes_self _

lemma fmlaTreeFlattenOpaque_mem_path {t : FmlaTree} (p : FmlaPath)
    {c : _root_.Sat.Clause}
    (h : FmlaPath.clauseAt p t = some c) :
    c ∈ fmlaTreeFlattenOpaque t := by
  rw [fmlaTreeFlattenOpaque_eq]
  exact fmlaTreeFlatten_mem_path p h

lemma subsumes_one_of_mem {f : _root_.Sat.Fmla} {c : _root_.Sat.Clause}
    (h : c ∈ f) : f.subsumes [c] := by
  refine ⟨fun d hd => ?_⟩
  rcases List.mem_singleton.mp hd with rfl
  exact h

lemma fmla_subsumes_trans {f g h : _root_.Sat.Fmla}
    (hfg : f.subsumes g) (hgh : g.subsumes h) : f.subsumes h := by
  exact ⟨fun c hc => hfg.prop c (hgh.prop c hc)⟩

lemma subsumes_append_formula {f a b : _root_.Sat.Fmla}
    (ha : f.subsumes a) (hb : f.subsumes b) : f.subsumes (a ++ b) := by
  refine ⟨fun c hc => ?_⟩
  rcases List.mem_append.mp hc with hca | hcb
  · exact ha.prop c hca
  · exact hb.prop c hcb

structure Pending where
  id : Nat
  lits : Array Int
  expr : Expr
  proof : Expr

private partial def andType (xs : Array Expr) (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => mkConst ``True
  | 1 => xs[start]!
  | len =>
      let mid := start + len / 2
      mkApp2 (mkConst ``And) (andType xs start mid) (andType xs mid stop)

private partial def andValue (xs : Array Expr) (start stop : Nat) : MetaM Expr := do
  match stop - start with
  | 0 => pure (mkConst ``True.intro)
  | 1 => pure xs[start]!
  | len =>
      let mid := start + len / 2
      let a ← andValue xs start mid
      let b ← andValue xs mid stop
      Lean.Meta.mkAppM ``And.intro #[a, b]

private def andProj (h : Expr) (i n : Nat) : MetaM Expr := do
  if n ≤ 1 then
    pure h
  else
    let mid := n / 2
    if i < mid then
      let l ← Lean.Meta.mkAppM ``And.left #[h]
      andProj l i mid
    else
      let r ← Lean.Meta.mkAppM ``And.right #[h]
      andProj r (i - mid) (n - mid)

private def flushChunk (name : Name) (chunkNo : Nat)
    (ctx : Expr) (pending : Array Pending) : MetaM (HashMap Nat Clause) := do
  if pending.isEmpty then
    return {}
  let types := pending.toList.toArray.map (fun p =>
    mkApp2 (mkConst ``Sat.Fmla.proof) ctx p.expr)
  let vals := pending.toList.toArray.map Pending.proof
  let ty := andType types 0 types.size
  let value ← andValue vals 0 vals.size
  let chunkName ← mkAuxDeclName (Name.str name ("chunk" ++ toString chunkNo))
  addDecl <| Declaration.thmDecl {
    name := chunkName
    levelParams := []
    type := ty
    value := value
  }
  let h := mkConst chunkName
  let mut db : HashMap Nat Clause := {}
  for (item, idx) in pending.toList.zipIdx 0 do
    let proof ← andProj h idx pending.size
    db := db.insert item.id { lits := item.lits, expr := item.expr, proof := proof }
  return db

private def mergeDb (db extra : HashMap Nat Clause) : HashMap Nat Clause :=
  extra.fold (fun out id cl => out.insert id cl) db

structure SegmentSeed where
  id : Nat
  lits : Array Int
  chunk : Nat
  index : Nat
  size : Nat

/- Export a selected set of live derived clauses at a segment boundary.  A
   bounded conjunction (64 clauses) keeps imported theorem types small while
   avoiding one declaration per live clause.  The next segment uses the chunk
   and index recorded in `SegmentSeed` to project each proof. -/
private def exportClauseDb (name : Name) (ctx : Expr)
    (db : HashMap Nat Clause) (ids : Array Nat) : MetaM Unit := do
  if ids.isEmpty then
    throwError "empty LRAT segment export"
  let mut start := 0
  let mut chunkNo := 0
  while start < ids.size do
    let stop := min ids.size (start + 64)
    let mut types : Array Expr := #[]
    let mut vals : Array Expr := #[]
    for i in [start:stop] do
      let id := ids[i]!
      let some cl := db[id]? | throwError m!"missing live clause {id} at segment boundary"
      addDecl <| Declaration.defnDecl {
        name := Name.str name ("clause" ++ toString id)
        levelParams := []
        type := mkConst ``_root_.Sat.Clause
        value := buildClause cl.lits
        hints := ReducibilityHints.abbrev
        safety := DefinitionSafety.safe
      }
      types := types.push (mkApp2 (mkConst ``Sat.Fmla.proof) ctx cl.expr)
      vals := vals.push cl.proof
    let ty := andType types 0 types.size
    let value ← andValue vals 0 vals.size
    addDecl <| Declaration.thmDecl {
      name := Name.str name ("chunk" ++ toString chunkNo)
      levelParams := []
      type := ty
      value := value
    }
    start := stop
    chunkNo := chunkNo + 1

private def seedClauseDb (_ctx : Expr) (proofExport : Name)
    (seed : List SegmentSeed) (db : HashMap Nat Clause) :
    MetaM (HashMap Nat Clause) := do
  let mut out := db
  for item in seed do
    /- Keep the expression carried by a seed canonical.  Referring to the
       preceding stage's generated `clause<ID>` declaration makes the type of
       an imported chunk depend on the entire checkpoint chain; after a few
       stages the kernel must reconcile stage-N and stage-(N+1) names for the
       same literal array.  Rebuilding this small clause expression is
       definitionally equal to the exported clause, while avoiding that
       cross-stage type tower. -/
    let expr := buildClause item.lits
    let chunkProof := mkConst (Name.str proofExport ("chunk" ++ toString item.chunk))
    let proof ← andProj chunkProof item.index item.size
    let id := item.id
    let lits := item.lits
    out := out.insert id { lits := lits, expr := expr, proof := proof }
  pure out

private def flushPending (name : Name) (ctx : Expr) (chunkNo : Nat)
    (db : HashMap Nat Clause) (pending : Array Pending) :
    MetaM (HashMap Nat Clause × Nat) := do
  if pending.isEmpty then
    return (db, chunkNo)
  let extra ← flushChunk name chunkNo ctx pending
  return (mergeDb db extra, chunkNo + 1)

/- The standard `buildClauses` follows a balanced formula whose split points
   are determined by clause counts. A semantic context may instead be
   partitioned at externally meaningful block boundaries. These helpers build
   and consume a balanced tree over ranges, preserving those boundaries. -/
private partial def buildConjPartitionedBalanced (arr : Array (Array Int))
    (ranges : List (Nat × Nat)) : Expr :=
  match ranges with
  | [] => panic! "empty CNF partition"
  | [(start, len)] => buildConj arr start (start + len)
  | _ =>
      let mid := ranges.length / 2
      mkApp2 (mkConst ``Sat.Fmla.and)
        (buildConjPartitionedBalanced arr (ranges.take mid))
        (buildConjPartitionedBalanced arr (ranges.drop mid))

private partial def buildClausesPartitioned (arr : Array (Array Int)) (ctx : Expr)
    (ranges : List (Nat × Nat)) (f p : Expr) (accum : Nat × HashMap Nat Clause) :
    Nat × HashMap Nat Clause :=
  match ranges with
  | [] => panic! "empty CNF partition"
  | [(start, len)] => buildClauses arr ctx start (start + len) f p accum
  | _ =>
      let mid := ranges.length / 2
      let f₁ := f.appFn!.appArg!
      let f₂ := f.appArg!
      let p₁ := mkApp4 (mkConst ``Sat.Fmla.subsumes_left) ctx f₁ f₂ p
      let p₂ := mkApp4 (mkConst ``Sat.Fmla.subsumes_right) ctx f₁ f₂ p
      let accum := buildClausesPartitioned arr ctx (ranges.take mid) f₁ p₁ accum
      buildClausesPartitioned arr ctx (ranges.drop mid) f₂ p₂ accum

/- Variant for a partition whose leaf ranges already have compact context
   inclusion certificates.  Using a local certificate at each range avoids
   constructing a long chain of `subsumes_left/right` projections from the
   1,483-range root theorem for every initial clause. -/
private partial def buildClausesPartitionedWithProofs
    (arr : Array (Array Int)) (ctx : Expr) (ranges : List (Nat × Nat))
    (proofs : Array Expr) (proofIndex : Nat) (f : Expr)
    (accum : Nat × HashMap Nat Clause) : Nat × HashMap Nat Clause :=
  match ranges with
  | [] => panic! "empty CNF partition"
  | [(start, len)] =>
      buildClauses arr ctx start (start + len) f proofs[proofIndex]! accum
  | _ =>
      let mid := ranges.length / 2
      let f₁ := f.appFn!.appArg!
      let f₂ := f.appArg!
      let accum := buildClausesPartitionedWithProofs arr ctx (ranges.take mid)
        proofs proofIndex f₁ accum
      buildClausesPartitionedWithProofs arr ctx (ranges.drop mid)
        proofs (proofIndex + mid) f₂ accum

/- Parse one LRAT record.  The upstream parser exposes only an accumulating
   `many` parser; keeping this one-step form lets the replay consume the trace
   incrementally instead of retaining a 300k-element `Array LRATStep`. -/
private def parseLRATOne : String.Parser LRATStep := do
  let step ← Parser.parseNat <* Std.Internal.Parsec.String.ws
  if (← Std.Internal.Parsec.peek!) = 'd' then
    Std.Internal.Parsec.skip <* Std.Internal.Parsec.String.ws
    pure <| LRATStep.del (← Parser.parseNats)
  else
    Std.Internal.Parsec.String.ws
    pure <| LRATStep.add step (← Parser.parseInts) (← Parser.parseInts)

/- Consume one record at a time.  The loop keeps only the current
   database, pending chunk, and input position; previous LRAT records are
   represented by the hashed clause database and flushed theorem chunks. -/
private def replayLRATStream (name : Name) (chunkSize : Nat)
    (ctx : Expr) (it0 : Sigma String.Pos) (db0 : HashMap Nat Clause)
    (pending0 : Array Pending) (chunkNo0 stepNo0 : Nat)
    (segmentExport : Option (Name × Array Nat)) : MetaM Unit := do
  -- Keep the parser/replayer state in a loop rather than a MetaM recursion.
  -- This prevents one continuation frame per LRAT record from surviving until
  -- the empty clause, which is material for 300k-step traces.
  let mut it := it0
  let mut db := db0
  let mut pending := pending0
  let mut chunkNo := chunkNo0
  let mut stepNo := stepNo0
  let mut finished := false
  while !finished do
    let .success it' _ := Std.Internal.Parsec.String.ws it
      | throwError "LRAT whitespace parse failed"
    if it'.2.IsAtEnd then
      match segmentExport with
      | some (exportName, exportIds) =>
          let result ← flushPending name ctx chunkNo db pending
          exportClauseDb exportName ctx result.1 exportIds
          logInfo m!"LRAT segment export: {exportIds.size} live derived clauses"
          finished := true
      | none => throwError "failed to prove empty clause"
    if finished then
      continue
    match parseLRATOne it' with
    | .error rem err =>
        throwError m!"LRAT parse failed at {rem.2.offset.byteIdx}: {err}"
    | .success rem step =>
        if stepNo > 0 && stepNo % 100000 == 0 then
          logInfo m!"processed LRAT steps: {stepNo}"
        match step with
        | LRATStep.del ds =>
            /- Deletions do not require an immediate theorem flush.  A pending
               clause is just another database entry, so removing it from both
               the hash map and the pending queue is sound.  Its proof
               expression is closed over the earlier declarations and may be
               retained by a surviving pending proof; forcing a flush at every
               deletion created one auxiliary theorem for almost every LRAT
               line (q=9 has 125k deletions), which dominated the environment
               size. -/
            db := ds.foldl (·.erase ·) db
            pending := pending.filter (fun p => !ds.contains p.id)
            it := rem
            stepNo := stepNo + 1
          | LRATStep.add i ns pf =>
              if ns.isEmpty then
                let result ← flushPending name ctx chunkNo db pending
                db := result.1
                pending := #[]
                chunkNo := result.2
              let e := buildClause ns
              let clauseName := Name.str name ("clause" ++ toString i)
              if !ns.isEmpty then
                addDecl <| Declaration.defnDecl {
                  name := clauseName
                  levelParams := []
                  type := mkConst ``_root_.Sat.Clause
                  value := e
                  hints := ReducibilityHints.abbrev
                  safety := DefinitionSafety.safe
                }
              let stored := if ns.isEmpty then e else mkConst clauseName
              match buildProofStep db ns pf ctx e with
              | Except.error msg => throwError msg
              | Except.ok proof =>
                  if ns.isEmpty then
                    let ty := mkApp2 (mkConst ``Sat.Fmla.proof) ctx e
                    addDecl <| Declaration.thmDecl {
                      name := name
                      levelParams := []
                      type := ty
                      value := proof
                    }
                    logInfo m!"LRAT refutation reached at step {stepNo}"
                    finished := true
                  else
                    pending := pending.push {
                      id := i
                      lits := ns
                      expr := stored
                      proof := proof
                    }
                    db := db.insert i { lits := ns, expr := stored, proof := proof }
                    if pending.size >= max 1 chunkSize then
                      let result ← flushPending name ctx chunkNo db pending
                      db := result.1
                      pending := #[]
                      chunkNo := result.2
                    it := rem
                    stepNo := stepNo + 1

private def emitChunkedCore (cnf lrat : String) (name : Name) (chunkSize : Nat)
    (given : Option (Expr × Expr))
    (partitioned : Option (List (Nat × Nat)))
    (partitionProofs : Option (Array Expr)) : MetaM Unit := do
  let Parsec.ParseResult.success _ (_nvars, arr) :=
      Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  let ctx' := match partitioned with
    | some ranges => buildConjPartitionedBalanced arr ranges
    | none => buildConj arr 0 arr.size
  logInfo m!"parsed CNF and built context shape"
  let (ctx, p) ← match given with
    | some pair => pure pair
    | none => do
      let ctxName ← mkAuxDeclName (name ++ `ctx)
      addDecl <| Declaration.defnDecl {
        name := ctxName
        levelParams := []
        type := mkConst ``Sat.Fmla
        value := ctx'
        hints := ReducibilityHints.regular 0
        safety := DefinitionSafety.safe
      }
      let ctx := mkConst ctxName
      let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
      pure (ctx, p)
  logInfo m!"elaborated replay context and inclusion proof"
  if partitionProofs.isSome then
    logInfo m!"building initial clause database from range certificates"
  let mut db := match partitioned, partitionProofs with
    | some ranges, some proofs =>
        (buildClausesPartitionedWithProofs arr ctx ranges proofs 0 ctx' default).2
    | some ranges, none => (buildClausesPartitioned arr ctx ranges ctx' p default).2
    | none, _ => (buildClauses arr ctx 0 arr.size ctx' p default).2
  logInfo m!"built initial clause database"
  replayLRATStream name chunkSize ctx ⟨lrat, lrat.startPos⟩ db #[] 0 0 none

private def emitChunked (cnf lrat : String) (name : Name) (chunkSize : Nat) : MetaM Unit :=
  emitChunkedCore cnf lrat name chunkSize none none none

/- Replay one finite LRAT segment and export its live derived clauses.  The
   segment command deliberately rebuilds the ordinary CNF database in each
   module (about four seconds for q=9) and injects only the live derived
   clauses exported by the preceding module. -/
private def emitSegmentCore (cnf lrat : String) (name : Name) (chunkSize : Nat)
    (ctx : Expr) (_hsub : Expr) (ranges : List (Nat × Nat))
    (partitionProofs : Array Expr) (seed : List SegmentSeed)
    (seedProofExport : Name) (exportName : Name) (exportIds : Array Nat) : MetaM Unit := do
  let Parsec.ParseResult.success _ (_nvars, arr) :=
      Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  logInfo m!"parsed CNF and built context shape"
  logInfo m!"elaborated replay context and inclusion proof"
  let mut db :=
    (buildClausesPartitionedWithProofs arr ctx ranges partitionProofs 0
      (buildConjPartitionedBalanced arr ranges) default).2
  logInfo m!"built initial clause database"
  if !seed.isEmpty then
    let seeded ← seedClauseDb ctx seedProofExport seed db
    db := seeded
    logInfo m!"seeded {seed.length} live derived clauses"
  replayLRATStream name chunkSize ctx ⟨lrat, lrat.startPos⟩ db #[] 0 0
    (some (exportName, exportIds))

end Mathlib.Tactic.Sat

open Lean Elab Term

namespace Mathlib.Tactic.Sat

/-!
`sat_cnf_def` is the lightweight companion to `lrat_proof_chunked`.  It
publishes the parsed CNF as a named `Sat.Fmla` definition without attempting
to elaborate the LRAT trace.  This is useful for developing a semantic
SAT-to-graph bridge: the bridge can be compiled and tested independently of
the (potentially very slow) kernel replay.
-/

elab "sat_cnf_def " n:ident ppSpace cnf:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let Parsec.ParseResult.success _ (nvars, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if arr.isEmpty then throwError "empty CNF"
    let ctx' := buildConj arr 0 arr.size
    addDecl <| Declaration.defnDecl {
      name := name
      levelParams := []
      type := mkConst ``Sat.Fmla
      value := ctx'
      hints := ReducibilityHints.regular 0
      safety := DefinitionSafety.safe
    }
    logInfo m!"defined {name} ({nvars} variables, {arr.size} clauses)"

/- `sat_cnf_partitioned_def` publishes the same parsed clause array as an
   explicit append of contiguous slices.  This is a structural companion to
   `sat_cnf_def`: membership proofs can split at the slice boundaries without
   normalizing a 96k-clause `take`/`drop` expression.  The ranges are supplied
   as a small list of `(start,length)` pairs and are checked against the
   parser's clause count at elaboration time. -/
private def buildConjPartitioned (arr : Array (Array Int))
    (ranges : List (Nat × Nat)) : Expr :=
  match ranges with
  | [] => panic! "empty CNF partition"
  | (start, len) :: rest =>
      rest.foldl
        (fun acc (s, n) =>
          mkApp2 (mkConst ``Sat.Fmla.and) acc (buildConj arr s (s + n)))
        (buildConj arr start (start + len))

elab "sat_cnf_partitioned_def " n:ident ppSpace cnf:term:max
    ppSpace ranges:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let rangeType := mkApp (mkConst ``List [Level.zero])
      (mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
        (mkConst ``Nat) (mkConst ``Nat))
    let ranges ← unsafe evalTerm (List (Nat × Nat)) rangeType ranges
    let Parsec.ParseResult.success _ (nvars, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if ranges.isEmpty then
      throwError "empty CNF partition"
    for (start, len) in ranges do
      if len == 0 then
        throwError "empty CNF partition slice"
      if start + len > arr.size then
        throwError m!"CNF partition slice [{start}, {start + len}) exceeds {arr.size} clauses"
    let ctx' := buildConjPartitioned arr ranges
    addDecl <| Declaration.defnDecl {
      name := name
      levelParams := []
      type := mkConst ``Sat.Fmla
      value := ctx'
      hints := ReducibilityHints.regular 0
      safety := DefinitionSafety.safe
    }
    logInfo m!"defined {name} ({nvars} variables, {arr.size} clauses; {ranges.length} structural slices)"

/- `sat_cnf_slice_def` is the bounded companion used by semantic audits.  It
   parses the same DIMACS input at elaboration time, but publishes only an
   explicitly requested contiguous clause slice.  This avoids forcing the
   kernel/compiler to normalize a 96k-clause formula merely to inspect a
   1k-clause cardinality block. -/
elab "sat_cnf_slice_def " n:ident ppSpace cnf:term:max ppSpace start:num
    ppSpace len:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let Parsec.ParseResult.success _ (nvars, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    let first := start.getNat
    let count := len.getNat
    if count == 0 then throwError "empty CNF slice"
    if first + count > arr.size then
      throwError m!"CNF slice [{first}, {first + count}) exceeds {arr.size} clauses"
    let mut slice : Array (Array Int) := #[]
    for i in [first:first + count] do
      slice := slice.push arr[i]!
    let ctx' := buildConj slice 0 slice.size
    addDecl <| Declaration.defnDecl {
      name := name
      levelParams := []
      type := mkConst ``Sat.Fmla
      value := ctx'
      hints := ReducibilityHints.regular 0
      safety := DefinitionSafety.safe
    }
    logInfo m!"defined {name} (clauses {first}..{first + count - 1}, {nvars} variables)"

private partial def buildFmlaTree (arr : Array (Array Int)) (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => panic! "empty CNF tree"
  | 1 => mkApp (mkConst ``FmlaTree.leaf) (buildClause arr[start]!)
  | len =>
      let mid := start + len / 2
      mkApp2 (mkConst ``FmlaTree.fork)
        (buildFmlaTree arr start mid) (buildFmlaTree arr mid stop)

/- Build a dependent path to one leaf without unfolding the whole tree.  The
   split points are known from the same balanced builder, so a path has only
   logarithmic constructor depth. -/
private partial def buildFmlaPath (arr : Array (Array Int)) (start stop index : Nat) : MetaM Expr := do
  if stop ≤ start then
    throwError "empty CNF tree path"
  if index < start || stop ≤ index then
    throwError m!"CNF tree path index {index} is outside [{start}, {stop})"
  match stop - start with
  | 1 =>
      pure (mkConst ``FmlaPath.here)
  | len =>
      let mid := start + len / 2
      if index < mid then
        return mkApp (mkConst ``FmlaPath.left)
          (← buildFmlaPath arr start mid index)
      else
        return mkApp (mkConst ``FmlaPath.right)
          (← buildFmlaPath arr mid stop index)

/- Build a `subsumes` proof for one parser chunk against an opaque tree.  The
   parser chunk has the same balanced shape as `buildFmlaTree`; each leaf is
   discharged by a compact path and its generated leaf equation. -/
private partial def buildTreeChunkSubsumesProof
    (arr : Array (Array Int)) (treeStart treeStop start stop : Nat)
    (treeExpr : Expr) : MetaM Expr := do
  match stop - start with
  | 0 => throwError "empty parser chunk"
  | 1 =>
      let path ← buildFmlaPath arr treeStart treeStop start
      let treePath := Lean.mkApp2 (Lean.mkConst ``FmlaPath.clauseAt) path treeExpr
      let eqValue ← Lean.Meta.mkAppM ``Eq.refl #[treePath]
      let memProof ← Lean.Meta.mkAppM
        ``fmlaTreeFlattenOpaque_mem_path #[path, eqValue]
      Lean.Meta.mkAppM ``subsumes_one_of_mem #[memProof]
  | len =>
      let mid := start + len / 2
      let left ← buildTreeChunkSubsumesProof arr treeStart treeStop start mid treeExpr
      let right ← buildTreeChunkSubsumesProof arr treeStart treeStop mid stop treeExpr
      Lean.Meta.mkAppM ``subsumes_append_formula #[left, right]

private partial def combineSubsumesProofs (proofs : Array Expr)
    (start stop : Nat) : MetaM Expr := do
  match stop - start with
  | 0 => throwError "empty subsumes proof list"
  | 1 => pure proofs[start]!
  | len =>
      let mid := start + len / 2
      let left ← combineSubsumesProofs proofs start mid
      let right ← combineSubsumesProofs proofs mid stop
      Lean.Meta.mkAppM ``subsumes_append_formula #[left, right]

/- `sat_cnf_tree_def` publishes a balanced tree for a contiguous DIMACS
   slice.  The generated term is definitionally the same clause sequence as
   the source slice, but semantic checks can recurse over logarithmic-depth
   subtrees. -/
elab "sat_cnf_tree_def " n:ident ppSpace cnf:term:max ppSpace start:num
    ppSpace len:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let Parsec.ParseResult.success _ (nvars, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    let first := start.getNat
    let count := len.getNat
    if count == 0 then throwError "empty CNF tree"
    if first + count > arr.size then
      throwError m!"CNF tree [{first}, {first + count}) exceeds {arr.size} clauses"
    let tree := buildFmlaTree arr first (first + count)
    addDecl <| Declaration.defnDecl {
      name := name
      levelParams := []
      type := mkConst ``FmlaTree
      value := tree
      hints := ReducibilityHints.regular 0
      safety := DefinitionSafety.safe
    }
    logInfo m!"defined {name} (clauses {first}..{first + count - 1}, {nvars} variables)"

/- Publish a compact dependent path to one generated tree leaf.  This is a
   proof-term building block for clause-membership certificates; it does not
   evaluate or replay any LRAT step. -/
elab "fmla_tree_path_def " n:ident ppSpace tree:term:max ppSpace cnf:term:max
    ppSpace start:num ppSpace len:num ppSpace index:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let treeExpr ← Term.elabTerm tree (some (mkConst ``FmlaTree))
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let Parsec.ParseResult.success _ (_, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    let first := start.getNat
    let count := len.getNat
    let idx := index.getNat
    if count == 0 then throwError "empty CNF tree path"
    if first + count > arr.size then
      throwError m!"CNF tree path [{first}, {first + count}) exceeds {arr.size} clauses"
    let pathType := Lean.mkConst ``FmlaPath
    let pathValue ← buildFmlaPath arr first (first + count) idx
    addDecl <| Declaration.defnDecl {
      name := name
      levelParams := []
      type := pathType
      value := pathValue
      hints := ReducibilityHints.regular 0
      safety := DefinitionSafety.safe
    }
    let treePath := Lean.mkApp2 (Lean.mkConst ``FmlaPath.clauseAt) pathValue treeExpr
    let leaf := buildClause arr[idx]!
    let expected ← Lean.Meta.mkAppM ``Option.some #[leaf]
    let eqType ← Lean.Meta.mkAppM ``Eq #[treePath, expected]
    let eqValue ← Lean.Meta.mkAppM ``Eq.refl #[treePath]
    addDecl <| Declaration.thmDecl {
      name := name ++ `eq
      levelParams := []
      type := eqType
      value := eqValue
    }
    logInfo m!"defined {name} (tree leaf index {idx})"

/- Publish a compact inclusion theorem for one parser chunk.  The source tree
   range may be much larger than the chunk; path certificates connect every
   chunk leaf to the same opaque tree without normalizing the whole formula. -/
elab "fmla_tree_subsumes_chunk_def " n:ident ppSpace tree:term:max
    ppSpace cnf:term:max ppSpace tree_start:num ppSpace tree_len:num
    ppSpace start:num ppSpace len:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let treeExpr ← Term.elabTerm tree (some (Lean.mkConst ``FmlaTree))
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let Parsec.ParseResult.success _ (_, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    let tfirst := tree_start.getNat
    let tcount := tree_len.getNat
    let first := start.getNat
    let count := len.getNat
    if tcount == 0 || count == 0 then
      throwError "empty tree or parser chunk"
    if tfirst + tcount > arr.size then
      throwError m!"tree range [{tfirst}, {tfirst + tcount}) exceeds {arr.size} clauses"
    if first < tfirst || tfirst + tcount < first + count then
      throwError m!"parser chunk [{first}, {first + count}) is outside tree range [{tfirst}, {tfirst + tcount})"
    let contextExpr := Lean.mkApp (Lean.mkConst ``fmlaTreeFlattenOpaque) treeExpr
    let formulaExpr := buildConj arr first (first + count)
    let proof ← buildTreeChunkSubsumesProof arr tfirst (tfirst + tcount)
      first (first + count) treeExpr
    let type := Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) contextExpr formulaExpr
    addDecl <| Declaration.thmDecl {
      name := name
      levelParams := []
      type := type
      value := proof
    }
    logInfo m!"defined {name} (parser clauses {first}..{first + count - 1})"

/- Generate a balanced partition of a tree range and a root inclusion theorem
   from per-chunk certificates.  Chunk theorems are stored as auxiliary
   declarations, so the root proof remains small even when the range contains
   tens of thousands of leaves. -/
elab "fmla_tree_subsumes_partition_def " n:ident ppSpace tree:term:max
    ppSpace cnf:term:max ppSpace tree_start:num ppSpace tree_len:num
    ppSpace chunk_size:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let treeExpr ← Term.elabTerm tree (some (Lean.mkConst ``FmlaTree))
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let Parsec.ParseResult.success _ (_, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    let first := tree_start.getNat
    let count := tree_len.getNat
    let width := chunk_size.getNat
    if count == 0 || width == 0 then
      throwError "empty tree range or chunk size"
    if first + count > arr.size then
      throwError m!"tree range [{first}, {first + count}) exceeds {arr.size} clauses"
    let mut ranges : List (Nat × Nat) := []
    let mut cursor := first
    let stop := first + count
    while cursor < stop do
      let len := min width (stop - cursor)
      ranges := ranges.concat (cursor, len)
      cursor := cursor + len
    let contextExpr := Lean.mkApp (Lean.mkConst ``fmlaTreeFlattenOpaque) treeExpr
    let shape := buildConjPartitionedBalanced arr ranges
    let shapeName := Name.str name "shape"
    addDecl <| Declaration.defnDecl {
      name := shapeName
      levelParams := []
      type := Lean.mkConst ``Sat.Fmla
      value := shape
      hints := ReducibilityHints.regular 0
      safety := DefinitionSafety.safe
    }
    let mut proofs : Array Expr := #[]
    for (chunkStart, chunkLen) in ranges do
      let chunkFormula := buildConj arr chunkStart (chunkStart + chunkLen)
      let chunkProof ← buildTreeChunkSubsumesProof arr first stop
        chunkStart (chunkStart + chunkLen) treeExpr
      let chunkName := Name.str name ("chunk" ++ toString proofs.size)
      let chunkType := Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes)
        contextExpr chunkFormula
      addDecl <| Declaration.thmDecl {
        name := chunkName
        levelParams := []
        type := chunkType
        value := chunkProof
      }
      proofs := proofs.push (Lean.mkConst chunkName)
    let rootProof ← combineSubsumesProofs proofs 0 proofs.size
    let rootType := Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) contextExpr shape
    addDecl <| Declaration.thmDecl {
      name := name
      levelParams := []
      type := rootType
      value := rootProof
    }
    logInfo m!"defined {name} ({ranges.length} chunks, clauses {first}..{stop - 1})"

/- Compose a collision-tree partition with the four contiguous tail blocks of
   the q=9 finite CNF.  The caller supplies a full-context inclusion proof for
   each tail block and for the collision context; the command derives the
   1,479 collision chunk proofs from the named partition auxiliaries and then
   combines all ranges with the same balanced shape used by the LRAT builder. -/
elab "fmla_append_partition_subsumes_def " n:ident
    ppSpace ctx:term:max ppSpace collisionCtx:term:max ppSpace partition:ident
    ppSpace cnf:term:max ppSpace collisionStart:num ppSpace collisionLen:num
    ppSpace chunkSize:num ppSpace baseLen:num ppSpace anchorLen:num
    ppSpace atleastLen:num ppSpace atmostLen:num
    ppSpace "collision_lift" collisionLift:term:max
    ppSpace "base_lift" baseLift:term:max
    ppSpace "anchor_lift" anchorLift:term:max
    ppSpace "atleast_lift" atleastLift:term:max
    ppSpace "atmost_lift" atmostLift:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let Parsec.ParseResult.success _ (_, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    let cstart := collisionStart.getNat
    let clen := collisionLen.getNat
    let width := chunkSize.getNat
    let blen := baseLen.getNat
    let alen := anchorLen.getNat
    let plen := atleastLen.getNat
    let qlen := atmostLen.getNat
    if clen == 0 || width == 0 then
      throwError "empty collision range or chunk size"
    let cstop := cstart + clen
    let bstart := cstop
    let bstop := bstart + blen
    let astart := bstop
    let astop := astart + alen
    let pstart := astop
    let pstop := pstart + plen
    let qstart := pstop
    let qstop := qstart + qlen
    if qstop > arr.size then
      throwError m!"q=9 partition ends at {qstop}, but CNF has {arr.size} clauses"
    let ctxExpr ← Term.elabTerm ctx (some (Lean.mkConst ``Sat.Fmla))
    let collisionExpr ← Term.elabTerm collisionCtx (some (Lean.mkConst ``Sat.Fmla))
    let liftType := Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) ctxExpr collisionExpr
    let collisionLiftExpr ← Term.elabTerm collisionLift (some liftType)
    let tailProofType (start len : Nat) :=
      Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) ctxExpr
        (buildConj arr start (start + len))
    let baseLiftExpr ← Term.elabTerm baseLift (some (tailProofType bstart blen))
    let anchorLiftExpr ← Term.elabTerm anchorLift (some (tailProofType astart alen))
    let atleastLiftExpr ← Term.elabTerm atleastLift (some (tailProofType pstart plen))
    let atmostLiftExpr ← Term.elabTerm atmostLift (some (tailProofType qstart qlen))
    let partitionName := (← getCurrNamespace) ++ partition.getId
    let mut ranges : List (Nat × Nat) := []
    let mut cursor := cstart
    while cursor < cstop do
      let len := min width (cstop - cursor)
      ranges := ranges.concat (cursor, len)
      cursor := cursor + len
    ranges := ranges.concat (bstart, blen)
    ranges := ranges.concat (astart, alen)
    ranges := ranges.concat (pstart, plen)
    ranges := ranges.concat (qstart, qlen)
    let shape := buildConjPartitionedBalanced arr ranges
    let shapeName := Name.str name "shape"
    addDecl <| Declaration.defnDecl {
      name := shapeName
      levelParams := []
      type := Lean.mkConst ``Sat.Fmla
      value := shape
      hints := ReducibilityHints.regular 0
      safety := DefinitionSafety.safe
    }
    let mut proofs : Array Expr := #[]
    let collisionRanges := ranges.take (ranges.length - 4)
    let storeProof (proofs : Array Expr) (start len : Nat) (proof : Expr) : MetaM (Expr × Array Expr) := do
      -- These are per-range certificates for the *full* context.  Keep them
      -- under the enclosing theorem name so replay can reference
      -- `q9_full_partition.chunkN` directly.
      let chunkName := Name.str name ("chunk" ++ toString proofs.size)
      let chunkType := Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes)
        ctxExpr (buildConj arr start (start + len))
      addDecl <| Declaration.thmDecl {
        name := chunkName
        levelParams := []
        type := chunkType
        value := proof
      }
      let chunkConst := Lean.mkConst chunkName
      pure (chunkConst, proofs.push chunkConst)
    for (chunkStart, chunkLen) in collisionRanges do
      let chunkName := Name.str partitionName ("chunk" ++ toString proofs.size)
      let chunkProof := Lean.mkConst chunkName
      let lifted ← Lean.Meta.mkAppM ``fmla_subsumes_trans #[collisionLiftExpr, chunkProof]
      let (_, nextProofs) ← storeProof proofs chunkStart chunkLen lifted
      proofs := nextProofs
    let (_, nextProofs) ← storeProof proofs bstart blen baseLiftExpr
    proofs := nextProofs
    let (_, nextProofs) ← storeProof proofs astart alen anchorLiftExpr
    proofs := nextProofs
    let (_, nextProofs) ← storeProof proofs pstart plen atleastLiftExpr
    proofs := nextProofs
    let (_, nextProofs) ← storeProof proofs qstart qlen atmostLiftExpr
    proofs := nextProofs
    let rootProof ← combineSubsumesProofs proofs 0 proofs.size
    let rootType := Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) ctxExpr shape
    addDecl <| Declaration.thmDecl {
      name := name
      levelParams := []
      type := rootType
      value := rootProof
    }
    logInfo m!"defined {name} ({ranges.length} ranges, clauses {cstart}..{qstop - 1})"

elab "lrat_proof_chunked " n:ident ppSpace cnf:term:max ppSpace lrat:term:max
    ppSpace "chunk_size" k:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (mkConst ``String) lrat
    emitChunked cnf lrat name k.getNat

/- A context-aware variant for partitioned CNFs.  The caller supplies a
   semantic context `ctx` and a proof that it subsumes the balanced formula
   generated from the DIMACS clauses.  LRAT initial clauses are then replayed
   against `ctx` directly, so no definitional equality between two different
   parenthesizations of the same clause list is required. -/
elab "lrat_proof_chunked_with_context " n:ident ppSpace cnf:term:max
    ppSpace lrat:term:max ppSpace "context " ctx:term:max
    ppSpace "subsumes " hsub:term:max ppSpace "chunk_size" k:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (mkConst ``String) lrat
    let Parsec.ParseResult.success _ (_, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if arr.isEmpty then throwError "empty CNF"
    let full := buildConj arr 0 arr.size
    let ctxExpr ← Term.elabTerm ctx (some (mkConst ``Sat.Fmla))
    let subType := mkApp2 (mkConst ``Sat.Fmla.subsumes) ctxExpr full
    let hsubExpr ← Term.elabTerm hsub (some subType)
    emitChunkedCore cnf lrat name k.getNat (some (ctxExpr, hsubExpr)) none none

/- Partition-aware LRAT replay.  The supplied ranges must cover the DIMACS
   array contiguously.  Initial clauses are extracted block by block, while
   the LRAT derivation itself is unchanged.  This avoids forcing
   `buildClauses` to rediscover semantic block boundaries from a single
   midpoint-balanced expression. -/
elab "lrat_proof_chunked_with_partitioned_context " n:ident
    ppSpace cnf:term:max ppSpace lrat:term:max
    ppSpace "context " ctx:term:max ppSpace "subsumes " hsub:term:max
    ppSpace "ranges " ranges:term:max ppSpace "chunk_size" k:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (Lean.mkConst ``String) lrat
    logInfo m!"chunk replay: evaluated CNF/LRAT strings"
    let rangeType := Lean.mkApp (Lean.mkConst ``List [Level.zero])
      (Lean.mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero])
        (Lean.mkConst ``Nat) (Lean.mkConst ``Nat))
    let ranges ← unsafe evalTerm (List (Nat × Nat)) rangeType ranges
    let Parsec.ParseResult.success _ (_, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if ranges.isEmpty then throwError "empty CNF partition"
    let mut cursor := 0
    for (start, len) in ranges do
      if len == 0 then throwError "empty CNF partition slice"
      if start != cursor then
        throwError m!"CNF partition has gap or overlap at {start}; expected {cursor}"
      if start + len > arr.size then
        throwError m!"CNF partition slice [{start}, {start + len}) exceeds {arr.size} clauses"
      cursor := start + len
    if cursor != arr.size then
      throwError m!"CNF partition ends at {cursor}, but CNF has {arr.size} clauses"
    let shape := buildConjPartitionedBalanced arr ranges
    let ctxExpr ← Term.elabTerm ctx (some (Lean.mkConst ``Sat.Fmla))
    let subType := Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) ctxExpr shape
    let hsubExpr ← Term.elabTerm hsub (some subType)
    emitChunkedCore cnf lrat name k.getNat (some (ctxExpr, hsubExpr)) (some ranges) none

/- Variant that consumes the compact per-range certificates emitted by
   `fmla_append_partition_subsumes_def`.  The prefix identifies declarations
   named `prefix.chunk0`, `prefix.chunk1`, ... in the current namespace. -/
elab "lrat_proof_chunked_with_partitioned_chunk_proofs " n:ident
    ppSpace cnf:term:max ppSpace lrat:term:max
    ppSpace "context " ctx:term:max ppSpace "subsumes " hsub:term:max
    ppSpace "ranges " rangeExpr:term:max ppSpace "chunk_proofs " prefixIdent:ident
    ppSpace "chunk_size" k:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (Lean.mkConst ``String) lrat
    logInfo m!"chunk replay: evaluated CNF/LRAT strings"
    let rangeType := Lean.mkApp (Lean.mkConst ``List [Level.zero])
      (Lean.mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero])
        (Lean.mkConst ``Nat) (Lean.mkConst ``Nat))
    let rangeList ← unsafe evalTerm (List (Nat × Nat)) rangeType rangeExpr
    logInfo m!"chunk replay: evaluated range list ({rangeList.length} ranges)"
    let Parsec.ParseResult.success _ (_, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if rangeList.isEmpty then throwError "empty CNF partition"
    let mut cursor := 0
    for (start, len) in rangeList do
      if len == 0 then throwError "empty CNF partition slice"
      if start != cursor then
        throwError m!"CNF partition has gap or overlap at {start}; expected {cursor}"
      if start + len > arr.size then
        throwError m!"CNF partition slice [{start}, {start + len}) exceeds {arr.size} clauses"
      cursor := start + len
    if cursor != arr.size then
      throwError m!"CNF partition ends at {cursor}, but CNF has {arr.size} clauses"
    let shape := buildConjPartitionedBalanced arr rangeList
    logInfo m!"chunk replay: parsed ranges and built balanced shape"
    let ctxExpr ← Term.elabTerm ctx (some (Lean.mkConst ``Sat.Fmla))
    logInfo m!"chunk replay: elaborated context"
    let subType := Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) ctxExpr shape
    let hsubExpr ← Term.elabTerm hsub (some subType)
    logInfo m!"chunk replay: elaborated inclusion proof"
    let prefixName := (← getCurrNamespace) ++ prefixIdent.getId
    let mut proofs : Array Expr := #[]
    for i in [0:rangeList.length] do
      proofs := proofs.push (Lean.mkConst (Name.str prefixName ("chunk" ++ toString i)))
    emitChunkedCore cnf lrat name k.getNat (some (ctxExpr, hsubExpr))
      (some rangeList) (some proofs)
    logInfo m!"chunk proof command parsed: {name}"

/- File-backed variant.  Reading the DIMACS/LRAT payloads in the command
   elaborator avoids expanding 100MB `include_str` terms before replay starts. -/
elab "lrat_proof_chunked_with_partitioned_chunk_proofs_from_files " n:ident
    ppSpace cnfPath:str ppSpace lratPath:str
    ppSpace "context " ctx:ident ppSpace "subsumes " hsub:ident
    ppSpace "ranges " rangeExpr:term:max ppSpace "chunk_proofs " prefixIdent:ident
    ppSpace "chunk_size" k:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let cnf ← Lean.Elab.Command.liftIO <| IO.FS.readFile cnfPath.getString
  let lrat ← Lean.Elab.Command.liftIO <| IO.FS.readFile lratPath.getString
  Command.liftTermElabM do
    logInfo m!"chunk replay (files): read CNF/LRAT payloads"
    let rangeType := Lean.mkApp (Lean.mkConst ``List [Level.zero])
      (Lean.mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero])
        (Lean.mkConst ``Nat) (Lean.mkConst ``Nat))
    let rangeList ← unsafe evalTerm (List (Nat × Nat)) rangeType rangeExpr
    let Parsec.ParseResult.success _ (_, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if rangeList.isEmpty then throwError "empty CNF partition"
    let mut cursor := 0
    for (start, len) in rangeList do
      if len == 0 then throwError "empty CNF partition slice"
      if start != cursor then
        throwError m!"CNF partition has gap or overlap at {start}; expected {cursor}"
      if start + len > arr.size then
        throwError m!"CNF partition slice [{start}, {start + len}) exceeds {arr.size} clauses"
      cursor := start + len
    if cursor != arr.size then
      throwError m!"CNF partition ends at {cursor}, but CNF has {arr.size} clauses"
    logInfo m!"chunk replay (files): parsed and validated ranges"
    let ns ← getCurrNamespace
    let ctxExpr := Lean.mkConst (ns ++ ctx.getId)
    let hsubExpr := Lean.mkConst (ns ++ hsub.getId)
    let prefixName := ns ++ prefixIdent.getId
    let mut proofs : Array Expr := #[]
    for i in [0:rangeList.length] do
      proofs := proofs.push (Lean.mkConst (Name.str prefixName ("chunk" ++ toString i)))
    emitChunkedCore cnf lrat name k.getNat (some (ctxExpr, hsubExpr))
      (some rangeList) (some proofs)

/- File-backed segmented replay.  `seed` lists live derived clauses exported
   by the preceding module; their proofs are projections from `proof_export`.
   At end-of-file the command exports the live IDs in `export_ids` as a new
   conjunction theorem named by `export`. -/
elab "lrat_proof_chunked_segment_with_partitioned_chunk_proofs_from_files " n:ident
    ppSpace cnfPath:str ppSpace lratPath:str
    ppSpace "context " ctx:ident ppSpace "subsumes " hsub:ident
    ppSpace "ranges " rangeExpr:term:max ppSpace "chunk_proofs " prefixIdent:ident
    ppSpace "seed " seedExpr:term:max ppSpace "proof_export " proofExportIdent:ident
    ppSpace "export_ids " exportIdsExpr:term:max ppSpace "export " exportIdent:ident
    ppSpace "chunk_size" k:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let cnf ← Lean.Elab.Command.liftIO <| IO.FS.readFile cnfPath.getString
  let lrat ← Lean.Elab.Command.liftIO <| IO.FS.readFile lratPath.getString
  Command.liftTermElabM do
    logInfo m!"segmented replay: read CNF/LRAT payloads"
    let rangeType := Lean.mkApp (Lean.mkConst ``List [Level.zero])
      (Lean.mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero])
        (Lean.mkConst ``Nat) (Lean.mkConst ``Nat))
    let rangeList ← unsafe evalTerm (List (Nat × Nat)) rangeType rangeExpr
    let seedType := Lean.mkApp (Lean.mkConst ``List [Level.zero])
      (Lean.mkConst ``SegmentSeed)
    let seedList ← unsafe evalTerm (List SegmentSeed) seedType seedExpr
    let idsType := Lean.mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Nat)
    let exportIdList ← unsafe evalTerm (List Nat) idsType exportIdsExpr
    let Parsec.ParseResult.success _ (_, arr) :=
        Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if rangeList.isEmpty then throwError "empty CNF partition"
    let mut cursor := 0
    for (start, len) in rangeList do
      if len == 0 then throwError "empty CNF partition slice"
      if start != cursor then
        throwError m!"CNF partition has gap or overlap at {start}; expected {cursor}"
      if start + len > arr.size then
        throwError m!"CNF partition slice [{start}, {start + len}) exceeds {arr.size} clauses"
      cursor := start + len
    if cursor != arr.size then
      throwError m!"CNF partition ends at {cursor}, but CNF has {arr.size} clauses"
    logInfo m!"segmented replay: parsed and validated ranges/seeds"
    let ns ← getCurrNamespace
    let ctxExpr := Lean.mkConst (ns ++ ctx.getId)
    let hsubExpr := Lean.mkConst (ns ++ hsub.getId)
    let prefixName := ns ++ prefixIdent.getId
    let mut proofs : Array Expr := #[]
    for i in [0:rangeList.length] do
      proofs := proofs.push (Lean.mkConst (Name.str prefixName ("chunk" ++ toString i)))
    let seedProof := ns ++ proofExportIdent.getId
    let exportName := ns ++ exportIdent.getId
    emitSegmentCore cnf lrat name k.getNat ctxExpr hsubExpr rangeList proofs
      seedList seedProof exportName exportIdList.toArray
    logInfo m!"segmented replay command parsed: {name}"

end Mathlib.Tactic.Sat
