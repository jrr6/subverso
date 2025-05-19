/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Examples.Env
import SubVerso.Module
import Lean.Util.Paths

open Lean Elab Frontend
open Lean.Elab.Command hiding Context
open SubVerso Examples Module
open SubVerso.Highlighting (Highlighted highlight)

def helpText : String :=
"Extract a module's highlighted representation as JSON

Usage: subverso-extract-mod MOD [OUT]

MOD is the name of a Lean module, and OUT is the destination of the JSON.
If OUT is not specified, the JSON is emitted to standard output.

The output JSON contains two fields: \"messages\", which contains the message
log, and \"commands\", which contains the commands in the module in the format
described below.

Each command in the module is represented as a JSON object with the following
fields:

 * \"kind\": the syntax kind of the command, as emitted by the Lean parser

 * \"range\": the start and end source positions of the command. Line and column
   numbers are one-based, so the start of the file is {\"line\": 1, \"column\": 1},
   and columns are in terms of Unicode code points.

 * \"defines\": the names defined in the command, as an array of strings.

 * \"code\": the JSON serialization of SubVerso's highlighted code datatype. The
   specifics of this representation are an implementation detail, and it should
   be deserialized using the same version of SubVerso.
"
/--
Creates a `ModuleItem` from source that could not be parsed.
-/

  -- TODO: process messages linearly -- calling this repeatedly for s spans with
  -- an m-message log should be O(max(m,s)), not O(m*s)
def findMessagesForUnparsedSpan (src : Substring) (msgs : Array Message) (fm : FileMap) : IO Highlighted := do
  let msgsHere := msgs.filterMap fun m =>
    let pos := fm.ofPosition m.pos
    let endPos := fm.ofPosition (m.endPos.getD m.pos)
    if src.startPos ≤ pos && pos ≤ src.stopPos then
      some (m, pos, min src.stopPos endPos)
    else
      none

  if msgsHere.isEmpty then
    return .text src.toString

  let mut res := #[]
  for (msg, start, fin) in msgsHere do
    if src.startPos < start then
      let initialSubstr := { src with stopPos := start }
      res := res.push (.text initialSubstr.toString)
    let kind : Highlighted.Span.Kind :=
      match msg.severity with
      | .error => .error
      | .warning => .warning
      | .information => .info
    let content := { src with startPos := start, stopPos := fin }
    res := res.push (.span #[(kind, ← Highlighting.openUntil.contents msg)] (.text content.toString))
    if fin < src.stopPos then
      let finalSubstr := { src with startPos := fin }
      res := res.push (.text finalSubstr.toString)
  return .seq res

def ModuleItem.ofUnparsed (input : String) (start stop : String.Pos) (fm : FileMap) (msgs : Array Message) : IO ModuleItem := return {
  range := some (fm.toPosition start, fm.toPosition stop)
  kind := nullKind
  defines := #[]
  code := (← findMessagesForUnparsedSpan (Substring.mk input start stop) msgs fm)
}

def addMissingSubstrs (stxs : Array Syntax) (inputCtx : Parser.InputContext) : Id (Array (Syntax ⊕ Substring)) := do
  -- HACK: fill in the (malformed) source that was skipped by the parser
  let mut last : String.Pos := 0
  let mut stxOrStrs : Array (Syntax ⊕ Substring) := #[]
  for stx in stxs do
    let some this := stx.getPos?
      | stxOrStrs := stxOrStrs.push (.inl stx)  -- empty headers have no info
        continue
    if this != last then
      let missedStr := Substring.mk inputCtx.input last this
      stxOrStrs := stxOrStrs.push (.inr missedStr)
    stxOrStrs := stxOrStrs.push (.inl stx)
    last := stx.getTrailingTailPos?.getD this
  return stxOrStrs

def formatMessages (log : Array Message) : IO (Array (MessageSeverity × String)) := do
  let withNewline (str : String) :=
    if str == "" || str.back != '\n' then str ++ "\n" else str
  log.mapM fun msg => do
    let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
    let txt := withNewline <| head ++ (← msg.data.toString)
    pure (msg.severity, txt)

unsafe def go (mod : String) (out : IO.FS.Stream) : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    let modName := mod.toName

    let sp ← Compat.initSrcSearchPath
    let sp : SearchPath := (sp : List System.FilePath) ++ [("." : System.FilePath)]
    let fname ← do
      if let some fname ← sp.findModuleWithExt "lean" modName then
        pure fname
      else
        throw <| IO.userError s!"Failed to load {modName} from {sp}"
    let contents ← IO.FS.readFile fname
    let fm := FileMap.ofString contents
    let ictx := Parser.mkInputContext contents fname.toString
    let (headerStx, parserState, msgs) ← Parser.parseHeader ictx
    let imports := headerToImports headerStx
    enableInitializersExecution
    -- TODO: still parse (but don't elaborate) in presence of import errors
    let env ←
      try
        Compat.importModules imports {}
      catch e =>
        let spos := headerStx.raw.getPos?.getD 0
        let pos  := ictx.fileMap.toPosition spos
        let msgs := msgs.add { fileName := ictx.fileName, data := toString e, pos := pos }
        let msgs := Compat.messageLogArray msgs
        let items : Array ModuleItem := #[{
          range := some (fm.toPosition 0, fm.toPosition contents.endPos)
          kind := nullKind
          defines := #[]
          code := (← findMessagesForUnparsedSpan contents.toSubstring msgs fm)
        }]
        let msgs ← formatMessages msgs
        let outputJson := Json.mkObj [("messages", Json.arr (msgs.map toJson)),
                                  ("commands", Json.arr (items.map toJson))]
        out.putStrLn (toString outputJson)

        return (0 : UInt32)
    let pctx : Context := {inputCtx := ictx}

    let commandState := {env, maxRecDepth := defaultMaxRecDepth, messages := msgs}
    let cmdPos := parserState.pos
    let cmdSt ← IO.mkRef {commandState, parserState, cmdPos}

    processCommands pctx cmdSt

    let cmdStx := (← cmdSt.get).commands

    let infos := (← cmdSt.get).commandState.infoState.trees
    -- TODO: hide silent messages
    let msgs := Compat.messageLogArray (← cmdSt.get).commandState.messages

    let mut items : Array ModuleItem := #[]
    let mut lastPos : String.Pos := 0
    for cmd in #[headerStx] ++ cmdStx do
      if let some thisPos := cmd.getPos? then
        if thisPos != lastPos then
          let missedItem ← ModuleItem.ofUnparsed ictx.input lastPos thisPos fm msgs
          items := items.push missedItem
        lastPos := cmd.getTrailingTailPos?.getD thisPos
      let hl ← (Frontend.runCommandElabM <| liftTermElabM <| highlight cmd msgs infos) pctx cmdSt
      let defs := hl.definedNames.toArray

      let range := cmd.getRange?.map fun ⟨s, e⟩ => (fm.toPosition s, fm.toPosition e)

      items := items.push {
        defines := defs,
        kind := cmd.getKind,
        range := range,
        code := hl
      }

    let msgs ← formatMessages msgs
    let outputJson := Json.mkObj [("messages", Json.arr (msgs.map toJson)),
                                  ("commands", Json.arr (items.map toJson))]
    out.putStrLn (toString outputJson)

    return (0 : UInt32)

  catch e =>
    IO.eprintln s!"error finding highlighted code: {toString e}"
    return 2

unsafe def main : (args : List String) → IO UInt32
  | [mod] => do
    go mod (← IO.getStdout)
  | [mod, outFile] => do
    if let some p := (outFile : System.FilePath).parent then
      IO.FS.createDirAll p
    IO.FS.withFile outFile .write fun h =>
      go mod (.ofHandle h)
  | other => do
    IO.eprintln s!"Didn't understand args: {other}"
    IO.println helpText
    pure 1
