import SubVerso.Highlighting
import SubVerso.Examples
import SubVerso.Examples.Env
import SubVerso.Examples.Slice
import SubVerso.Helper.Netstring
import Lean.Data.Json
import Lean.Data.NameMap

open SubVerso.Examples (loadExamples Example)
open Lean.FromJson (fromJson?)

open SubVerso

section
open Lean Elab Command
open SubVerso.Examples.Slice

elab "#test_slicing" s:str out:ident c:command : command => do
  let {original := _, residual, sliced} ← sliceSyntax c

  let mut log := ""

  log := log ++ s!"Original:\n{Syntax.prettyPrint c}\n"
  log := log ++ s!"Residual:\n{Syntax.prettyPrint residual}\n"
  for (s, stx) in sliced.toArray do
    log := log ++ s!"Slice {s}:\n{Syntax.prettyPrint stx}\n"

  let use := s.getString
  if let some stx := sliced[use]? then
    elabCommand stx
  else
    logInfo m!"Slice '{use}' not found"
    elabCommand residual
  elabCommand <| ← `(def $out := $(quote log))

set_option pp.rawOnError true in
#test_slicing "foo" sliceLog
def heya : IO Unit := do
  IO.print "Hey"
  -- !! begin foo
  IO.println " there"
  /- Bigger comment
  -/
  -- !! end foo
  let x := 33 -- !! begin foo
  if x > 3 then pure () -- !! end foo
  if x == 3 /-
    !! begin foo
  -/ || true /- !! end foo -/ then pure ()
  let _ := [1, 2/- !! begin foo-/, 3/- !! end foo-/]
  pure ()

/-- Lean versions 4.10.0 and earlier had some issues with Syntax.prettyPrint. They were fixed in 4.11, but as that's not really what's being tested, both are OK. -/
def expectedLogOld :=
  "Original:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  -- !! begin foo\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  -- !! end foo\n  let x := 33 -- !! begin foo\n  if x > 3 then pure () -- !! end foo\n  if x == 3 /-\n    !! begin foo\n  -/ || true /- !! end foo -/ then pure ()\n  let _ := [1, 2/- !! begin foo-/, 3/- !! end foo-/]\n  pure ( ) \nResidual:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  let x := 33 \n  if x == 3  then pure ()\n  let _ := [1, 2]\n  pure ( ) \nSlice foo:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  let x := 33 \n  if x > 3 then pure () \n  if x == 3  || true  then pure ()\n  let _ := [1, 2, 3]\n  pure ( ) \n"


def expectedLog :=
  "Original:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  -- !! begin foo\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  -- !! end foo\n  let x := 33 -- !! begin foo\n  if x > 3 then pure () -- !! end foo\n  if x == 3 /-\n    !! begin foo\n  -/ || true /- !! end foo -/ then pure ()\n  let _ := [1, 2/- !! begin foo-/, 3/- !! end foo-/]\n  pure ()\nResidual:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  let x := 33 \n  if x == 3  then pure ()\n  let _ := [1, 2]\n  pure ()\nSlice foo:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  let x := 33 \n  if x > 3 then pure () \n  if x == 3  || true  then pure ()\n  let _ := [1, 2, 3]\n  pure ()\n"

end

open Lean in
def exampleArray (examples : NameMap (NameMap α)) : Array α := Id.run do
  let mut exs := #[]
  for (_, inner) in examples do
    for (_, x) in inner do
      exs := exs.push x
  exs

open Lean in
def findVersionString (examples : NameMap (NameMap Example)) : Option String := do
  let demo ← examples.find? `Demo
  let version ← demo.find? `version
  let [(.information, str)] := version.messages
    | none
  str.trim |>.drop 1 |>.dropRight 1

namespace SubVerso

partial
def Highlighting.Highlighted.countProofStates (hl : Highlighting.Highlighted) : Nat :=
  match hl with
  | .seq hls =>
    hls.map countProofStates |>.foldr (· + · ) 0
  | .span _ hl' =>
    hl'.countProofStates
  | .tactics _ _ _ hl' =>
    hl'.countProofStates + 1
  | _ => 0

namespace Examples

def Example.countProofStates (e : Example) : Nat :=
  e.highlighted.map (·.countProofStates) |>.foldl (· + ·) 0

end Examples
end SubVerso

def cleanupDemo (demo : System.FilePath := "demo") : IO Unit := do
  if ← System.FilePath.pathExists (demo / "lake-manifest.json") then
    IO.FS.removeFile (demo / "lake-manifest.json")
  if ← System.FilePath.isDir (demo / ".lake") then
    IO.FS.removeDirAll (demo / ".lake")

open Lean in
def proofCount (examples : NameMap (NameMap Example)) : Nat := Id.run do
  let mut n := 0
  for e in exampleArray examples do
    n := n + e.countProofStates
  n

open Lean in
def checkVersion (expected : String) (examples : NameMap (NameMap Example)) : IO Unit := do
  let v := findVersionString examples
  IO.println s!"Reported version {v}"
  if v != some expected then
    IO.eprintln "Unexpected version!"
    IO.Process.exit 1
  pure ()

open Lean in
def checkHasSorry (examples : NameMap (NameMap Example)) : IO Unit := do
  IO.println "Making sure the `hasSorry example has a sorry"
  let demo ← examples.find? `Demo |>.map pure |>.getD (do IO.eprintln "Demo not found"; IO.Process.exit 1)
  let hasSorry ← demo.find? `hasSorry  |>.map pure |>.getD (do IO.eprintln "hasSorry not found"; IO.Process.exit 1)
  if hasSorry.messages == [(.warning, "declaration uses 'sorry'\n")] then pure ()
  else
    IO.eprintln s!"Expected a sorry warning, got {repr hasSorry.messages}"
    IO.Process.exit 1

open Lean in
def checkIsLinted (examples : NameMap (NameMap Example)) : IO Unit := do
  IO.println "Making sure the linted example is linted"
  let demo ← examples.find? `Demo |>.map pure |>.getD (do IO.eprintln "Demo not found"; IO.Process.exit 1)
  let hasSorry ← demo.find? `linted  |>.map pure |>.getD (do IO.eprintln "linted not found"; IO.Process.exit 1)
  if let [(.warning, str)] := hasSorry.messages then
    -- The phrasing varies a bit in Lean versions, but this is the important part
    if "unused variable `x`".isPrefixOf str then
      return ()

  IO.eprintln s!"Expected a linter warning, got {repr hasSorry.messages}"
  IO.Process.exit 1

open SubVerso.Helper in
def testNetstring (str : String) : IO Unit := do
  let buf ← IO.mkRef {}
  let stream := IO.FS.Stream.ofBuffer buf
  writeNetstring stream str.toUTF8
  buf.modify ({· with pos := 0})
  let some bytes ← readNetstring stream
    | throw <| .userError "Didn't read netstring (unexpected EOF)"
  let str2 := Compat.decodeUTF8 bytes
  if str == str2 then pure ()
  else throw <| .userError s!"Mismatch: expected '{str}' but got '{str2}'"

def testNetstrings := do
  testNetstring ""
  testNetstring "abc"
  testNetstring "abc{}\n"
  let mut longStr := "hello\n"
  for i in [0:100] do
    longStr := s!"{i}({longStr}{longStr})"
  testNetstring longStr


def main : IO UInt32 := do
  IO.println "Checking the slice log"
  -- The pretty-printer used to show the modified syntax had some bug-fixes. We can just check both.
  if sliceLog != expectedLog && sliceLog != expectedLogOld then
    IO.println "Mismatch between expected:"
    IO.println expectedLog
    IO.println "and actual:"
    IO.println sliceLog
    return 1

  IO.println "Checking that the TOML project will load"
  cleanupDemo (demo := "demo-toml")
  let examplesToml ← loadExamples "demo-toml"
  if examplesToml.isEmpty then
    IO.eprintln "No examples found"
    return 1
  else IO.println s!"Found {proofCount examplesToml} proofs"

  IO.println "Checking that the test project generates at least some deserializable JSON with 4.3.0"
  cleanupDemo
  let examples ← loadExamples "demo"
  if examples.isEmpty then
    IO.eprintln "No examples found"
    return 1
  checkVersion "4.3.0" examples
  checkHasSorry examples
  checkIsLinted examples
  let proofCount1 := proofCount examples
  IO.println s!"Found {proofCount1} proofs "

  IO.println "Checking that the test project generates at least some deserializable JSON with 4.8.0"
  cleanupDemo
  let examples' ← loadExamples "demo" (overrideToolchain := some "leanprover/lean4:v4.8.0")
  if examples'.isEmpty then
    IO.eprintln "No examples found with later toolchain"
    return 1
  checkVersion "4.8.0" examples'
  checkHasSorry examples'
  checkIsLinted examples'
  let proofCount2 := proofCount examples'
  IO.println s!"Found {proofCount2} proofs "

  IO.println "Checking that the test project generates at least some deserializable JSON with 4.10.0"
  cleanupDemo
  let examples'' ← loadExamples "demo" (overrideToolchain := some "leanprover/lean4:4.10.0")
  if examples''.isEmpty then
    IO.eprintln "No examples found with later toolchain"
    return 1
  checkVersion "4.10.0" examples''
  checkHasSorry examples''
  checkIsLinted examples''
  let proofCount3 := proofCount examples''
  IO.println s!"Found {proofCount2} proofs "

  if proofCount1 != proofCount2 || proofCount2 != proofCount3 then
    IO.eprintln "Example proof count mismatch"
    return 1
  pure 0
