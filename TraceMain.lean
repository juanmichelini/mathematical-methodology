import MathematicalMethodology.Trace

open MM MM.Strategic MM.Trace

/-- `lake exe trace [dir] [first|all]`: write the traces to `dir` (default `trace/`, which is
git-ignored; nothing here is committed) and print a summary.

* `first`: only the first search (64 candidates, a few seconds, small files);
* `all` (default): both searches, a few minutes and about 150 MB (the second search proposes
  about 400 000 conjectures).

The step budget `paciencia` is 30 (foundations' value); `TRACE_PACIENCIA=n` overrides it.
(Reading it at run time also keeps Lean from computing the searches at start-up, before `main`.)

Exits non-zero if the kept functions are not the 3 (first search) and 28 (second search) of
Appendix B, or differ from `selectFirst`/`selectSecond`. -/
def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "trace"
  let all := args.getD 1 "all" != "first"
  IO.FS.createDirAll dir
  let paciencia := ((← IO.getEnv "TRACE_PACIENCIA").bind String.toNat?).getD 30
  let fstT := traceFirst paciencia
  let fst := selectFirst paciencia
  let sndT := if all then traceSecond fst paciencia else []
  let snd := if all then selectSecond fst paciencia else []
  -- names of the kept functions, by candidate index
  let nameFst (i : Nat) : Option String :=
    ((fstT.filter keptFirst).map (·.index)).idxOf? i |>.map (s!"f{·}")
  let nameSnd (i : Nat) : Option String :=
    ((sndT.filter keptSecond).map (·.index)).idxOf? i |>.map (s!"f{fst.length + ·}")
  let texts := (MM.Export.proofsOf datas (fst ++ snd)).1
  let both (f : String → List CandTrace → String) : String :=
    f "first" fstT ++ (if all then "\n" ++ f "second" sndT else "")
  IO.FS.writeFile (dir / "enumerated.txt") (enumeratedFile fstT sndT)
  IO.FS.writeFile (dir / "conjectured.txt") (both conjecturedFile)
  IO.FS.writeFile (dir / "attempted.txt") (both attemptedFile)
  IO.FS.writeFile (dir / "proved.txt")
    (provedFile "first" fstT keptFirst nameFst texts ++
     (if all then "\n" ++ provedFile "second" sndT keptSecond nameSnd texts else ""))
  let summary := "\n".intercalate (summaryOf "first" fstT keptFirst ++
    (if all then summaryOf "second" sndT keptSecond else []))
  IO.FS.writeFile (dir / "summary.txt") (summary ++ "\n")
  IO.println summary
  IO.println s!"traces written to {dir}"
  let ok := (fstT.filter keptFirst).length == fst.length && (paciencia != 30 || fst.length == 3) &&
    (!all || ((sndT.filter keptSecond).length == snd.length && (paciencia != 30 || snd.length == 28)))
  unless ok do IO.eprintln "FAIL: the kept functions differ from selectFirst/selectSecond or from Appendix B"
  return if ok then 0 else 1
