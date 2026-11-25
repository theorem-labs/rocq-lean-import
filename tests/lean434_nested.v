From LeanImport Require Import Lean.

(* RLI434.half takes an autoParam argument (dumps/lean434/src/RLI434AutoParam.lean), so the closure of the
   export's two roots, RLI434.half and RLI434.half_four, holds autoParam, Lean.SourceInfo and the nested
   inductive Lean.Syntax; and the syntax of `by decide`, RLI434.half._auto_1, holds string literals, so
   Char.ofNat and Char.ofNatAux (export line 10766). autoParam and Lean.Syntax were never a root of this export,
   and neither is refused before the fix: the src/ of 69c45616, the parent of the fix 17ac70f1
   (ci/build-9.2-cut.sh --revert-fix), imports Lean.SourceInfo, Lean.Syntax and autoParam and refuses
   Char.ofNatAux first (Stack overflow.). The base source refuses Nat.pow_pos._f (export line 9131) first. *)
Set Lean Error Mode "Fail".
Lean Import "../dumps/lean434/autoparam.ndjson".

Check Lean_Syntax.
Check autoParam.
Check RLI434_half.
Check RLI434_half_four.
