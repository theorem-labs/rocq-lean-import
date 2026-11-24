# Lean 4.34 regression fixtures

Exports use Lean **4.34.0** (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`)
and lean4export **`076e8e57`** (NDJSON format **3.1.0**). The library exports
come from `Init`. The other captures use the four sources in `src/`.

Put the Lean toolchain's `bin` directory and `lean4export` on `PATH`. For an
export of a module `M` in `src/`, copy `M.lean` to a scratch directory and run
these commands there before the export command:

```sh
lean -o M.olean M.lean
export LEAN_PATH="$PWD:$(lean --print-prefix)/lib/lean"
```

Run each export command with stdout written to the indicated file. The
strings export omits the original `decide` cases. `String.length` still
requires a large closure, so Git stores a ZIP archive with one member.

`../init.ndjson.zip` and `../stdlib.ndjson.zip` both contain `lean.version`
`4.30.0` (Git hash `d024af099ca4bf2c86f649261ebf59565dc8c622`). Both select
the new NDJSON path under the version rule. The existing tests parse both
archives without translating their declarations. The original text dumps
select the legacy path.

## Captures

| File | Command or purpose | SHA-256 |
| --- | --- | --- |
| `bitvec_uint32.ndjson` | `lean4export Init -- BitVec.ofNatLT UInt32.ofBitVec UInt32.toBitVec UInt32.add` | `9b69f3f9080aa896c1480327c755bfbed66ccf7d0ea90e998b10fef8f6b2395a` |
| `pow.ndjson` | `lean4export Init -- Nat.pow_zero Nat.pow_succ Nat.pow_one Nat.pow_pos Nat.pow_le_pow_right Int.pow_succ Nat.shiftLeft_eq Nat.shiftRight_eq_div_pow _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.div_two_le_of_lt_two _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.zero_lt_pow` | `8365bcaa62441901940057ea6cc2c50b55c51ebf40746ec1d0868d3059b938da` |
| `char.ndjson` | `lean4export Init -- Char.ofNatAux Char.ofNat` | `92c1b725a15a2ce4f72d4fb3fbe7dcf10ce6c54ca31a34bdfccae90ecfb3dbae` |
| `strings.ndjson.zip` | `lean4export RLI434Strings -- RLI434.ab_length RLI434.astral RLI434.astral_length > strings.ndjson`, then ZIP (deflate, level 9, single member `strings.ndjson`). Member SHA-256: `8ea287b6be6405eb2a819120ae94998a981c5b4932a6a9ef2a3eddd2a33eb4db`. | `4e23bce574f5fdfe047ce3582ddcb51c3896d67825a88160c67013ded80b511d` |
| `autoparam.ndjson` | `lean4export RLI434AutoParam -- RLI434.half RLI434.half_four` | `1d565c5fc801b1a5bbea547708388b23747e406c6348a29ead6c3af39ca1be29` |
| `linear.ndjson` | `lean4export Init -- 'Nat.«Internal».Linear.ExprCnstr.denote_toNormPoly'` | `4f500ee24602d95ec51e926a58faef0d1f62e38bc2f4caf5e7057fedb5d3a8d0` |
| `bigint.ndjson` | `lean4export RLI434BigInt -- RLI434.big RLI434.big_ok RLI434.big_fields RLI434.boundedVal RLI434.boundedVal_val RLI434.omega_big RLI434.window` | `6ddedad371f15177ff9c59126493c0daa8bc89be2e014b6615b27a3357758973` |
| `timeout.ndjson` | `lean4export RLI434Timeout -- RLI434T.fast RLI434T.slow_sum RLI434T.slower_sum RLI434T.after_slow RLI434T.needs_slow RLI434T.needs_slower` | `a8411c6f9c9063724895df8329bafdd0ba2934eec791bc9ba1c9ea5c5a527029` |
| `bitvec_only.ndjson` | `lean4export Init -- BitVec` | `6033908788afecb40929ff381d0168ff72490107be0fa2324f22b3b041f1350a` |
| `predeclared.ndjson` | `lean4export Init -- Char UInt32.size Nat.isValidChar Nat.pow Or And ULift` | `656869c1a35b48fc2fdcc0a16e7040020c59a3f3e0d6aa318ee52b39cfd82307` |
| `src/RLI434AutoParam.lean` | Lean source for `autoparam.ndjson`. | `89c539317c51db6115c38ff997cc826a68989dfec1a15e4de4e3e5c62f62b927` |
| `src/RLI434BigInt.lean` | Lean source for `bigint.ndjson`. | `c5e679bfcfb6bd2bd37eed68d1535d885b53d0ec7724a05c4c1d6212093985c8` |
| `src/RLI434Strings.lean` | Lean source for the ZIP member `strings.ndjson`. | `1ede0487aaf9edc69d6c7b1214adb1505fc7d51a108bbe8f5997f0107c4f053d` |
| `src/RLI434Timeout.lean` | Lean source for `timeout.ndjson`. | `860a0246061ae0b87e70dac9a7f8eefc36c46a0af99e3dcee725e771e0f8cbe9` |

## Derived fixtures

Each row gives the source file and the edited lines. Line numbers are
one-based. Lines not described in a row are unchanged. For slices, the range
excludes all source lines outside the range.

| File | Source and edits | SHA-256 |
| --- | --- | --- |
| `negative_fin_field.ndjson` | `bitvec_only.ndjson` lines 1–233 with line 1 `meta.lean` replaced by `{"version":"4.16.9"}`. Add expressions on lines 234–236. These copy the constructor products from expression 157 and replace binder 3 type with Nat (expression 1). Append the original line 234 with `ctors[0].type` set to `180`. | `257953d16cdf946fc976b812c68a934a4079b4c773479009f93e6403989d61ef` |
| `negative_fin_sort.ndjson` | `bitvec_only.ndjson` lines 1–233. Add level 5 (`succ` of level 1) on line 234, the sort `Sort 2` (expression 178) on line 235 and `Nat → Sort 2` (expression 179, binder `n`) on line 236. Append the original line 234 (`Fin`) with `types[0].type` set to `179`, so that `Fin` is in `Type 1` instead of `Type`. | `d8e3230d375db3bc9d17fac887803f66e702c903ffa6c841a2a95efad8628a9f` |
| `negative_le_field.ndjson` | `bitvec_only.ndjson` lines 1–181. Add expressions on lines 182–184. These copy the constructor products from expression 83 and replace binder 3 type with Nat (expression 1). Append the original line 182 with `ctors[1].type` set to `138`. | `68be0632e5c8b0a3767d9848e9906f479644b8c43faf6d8e0fe738f8cee4239e` |
| `negative_le_type.ndjson` | `bitvec_only.ndjson` lines 1–181. Add two `forallE` records at lines 182 and 183, copying the original type but changing its final sort to Type (expression 0). Append line 182 with `types[0].type` set to 137. | `a57bad502ec4fb5cfb03dc6106b8fd75e6b76ef8f0590d6a065da175fc5c01b5` |
| `negative_pow_body.ndjson` | `pow.ndjson` lines 1–869. Line 820 (expression 604): change `lam.body` from 603 to 445, so `Nat.pow` returns zero. Keep `Nat.pow_zero` unchanged. | `6c30b0b4e21d7e4851fc8326f581f7b2d7e1c36ef831cf7bce7e0a774403734d` |
| `negative_pow_proof.ndjson` | `pow.ndjson` lines 1–1014. Line 1014: change the proof ID from 767 to 646 (the proof of `Nat.pow_zero`). | `34455d3934644db6635fe60a1619000b9d03e7c9d5142ebf9f544a1774a2883f` |
| `negative_pow_statement.ndjson` | `pow.ndjson` lines 1–1014. Line 1008 (expression 762): change `app.arg` from 761 to 759, making the right-hand side `n^m`. Keep the original `rfl` proof. | `123f10f646b6c35f9eabbe8554ec02853a495d5a22350f1cc7aaeba6d5a10da7` |
| `negative_size_body.ndjson` | `pow.ndjson` lines 1–869. Replace `meta.lean` on line 1 with `{"version":"4.16.9"}`. Append lines 870–879: two name nodes for `UInt32.size`, literal 5, `def UInt32.size : Nat := 5`, the name `sizeIsFive`, a reference to `UInt32.size`, the two equality applications, the `rfl` application on `UInt32.size`, and `thm sizeIsFive : UInt32.size = 5`. | `260b491ee660eca065cb700e5f7bec7d5722ba673c454c055ea1f1aa235163af` |
| `parse_bad_format.ndjson` | `timeout.ndjson`: change line 1 `meta.format.version` to `9.9.9`. Remove all lines from line 4 on. | `eb5b2a23c9b11127b3ddad1a726ef469ecff8ff98686c8966d944267b7373c0c` |
| `parse_empty.ndjson` | Zero bytes. Remove every line of `timeout.ndjson`. | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `parse_id.ndjson` | `timeout.ndjson` lines 1–131: append lines 132–136 (bad expression ID `90` references absent ID `9999`, its dependent `91`, independent sort `92`, the name `RLIIndependent`, and an axiom of that independent type). | `90fc390148199ad62f23246d79549de88703c4f7ffa2a7c9c6e23a3e976041b6` |
| `parse_messages.ndjson` | `timeout.ndjson` lines 1–131: replace line 131 with its copy without `hints`. Add `{"notARecord":true}` on line 132. Restore the original line 131 on line 133. | `1b9aee677977407adf4a10fdd8526fb56c9bc2f1e051b8cc243f900063d5c9af` |
| `parse_mutual.ndjson` | `timeout.ndjson` lines 1–131: insert a copy of line 51 at line 52 with two `types` elements, then a blank line at 53. | `ab7a5afad54b5ef66b18ce06c72f13ba631546b8aa6085d4642667a2dfc1fba4` |
| `parse_no_meta.ndjson` | `timeout.ndjson`: remove line 1 and all lines from line 4 on. Only name ID 1 and level ID 1 remain. | `1c84118851b0dedd040628371f0f5116a485414f2c5ec23a6ccf3e6e6de1367f` |
| `parse_truncated.ndjson` | `timeout.ndjson` lines 1–131: append the bytes `{"ie":` without a newline (line 132). | `74b2c58cf7ffbfbcfe4dad85a0cc8e0ed5bce6a971c7b08d31be76bbcca40676` |
| `path_3.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "3.51.1"}`. | `fb98c89683c3ab588a849e2503ead8112dd12226e9d1ac244a8ba59a0100b4d3` |
| `path_4169.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "4.16.9"}`. | `e3ba42a395e4ba8ca7241d9428fbb1c30b8b59ff2c81a5f71d8f266278067fc8` |
| `path_4170.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "4.17.0"}`. | `97e151de5ddfcc21be24540a318c063a5bee06457c92e92d3d5a8175fd22e093` |
| `path_4180.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "4.18.0"}`. | `d2a440cf1207e0c04e7ee451be4154e2e75ac8f28896769e398081717f0f71d7` |
| `path_4300.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "4.30.0"}`. | `be89ca8e0ba9e1bff5de4838b9da619d839ee7e6ea421c7a3d6811f7150e1270` |
| `path_500.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "5.0.0"}`. | `653f55ca5189010ae7a86fe03432ec7aa5f2d9a733c236f6ab91ac217179def9` |
| `path_bad_version.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "nightly-2025-01-01"}`. | `e00f52809ec0e686f711728eae6f6f2956a56f1bb988f7d959603d2d495f3f5a` |
| `path_empty_version.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": ""}`. | `fa034392f10d014b7f76bb6cb220735034a62ae71baf23d6db56d9ee79c4f42d` |
| `path_nightly.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "4.18.0-nightly-2025-01-01"}`. | `f7c9980b5a7e2912a240117ebacb3a404d6dd61d18fe96bc2e97c8fe10b2b498` |
| `path_no_lean.ndjson` | `bitvec_only.ndjson`, line 1: remove `meta.lean`. | `f30b57e92f4ae4a732fd591ca55f5bcc0ab6b33c40bd560b7e3e298deba5469f` |
| `path_no_version.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{}`. | `92fd151613abce3118960ee544780107e2e794b4b37dac7723ebc6a4e8f1a132` |
| `path_numeric.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": 434}`. | `cdd72022fdce3e6172cfb3be408c9ef407d1ecf9d3e6fa22f1deb6d1d8625b31` |
| `path_old.txt` | `bitvec_only.ndjson`: omit line 1. Convert each remaining line, in order, to the corresponding old-format record. See the conversion table below. | `e7a21cbc6d5beefaa3d93488d5ef41c34a28224fece0926147d535e2c348db9e` |
| `path_rc.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "4.17.0-rc1"}`. | `1cc76e6c7f206855f963c566c7ea0e579945d4054ecef5a1f85deb2d8565d1fd` |
| `path_v.ndjson` | `bitvec_only.ndjson`, line 1: replace `meta.lean` with `{"version": "v4.17.0"}`. | `53ab1076398e87d97e8ce421bbc7b31236a443fef9685538a0f19ba54f5df899` |
| `pred_and.ndjson` | `predeclared.ndjson` lines 1–1114. On line 1114, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `9a8bb4bd4068ed081c50fc35812254b60eb954e49e6b92f0d9f3ca4514de71b3` |
| `pred_bitvec.ndjson` | `bitvec_only.ndjson` lines 1–1003, replace `meta.lean` on line 1 with `{"version":"4.16.9"}`. On line 1003, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `3f7cb2de6de524deac602b7bad25c2877622839585d3f6a2e3123d8978b38594` |
| `pred_char.ndjson` | `predeclared.ndjson` lines 1–1209, replace `meta.lean` on line 1 with `{"version":"4.16.9"}`. On line 1209, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `5f763bbae44c2bec3c0b97b4991b1e748707093bfa26d26aab77116f89d14ee3` |
| `pred_duplicate.ndjson` | `predeclared.ndjson` lines 1–1027; append a byte-for-byte copy of line 1027 (`UInt32`). | `bc5ae00d588f3e727fc1bec883c9e7991f4bd2ff49a9eabeaf03096d705f0d0b` |
| `pred_eq.ndjson` | `pow.ndjson` lines 1–101. On line 101, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `388f0eb104725ef170e56472753872b39b8d210753a0ffce01b170f221a5bd80` |
| `pred_fin.ndjson` | `bitvec_only.ndjson` lines 1–234. On line 234, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `0c17329cb48191629229a2d439dd6a2e59dccfd55b543eb86197efa709f05bd7` |
| `pred_nat.ndjson` | `bitvec_only.ndjson` lines 1–51. On line 51, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `a8dbf714685abc4f2c060199ffebf9e789007b3f69f9b347a5973fb354b663dd` |
| `pred_nat_isvalidchar.ndjson` | `predeclared.ndjson` lines 1–1137, replace `meta.lean` on line 1 with `{"version":"4.16.9"}`. On line 1137, set `def.type` to expression ID 0 (Type). | `9282929c25274a733a8b6efa9b320c8bb897205dab0eb0e55e55c71c1b9390ad` |
| `pred_nat_le.ndjson` | `bitvec_only.ndjson` lines 1–182. On line 182, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `3d57fd41b49ff071cc446c5872f2f8e543fa9244f3ca6390a2d37586f1e93495` |
| `pred_nat_pow.ndjson` | `bitvec_only.ndjson` lines 1–945, replace `meta.lean` on line 1 with `{"version":"4.16.9"}`. On line 945, set `def.type` to expression ID 0 (Type). | `2dd379057081c4b7b1eb41101a2c7444b1b05c2715f8aaf9f99944c67d99ddc0` |
| `pred_or.ndjson` | `predeclared.ndjson` lines 1–1080. On line 1080, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `c0070621f8b571a4a21b72f66070f76d3b55a9f2d83fcbdffd6e36dd0957f516` |
| `pred_uint32.ndjson` | `predeclared.ndjson` lines 1–1027, replace `meta.lean` on line 1 with `{"version":"4.16.9"}`. On line 1027, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `cd726d99638f1df739bbfefdfde3b03bcc4621202023397238b14949b9783f27` |
| `pred_uint32_size.ndjson` | `predeclared.ndjson` lines 1–1215, replace `meta.lean` on line 1 with `{"version":"4.16.9"}`. On line 1215, set `def.type` to expression ID 0 (Type). | `6b5699e06b2da97ac4a1b0fac059b76c10142487317153d1d5915a73f0bb3d31` |
| `pred_ulift.ndjson` | `predeclared.ndjson` lines 1–1251. On line 1251, set `inductive.ctors`, `types[0].ctors`, and `recs` to empty arrays (constructor count mismatch). | `cb616a22a0226829f4d756765fd37e18fc0d56c219743b9b7ac595c5427f9e1f` |
| `string_mk_4250.ndjson` | Hand-written around `pow.ndjson` lines 2–101 (`Nat` on line 51, `Eq` on line 101). Line 1: a metadata line whose `lean` object is `{"version":"4.25.0"}`. Lines 102–180 are written by hand, each id the next one: `structure Char where mk :: val : Nat` (line 107); `def Char.ofNat (n : Nat) : Char := Char.mk n` (line 115); `inductive List.{u} (α : Type u)` with `nil` and `cons (head : α) (tail : List α)` (line 135); `structure String where mk :: data : List.{0} Char` (line 143); `def RLI425.lit : String := "aé∀𝔸"` (line 147), a literal of the code points 97, 233, 8704 and 120120, one to four bytes of UTF-8 each; and `theorem RLI425.lit_eq : RLI425.lit = String.mk [Char.ofNat 97, Char.ofNat 233, Char.ofNat 8704, Char.ofNat 120120] := Eq.refl.{1} String RLI425.lit` (line 180). The inductive records have empty `recs`. | `52c2e6df58513f0b64dda58c3d53b2e3c8f6dbb4b25a3966e9a55e7e0084f9c1` |
| `string_mk_4260.ndjson` | `string_mk_4250.ndjson`, line 1: `lean.version` `4.26.0`. | `aaf45d4d6b63bd2bb16201f134669703bb55b88049a55fcd23d8a43958a8c6e2` |
| `timeout_cases.ndjson` | `timeout.ndjson`: delete declaration lines 2195 and 2228 (`slow_sum` and `needs_slow`). Keep the numbered expression records. | `769cbe8e8784cebe340357c7f7f33a2ff870cba6bcb0f89dad8cbcece58aa141` |
| `timeout_inductive.ndjson` | `timeout.ndjson` lines 1–2194: the records before the declaration of `RLI434T.slow_sum` (line 2195), whose statement `T` is expression 1689 and whose `decide` proof `P` is expression 1704. Append lines 2195–2202: the names `RLI434T.SlowBox`, `RLI434T.SlowBox.mk` and `h`; `fun (n : T) => T` (expression 1705); its application to `P` (1706); `RLI434T.SlowBox` (1707); `(h : (fun n => T) P) → RLI434T.SlowBox` (1708); and `inductive RLI434T.SlowBox : Type` with that one constructor and empty `recs`. Checking the constructor's type checks `P`, which takes as long as checking `slow_sum`. | `37fd3cdd29c55cd39ae0537bc07bd99216631d5fcdba167876b0458bca1fece3` |

### Old text format conversion

`path_old.txt` rewrites lines 2–1003 of `bitvec_only.ndjson` one for one. It
keeps each name, universe and expression index. The following table gives the
fields after the index (declaration records have no leading index). Omitted
JSON fields, such as inductive recursor descriptions, have no text-format
counterpart in these records.

| NDJSON record | Text record |
| --- | --- |
| `str` / `num` name | `#NS pre str` / `#NI pre i` |
| `succ`, `param`, `max`, `imax` | `#US base`, `#UP name`, `#UM a b`, `#UIM a b` |
| `sort`, `bvar`, `const`, `app` | `#ES level`, `#EV index`, `#EC name us…`, `#EA fn arg` |
| `lam`, `forallE` | `#EL binderInfo name type body`, `#EP binderInfo name type body` |
| `proj`, `natVal` | `#EJ typeName idx struct`, `#ELN value` |
| `def` | `#DEF name type value levelParams…` |
| `inductive` | `#IND numParams name type ctorCount (ctor.name ctor.type)… levelParams…` |

Binder tags `#BD`, `#BI`, `#BS`, and `#BC` denote default, implicit, strict
implicit, and instance implicit binders, respectively.
