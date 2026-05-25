# Design: Regenerate Dumps With Current lean4export

## Context

`rocq-lean-import` currently consumes old line-oriented Lean export dumps with
records such as `#DEF`, `#AX`, `#IND`, and numeric tables for names,
universes, and expressions. The checked-in dump fixtures under `dumps/` are in
that old format, and the repository does not currently contain the Lean source
files used to produce the custom regression dumps.

The new target is `lean4export` master and the Lean version pinned by that
repository. As of 2026-05-25, `lean4export` master pins
`leanprover/lean4:v4.30.0-rc2` in `lean-toolchain`. Current `lean4export`
emits Lean 4 NDJSON export format `3.1.0`: a metadata object followed by
primitive table records for names, levels, and expressions, and declaration
records for axioms, definitions, theorems, opaques, quotient declarations,
inductives, constructors, and recursors.

## Goals

- Regenerate maintained dump fixtures from current `lean4export` output.
- Use upstream Lean source modules for upstream-backed fixtures such as `core`,
  `init`, and `stdlib`.
- Add local Lean source files for custom regression fixtures such as `ulift`,
  `pnni.out`, `anomaly_print_projections`, `bin_tree`, `list`, `logic`, and
  `quot`.
- Add support for NDJSON export format `3.1.0` while preserving compatibility
  with old line-oriented dumps during the transition.
- Keep the existing Rocq translation pipeline stable where possible by mapping
  NDJSON records into the current internal action model.

## Non-Goals

- Do not require Mathlib regeneration in the first milestone.
- Do not redesign the whole importer around Lean 4 declarations.
- Do not remove the old parser immediately.
- Do not support arbitrary third-party Lake projects beyond the maintained
  manifest workflow.
- Do not solve every semantic import failure introduced by newer Lean in this
  first milestone.

## Architecture

The existing importer translation logic should remain the stable core. The
first major change is a second parser frontend for current `lean4export`
NDJSON.

`Lean Import <file>` should detect the dump format from the first meaningful
line:

- old line-oriented format continues through the current `LeanParse.do_line`
  path;
- NDJSON format goes through a new parser module, `LeanParseNdjson`,
  which decodes JSON records and emits the existing `LeanExpr.action` values
  consumed by `lean.ml`.

The parser boundary should keep format-specific work out of the translator.
Name handling, universe-instantiation logic, quotient handling, Rocq
declaration generation, and existing error-mode behavior should continue to
live in the current importer pipeline.

## NDJSON Mapping

The NDJSON parser should maintain parser-local tables for Lean names, universe
levels, and expressions, mirroring the old parser's table behavior. It should
map export records into existing OCaml types:

- names into `LeanName.t`;
- levels into `LeanExpr.U.t`;
- expressions into `LeanExpr.expr`;
- axioms into `Ax`;
- definitions, theorems, and supported opaques into `Def` or `Ax` according to
  importer semantics;
- inductive groups into `Ind` entries using the exported inductive and
  constructor data;
- quotient declarations into the existing quotient action;
- projections, natural literals, string literals, lambdas, Pis, lets, apps,
  constants, and sorts into the existing expression variants.

Recognized NDJSON records that cannot yet be represented in the current model
should fail with a precise unsupported-feature message instead of an assertion.
The parser should preserve useful source identity in errors: file line number,
record kind, and declaration name when available.

## Fixture Sources And Manifest

Add a maintained Lean fixture source tree at `lean/fixtures/` for local
regression sources. These local files should be the source of truth for custom
dump fixtures that are not cleanly backed by upstream Lean modules.

Add a manifest at `lean/fixtures/manifest.toml`, mapping each maintained dump
to one of:

- an upstream Lean module exported at the `lean4export` pinned Lean version;
- a local Lean fixture file in the repository.

The manifest should also record enough lock information to make regeneration
auditable:

- `lean4export` repository URL;
- `lean4export` commit;
- `lean-toolchain` value;
- export format version;
- whether the dump is part of default regeneration or an expensive optional
  target.

The `stdlib` dump should be maintained in the manifest but tagged as an
expensive optional target rather than part of the default fast regeneration
set. `mathlib.out.zip` should remain outside the first milestone.

## Regeneration Workflow

Add a `make regenerate-dumps` target backed by
`scripts/regenerate-dumps.sh`.

The workflow should:

1. Locate or clone `lean4export` at the locked commit.
2. Verify its `lean-toolchain` matches the manifest lock.
3. Build `lean4export` with `lake build`.
4. Export each manifest entry using the correct `lake env` context.
5. Write deterministic NDJSON dump files under `dumps/`.
6. Fail if a generated dump is empty or lacks the expected metadata record.
7. Report the `lean4export` commit, Lean toolchain, and export format in the
   regeneration output.

The script should fail early with actionable messages when `lake`, `lean`, or
`elan` is missing, when `lean4export` cannot be built, when an upstream module
cannot be exported, or when the manifest lock is inconsistent.

## Data Flow

The import path should be:

1. `Lean Import` opens the dump and initializes shared import state.
2. The format detector reads the first non-empty line.
3. The selected parser updates parser-local tables or returns a declaration
   action.
4. Declaration actions flow into the existing importer logic.
5. Rocq tests import regenerated dumps and check focused behavior.

The regeneration path should be:

1. Read the manifest.
2. Resolve upstream modules and local fixture files.
3. Run `lean4export` in the matching Lake environment.
4. Write dump files.
5. Validate basic dump shape.
6. Run focused parser/import tests.

## Error Handling

Importer errors should distinguish:

- malformed NDJSON;
- valid NDJSON with an unsupported record kind;
- valid NDJSON that cannot yet be mapped to the current internal model;
- successful parsing followed by Rocq translation failure.

Regeneration errors should distinguish:

- missing Lean tooling;
- failed `lean4export` build;
- manifest/toolchain mismatch;
- unexportable upstream module;
- empty or malformed generated dump.

## Testing

Testing should be layered so failures identify the broken stage.

Parser unit tests should cover small checked-in NDJSON snippets for names,
universes, expressions, definitions, axioms, inductives, projections, literals,
and quotient-related declarations.

Regeneration smoke tests should cover:

- one small upstream module export using the pinned `lean4export` toolchain;
- one local custom fixture export;
- validation that generated dumps are non-empty and start with the expected
  NDJSON metadata.

Import tests should update existing `tests/*.v` files to consume regenerated
NDJSON dumps. Line-range tests should remain only where regenerated ordering is
stable enough to make them meaningful; otherwise tests should prefer full-file
imports and named behavior checks like the current `ulift.v`.

Compatibility tests should keep at least one old-format fixture during the
transition so the old parser path is not accidentally broken.

## Success Criteria

- A documented command regenerates maintained dumps from `lean4export` master's
  pinned Lean version.
- Upstream-backed fixtures use upstream Lean modules.
- Custom regression fixtures have local Lean source files in the repository.
- `Lean Import` accepts NDJSON export format `3.1.0`.
- Existing translation logic is reused where possible through the existing
  `LeanExpr.action` model.
- Focused Rocq tests exercise regenerated dumps through the new parser.
