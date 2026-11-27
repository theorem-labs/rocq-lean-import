Alpha Announcement: Coq is a Lean Typechecker

# Introduction

This plugin provides the `Lean Import` command.

This is an experimental alpha, it is useful to compare how Lean and
Rocq work but probably not much beyond that.

# How do I install this?

This is a standard rocq makefile project and can be installed with

```sh
opam install coq-lean-import
```

# How do I use this?

You need Lean [exported files](https://github.com/leanprover/lean/blob/master/doc/export_format.md)
as input.

For use with Lean 4, you can use [lean4export](https://github.com/leanprover/lean4export).

For use with Lean 3, see [commit ce8ed08172d3247d992dacab08e0e8f59864a57b](https://github.com/coq-community/rocq-lean-import/commits/ce8ed08172d3247d992dacab08e0e8f59864a57b), which is compatible with Coq 8.20 and Lean 3, or [commit c513cee4f5edf8e8a06ba553ca58de5142cffde6](https://github.com/coq-community/rocq-lean-import/commits/c513cee4f5edf8e8a06ba553ca58de5142cffde6) which is compatible with Lean 3 and [coq/coq@a00be77](https://github.com/coq/coq/commit/a00be7706fad3eebbaec3d77ba2bb5cba516fb2b).

For your convenience, I have uploaded a few examples:
- [core.out](https://gist.githubusercontent.com/SkySkimmer/c8705b6d2d561ff7537d1dcabed371a0/raw/1538c7133d1334061e9ced67d3894d0b82cc83a4/core.out) (256KB)
  This corresponds to [core.lean](https://github.com/leanprover/lean/blob/master/library/init/core.lean) in Lean's stdlib.
  It contains 584 basic definitions and inductives such as equality, natural numbers, and the primitive quotient type (without the soundness axiom).
- [stdlib.out](https://gist.github.com/SkySkimmer/92e080ce3a0a89f0f592343076a86521/raw/7353fd277766a41a50cf4d6731443b3bb0e62c2a/stdlib.out) (14MB)
  This is the whole Lean stdlib, totalling 10244 definitions and inductives.
- [mathlib.out.zip](dumps/mathlib.out.zip) (211MB compressed to 56MB, NB: uses git lfs)
  All mathlib (AFAICT): 66400 definitions and inductives (the way I counted may differ a bit from the way Lean counts).

Then start Coq and run

~~~coq
Require Lean.

Lean Import "/path/to/stdlib.out".
~~~
(if using the `mathlib.7z` I uploaded, make sure to decompress it first)

Coq will output many messages:
~~~
line 20: eq
eq is predeclared
line 21: quot
quot registered
line 38: has_add
line 59: has_add.add
line 90: add_semigroup
line 125: add_semigroup.add
line 136: add_semigroup.to_has_add
line 145: has_zero
line 159: has_zero.zero
line 168: has_mul
line 182: has_mul.mul
line 210: semigroup
line 243: semigroup.mul
line 253: semigroup.to_has_mul
line 262: has_one
line 276: has_one.one
line 285: has_le
line 305: has_le.le
line 323: list
line 331: nat
line 348: or
...
~~~

The `Require Lean` is needed for primitive quotient support (and
because quotients talk about equalities it predeclares `eq`). Without
it, you will get an error when trying to declare any value which
depends on `quot`.

Once it has finished working, Coq will output a summary:
~~~
...
line 586592: string.mk_iterator.equations._eqn_1
line 586615: heq.elim
Done!
- 10245 entries (24081 possible instances) (including quot).
- 274 universe expressions
- 14091 names
- 562009 expression nodes
Max universe instance length 4.
0 inductives have non syntactically arity types.
~~~

An "entry" means an axiom or constant, or an inductive type (including
its constructors and recursor), or the primitive quotient declarations
`quot`, `quot.mk`, `quot.lift` and `quot.ind`.

By default `Lean Import` fails at the first error. With `Set Lean Error
Mode "Stop".` it succeeds instead, which allows inspecting the state from
just before the failing entry (see `Lean Error Mode` below).

# How do I run the tests?

`make test` builds the plugin and runs each test of `tests/_CoqProject`
(`make -k test` runs every one even after a failure). Two of the exports
the tests read, `dumps/init.ndjson.zip` and `dumps/stdlib.ndjson.zip`, are
Git LFS objects: in a clone made without Git LFS they are small pointer
files, and `tests/Makefile`, which extracts each archive next to it on the
first run, fails on them. Fetch them first:

~~~sh
git lfs install
git lfs pull --include 'dumps/init.ndjson.zip,dumps/stdlib.ndjson.zip'
make test
~~~

After it makes a test that its `ROCQCHK_TESTS` names, `tests/Makefile`
runs `rocqchk` (the cut's, on CI) on the test's `.vo`, its output in
`tests/<name>.rocqchk.log`; when rocqchk refuses the file, the make
prints `ROCQCHK FAIL: tests/<name>.vo: ` and the first line of that log
that is not blank, and fails. `Lean Import` stores the importer's state
in the `.vo` (see "Natural number literals"), and this step shows that
rocqchk reads it.

# How does it work?

The basic idea is to translate Lean `Prop` to Coq `SProp`, inductives
to inductives, etc.

We need to deal with a few issues in the translation:

## Differences in name handling

Lean has `.` separated namespaces, so we can have `foo.c` depend on
`bar.b` which depends on `foo.a`. This cannot be done with Coq
modules. Instead we replace dots by underscores, and add some indexing
to deal with collisions.

For instance,
~~~lean
inductive nat
| zero : nat
| succ (n : nat) : nat
~~~
becomes
~~~coq
Inductive nat := nat_zero | nat_succ (n : nat).
~~~
then if Lean declared a `nat_succ` it would get renamed to `nat_succ0`.

## Prop instantiations

Lean provides universe polymorphic values where universes may be
instantiated by `Prop`. For instance
~~~lean
inductive psum (α : Sort u) (β : Sort v)
| inl {} (val : α) : psum
| inr {} (val : β) : psum
~~~
provides discriminated sums of relevant as well as irrelevant types:
we can have `psum@{0 0} true true` as well as `psum@{1 1} nat bool` or
even `psum@{0 1} true nat`.

In Coq this is not possible. Instead we duplicate every value
according to which universes are instantiated to `Prop`. This
duplication is what the "possible instances" refers to in the end of
processing summary.

The version where no universe is `Prop` is considered the default and
gets the base name. The others have `_instX` appended to their name,
where `X` is the decimal representation of the number where bit `n` is
set if and only if universe `n` is instantiated by `Prop`. (this
naming scheme is subject to change)

By default, we produce the base instance, and the others are produced
as needed when encountered in other base instances. In other words,
when encountering the entry for `psum` we declare
~~~coq
Inductive psum (α:Type) (β:Type) := psum_inl (val:α) | psum_inr (val:β).
~~~
Then if we later encounter `def bla := ... psum@{0 u} ...` we will produce
~~~coq
Inductive psum_inst1 (α:Type) (β:Type) := psum_inl_inst1 (val:α) | psum_inr_inst1 (val:β).
~~~
and the same for `psum_inst2` and `psum_inst3`.

This lazyness has an exception: each instance of an inductive type
with large elimination has 2 instances of the recursor, depending on
whether we're eliminating to a `Prop` motive. These 2 instances are
always declared, so we don't wait until `psum_rec_inst1` is needed to
declare it.

Instances may be eagerly declared by using `Set Lean Upfront Instantiation`.

## Algebraic universes

Lean uses non cumulative universes, such that `Π (x:A), B` lives
exactly in the impredicative maximum of the domain and codomain
universes: `imax(uA,uB)`. We also get `max` in the level of inductive
types.

Thanks to the previous section, every universe name can be determined
to be either `SProp` or strictly greater than `Set`, so we can reduce
universe expressions to Coq algebraic universes. However this leaves
us with 2 issues:

- Coq expects universes in terms to be atomic, except in the codomain
  of the type of a global declaration. This is mostly required for the
  elaborator, so we could ignore it.

- Coq universe polymorphic values may only be instantiated by atomic
  universes (and, as we mentioned, ones which are not `SProp`).
  However Lean can (and must, due to lack of cumulativity) instantiate
  polymorphic universes with arbitrary expressions.

So we need to replace algebraic universes in universe instances by
some atomic name. In order to preserve conversions, we also need to
replace algebraic universes in terms (so for instance if we have `def
univ@{u} := Sort u`, the translation of `univ@{max(u,v)}` must be
convertible to `Sort (max (u,v))`).

The full process of translating a universe expression is then:

- first, produce a Coq algebraic universe:
  - `Prop` is translated to `SProp`
  - `a+1` is translated to the Coq successor of the translation of `a`
    (note that the successor of `SProp` is `Set + 1`, not `SProp + 1`
    which is invalid)
  - a Lean universe parameter is translated to `SProp` or a Coq named
    universe (depending on which instance we are currently producing).
    A universe name that is not one of the entry's universe parameters
    (its `levelParams` in the export) refuses the entry with `the
    universe <name> is not a universe parameter of this entry (its
    parameters: <parameters>)`, with `none` for an entry that has none
  - `max(a,b)` is translated to the max of the respective translations
  - `imax(a,b)` is translated to `SProp` if `b` is translated to
    `SProp`, otherwise to the max of the respective translations.

We also need to make sure that every universe parameter not
instantiated by `Prop` is considered strictly greater than `Set`. This
is because Lean recognizes that `imax(Prop+1,l)+1 <= max(Prop+1,l+1)`:
either `l=Prop`, in which case the problem reduces to `Prop+1 <=
Prop+1`, or `l=l'+1`, in which case it reduces to `l'+1 <= l'+2`.
However in our translation we reduced to `max(Set+1,l)+1 <=
max(Set+1,l+1)` which is only true when `Set < l`.

To ensure this we keep constraints `Set < l` for every universe
parameter `l`, and we also apply a simplification step to the
translated universes which removes any `Set+n` subexpression when it
is together with a `l+k` with `n <= k + 1`.

We then associate a unique surrogate name for each simplified
algebraic universe.

At the end, we will produce a top-level universe polymorphic value
with the original parameters appended with the surrogates. It will
have constraints such that `Set < l` for each original parameter `l`,
and each pair of parameter (surrogate or original) is related by any
constraint relating its corresponding algebraic universes. For
instance, if `AB` is the surrogate for `max(a,b)` and `ABC` is the
surrogate for `max(a,b,c)` we must have all of `a <= AB, b <= AB, a <=
ABC, b <= ABC, c <= ABC` and `AB <= ABC`.

Since we have added universe parameters, we must adapt instances in
terms accordingly: if a definition `foo@{u}` is translated to `foo@{u,
U1}` where `U1` is the surrogate for `max(Set+2,u)`, its use as
`foo@{max(a,b)}` must be translated to `foo@{AB AB2}` where `AB` is the
surrogate for `max(a,b)` and `AB2` is the surrogate for
`max(Set+2,a,b)`.

By default, surrogate names are based on their corresponding universe.
For instance the surrogate for `max(u,v)` is `Lean.max__u_v.0`. If a
strangely-crafted input uses this to cause collisions, you can `Unset
Lean Fancy Universes` to get guaranteed unique names `bla.XXX` where
`bla` is the current file and `XXX` some unique index.

Note that once the kernel has accepted a declaration the universe
names are used only for printing.

## Subsingletons

Even with Coq accepting UIP, the rules for which inductives enjoy
unrestricted eliminations are different between Coq and Lean.
Typically, the accessibility predicate `Acc` is unrestricted in Lean
but is not accepted in `SProp` by Coq.

This is because it leads to an undecidable theory (of course we now
know that UIP combined with impredicativity is enough for that).

The workaround is simple: we detect when Coq is stricter than Lean and
in that case disable universe checking while declaring the inductive.

Sadly this is not enough to make the translation work in Coq without
UIP, because such a Coq also lacks the special reduction of the
eliminator of equality.

Note that this translation breaks extraction: for instance the recursor
of the translated `acc` cannot be extracted. However a more careful
translation could take advantage of Coq's non recursively uniform
parameter feature to fix extraction.

We may note that Lean is sometimes stricter than Coq. Specifically, if
an inductive has a `Prop` and a non-`Prop` instantiation, it may
happen that Coq only squashes the `Prop` instantiation.

## Primitive quotients

Lean's quotient primitives are
~~~lean
constant quot {α : Sort u} (r : α → α → Prop) : Sort u

constant quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : quot r

constant quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → eq (f a) (f b)) → quot r → β

constant quot.ind {α : Sort u} {r : α → α → Prop} {β : quot r → Prop} :
  (∀ a : α, β (quot.mk r a)) → ∀ q : quot r, β q
~~~
with the appropriate reductions.

Coq can emulate this using "Private inductive types". This emulation
has been done for you in the Coq module named `Coq.Lean`: simply
`Require` it before running `Lean Import`.

Because the `lift` mentions equality, `Coq.Lean` also predeclares the
equality type (we can't use the one from Coq's standard library since
it's not polymorphic). Declaring the eliminators for equality is still
done by `Lean Import`.

## Predeclared constants and the path of an export

Besides equality and the quotient, `src/Lean.v` predeclares a few Lean
types and definitions, and `Lean Import` binds the export's entry of
each to the predeclared one instead of declaring it: `Eq`, `Nat`,
`Nat.le`, `Or`, `And`, `Fin`, `ULift` (with
`ULiftCumulativeRegistration`, see `src/ULiftCumulativeRegistration.v`)
and, on the legacy path only, `BitVec`, `UInt32`, `Char`, `UInt32.size`,
`Nat.isValidChar` and `Nat.pow`.

An NDJSON export takes the new path when its metadata line gives
`lean.version` 4.17.0 or later (a leading `v` and a suffix after `-`,
as in `4.17.0-rc1`, are ignored), and the legacy path for an earlier
version. An export in the old text format takes the legacy path. An
NDJSON export whose metadata has no `lean` object or no
`MAJOR.MINOR.PATCH` version takes the legacy path with a warning that
names the field and its value. The path is chosen before the first
entry, from the metadata only.

Each entry is saved with the path, and the Lean version, of the export
that gave it. An instance that is declared only when an entry first
asks for it (an instance at `Prop`, see "Prop instantiations" above, or
any instance under `Lean Lazy Instantiation`) may be asked for by an
entry of a later export: it is declared on the saved path and version,
after which the entry that asked goes on on its own export's path and
version. A compiled Rocq library keeps the saved paths and versions, so
a later import in another Rocq process that loads the library declares
such an instance the same way.

On the new path `BitVec`, `UInt32`, `Char`, `UInt32.size`,
`Nat.isValidChar` and `Nat.pow` are imported from their own entries, as
Lean defines them, and a string literal is translated as the term
Lean's kernel unfolds it to (its `string_lit_to_constructor`): the
string constructor applied to a list of `Char.ofNat <code point>`.
The constructor is `String.mk` for an export of Lean 4.17.0 to 4.25.x
and `String.ofList` from Lean 4.26.0 on, as the metadata's
`lean.version` says (for an instance declared later, the version saved
with its entry); an export that does not declare that constructor is
refused at its first literal (`missing String.mk` or `missing
String.ofList`). On either
path a literal must be well-formed UTF-8, as Lean's strings are. A
repeated `UInt32` or `Char` entry is skipped as a duplicate, like any
other entry. On the legacy path a second `UInt32` or `Char` entry may
switch between the pre-4.17 records `UInt32_legacy`/`Char_legacy` and
`UInt32`/`Char`.

On either path each entry bound to a predeclared constant is first
checked against it, after the translation the importer gives any entry:
an inductive type's parameter count, type, constructor count and
constructor types, and a definition's declared type (its value is not
read: the predeclared one is kept). Types are compared by conversion,
except the sort of an inductive type, which must be exactly the one the
predeclared type stands for: `src/Lean.v` declares in `Set` the types
Lean declares in `Type`, so a type predeclared in `Set` accepts only
`Type@{Set+1}`, the importer's translation of Lean's `Type` (not `Type
1` or above), and a type predeclared in `SProp` accepts only `SProp`,
the translation of Lean's `Prop`. An entry that differs is refused with
a message `The export's <name> does not agree with the predeclared
<constant>: ...` that gives the difference. The constructors of the
export are bound, by their export names, to the predeclared
constructors in order.

## Natural number literals

Lean's `Nat` is imported as the unary type `Nat` of `src/Lean.v`, on
either path. A literal below 5000 becomes `Nat_succ` applied to the
literal one below (shared between literals). A literal `i` of 5000 or
more becomes `Nat_succ` applied `r` times (1 to 8) to the binary form
of `i - r` (`Nat_double` and `Nat_succ` over its bits), with `r` chosen
so that `i - r` is 4 modulo 8. For each such `b`, large literals in
the block `b + 1` through `b + 8` use the same binary form of `b`.
If `j` and `j - 1` are both large literals in that block, the predecessor
of the literal `j` is, term for term, the literal `j - 1`, and
the kernel compares two such predecessors without unfolding
`Nat_double`; the predecessor of the literal `b + 1` is the binary form
of `b`, which is not the literal `b`. So a conversion that takes `k`
`Nat_succ` off the literal `j` and meets the literal `j - k` is cheap
when `j - k` is in the block of `j` (comparing `-(-x)` with `x` for
`x = -134217728`, 134217728 being `b + 4`, where the plain binary form
needs a stack as deep as the value). Crossing the block boundary can
still force a unary walk: for example, `Nat.pred` of the literal
134217733 reaches the binary form of 134217732, not the literal
134217732. Before this form a literal of 5000 or more was the binary
form of `i` itself; a tool that reads the translated terms must accept
up to 8 leading
`Nat_succ`.

Until it builds the term, the importer keeps a literal as the decimal
string of its value (written by Zarith, so `007` and `7` are the same
string), not as a Zarith number: `Lean Import` stores the importer's
state in the `.vo` (the entries it read and, for an export of the old
text format, every expression parsed so far), and `rocqchk` reads no
OCaml custom block, which a Zarith number of 2^62 or more is (it stops
with `Unhandled code 0018`). A `.vo` that an earlier importer wrote
holds Zarith numbers there; compile it again.

Lean's kernel computes `Nat` arithmetic on literals with GMP. Rocq's
kernel reduces Lean's own `Nat.add`, `Nat.sub`, `Nat.mul` and `Nat.pow`
on these unary terms one `Nat_succ` at a time, so a proof that Lean's
kernel checks by computing with large numbers (`decide` on `Int`
values near 2^33 or above, for example) does not end in Rocq in any
useful time, unless the transport pass below proves the values it needs
(literal arithmetic) for the proof arguments it casts.

## Transport of proof arguments across Nat literals

Lean `Prop` is `SProp` here, so a proof argument whose type differs
from the expected one only at closed `Nat` terms of equal value can be
cast without changing anything a computation sees. On the new path,
before the value of a definition or theorem is declared, `Lean Import`
does that where the kernel would otherwise compare the two terms one
`Nat_succ` at a time. Lean v4.34.0's `Char.ofNatAux`, for example,
passes a proof of `n < UInt32.size` where `BitVec.ofNatLT 32` expects
`n < 2 ^ 32`; Lean's kernel computes `2 ^ 32` with GMP, Rocq's would
unfold Lean's `Nat.pow`, `Nat.mul` and `Nat.add` 2^32 times.

What it changes:

- An argument of an application, or the value of a theorem itself,
  whose type is an `SProp` type that differs from the expected type
  only at closed `Nat` terms of equal value of 4096 or more, becomes
  `sprop_transport P x y e p` (`src/Lean.v`): `p` is Lean's proof, `P`
  the expected type with the place abstracted, and `e : x = y` a
  generated lemma. A closed `Nat` term is a literal, a constant whose
  value is a closed `Nat` term (`UInt32.size`), or the export's
  `Nat.add`, `Nat.mul`, `Nat.pow`, `HAdd.hAdd`, `HMul.hMul`,
  `HPow.hPow` (at Lean's `Nat` instances) or `OfNat.ofNat Nat` applied
  to closed `Nat` terms. Two terms that unfold to the same literal
  (`UInt32.size` and `4294967296`) are left to the kernel, which
  converts them without arithmetic.
- The lemma `<entry>__nat_eq_<k>` (`Char_ofNatAux__nat_eq_1 :
  UInt32.size = 2 ^ 32`, say) is declared before the entry, as a
  constant the kernel checks like any other. For two `Nat` terms its
  proof goes through Rocq's binary `N` (`toN` and the lemmas after it
  in `src/Lean.v`): the export's own `Nat.add`, `Nat.mul` and
  `Nat.pow`, whose defining equations the kernel checks by
  `Logic.eq_refl` on open terms, a step per bit of each literal, and
  each binary computation checked on literals. In the Fin case (below)
  the proof goes through the unary literal `l` of the value:
  `sprop_transport (fun n => x = n) l y (eq_refl l) (eq_refl x)`, so
  that the kernel converts each of the two values with `l` on its own.
  A later argument with the same two terms reuses the lemma, within the
  Rocq file that runs the imports: the cache is not kept in a compiled
  file, so a file that Requires one with an earlier import generates
  the lemmas it needs again, under new names. The values the importer
  computes only find the places: a wrong one gives a lemma the kernel
  refuses, which is logged and not used: `line N: NAME: the generated
  lemma ID : X = Y is refused by the kernel` when `X` and `Y` have at
  most 256 nodes together (then followed by the kernel's error when the
  proof has at most 256 nodes too, which a Fin lemma of a value above
  about 60 exceeds: its proof holds the unary literal twice), else
  `line N: NAME: the generated lemma ID is refused by the kernel (its
  statement has more than 256 nodes and is not printed)`.
- The import's output has one line per entry whose value changes,
  printed once the kernel has accepted that value:
  `line N: NAME: <k> argument(s) transported (<lemmas>)`.
- The Fin case. Two closed terms whose head constants differ, which
  both reduce (at most 64 steps each side in all, counting every step
  of its head reductions: of the term, of the subject of a projection,
  and of the field of each record; a step is the unfolding of a
  constant, the substitution of one bound argument, so that a constant
  applied to three arguments it binds takes four steps, a zeta step, or
  a projection, which is counted before its subject is reduced) through
  zero to four records of one field (a fifth gives no lemma), the same
  records on both sides with the same parameters, to a `Fin` of the
  same bound, and whose two `Fin` values are closed `Nat` terms of the
  same value. Two parameters, or the two bounds, are the same when they
  are the same term, or closed `Nat` terms of the same value of at most
  1024 whose every operand, a divisor included, is at most 1024 (so
  `BitVec (2 + 6)` against `BitVec 8`, of bounds `2 ^ (2 + 6)` and
  `2 ^ 8`; the kernel converts them in the cast):
  Lean v4.34.0's `Char.utf8Size_eq_one_iff` passes a proof of
  `v ≤ UInt32.ofNatLT 127 _` where `v ≤ (127 : UInt32)` is expected,
  and `(127 : UInt32)` stores `127 % 2 ^ 32`. The lemma is
  `<entry>__nat_eq_<k> : 127 = 127 % 2 ^ 32`, through the unary literal
  `127`: the kernel computes each value on the unary `Nat`, in time
  that grows with each number it computes but a divisor. A `Fin` value
  is read through the forms of a closed `Nat` term above, `Nat.mod`
  and `HMod.hMod` at Lean's `Nat` instance, and `Nat.land`, `Nat.lor`,
  `Nat.xor`, `Nat.shiftLeft` (by at most 16, or of 0), `Nat.shiftRight`,
  `Nat.sub` (truncated at 0) and `Nat.div` (0 for a divisor 0), each
  function or its class function at Lean's `Nat` instance (`&&&`,
  `|||`, `^^^`, `<<<`, `>>>`, `-`, `/`), every operand of each read the
  same way (so `(255 &&& 127) + 0` has a value); a term it reads none of
  is reduced at its head (as above, at most 64 steps of its own) until
  the term is one of those forms: `BitVec.toNat 8 (UInt8.toBitVec 224)`
  reads `224 % 2 ^ 8`. A head reduction that stops anywhere else (a `match`,
  a fixpoint, an axiom) gives no value. The value and every operand of
  it, but the divisor of a `%`, are below 65536; otherwise there is no
  lemma. Two such terms whose `Fin` values differ give no lemma either:
  they are left to the kernel as without the pass, and the other places
  of the same argument are still cast.
- Literal arithmetic, when `src/Lean.v` registers its lemmas (a missing
  one turns off this case alone). Two closed terms of a data type whose
  heads differ (two constants, two constructors, or one of each), of a
  type whose sort the pass reads (`Set` or `Type@{l}`, so not a function
  type or a sort): the pass evaluates each side in rounds. A round
  reduces the term to a normal form: it unfolds constants, beta, zeta
  and casts, takes the branch of a `match`, unfolds a fixpoint once its
  recursive argument is a constructor, and takes the field of a
  constructor's projection. It holds each Lean `Nat.add`, `Nat.mul`,
  `Nat.pow`, `Nat.sub`, `Nat.div` and `Nat.mod` with an operand or a
  value of 65536 or more, or a held operand, and each closed `decide p`
  whose `p` holds a `Nat` term of 65536 or more; below that it computes
  the operation, as the kernel does. The next round puts each held
  operation's value in its place, by a lemma of its own: `toN_sub` for
  `-`, Lean's `Nat.div_eq_of_lt_le` with `Nat_le_of_toN` and `toN_of_eq`
  for `/`, the certificates above for `+`, `*` and `^`, and Lean's
  `decide_eq_true` for a `decide`, from a proof of `p`: `a ∣ b` by its
  witness, `≤` and `=` at `Nat` by the certificates, `=` at another data
  type by the same evaluation, and Lean's `Int.NonNeg`. When the two
  normal forms are the same value, the lemma `<entry>__nat_eq_<k> : a =
  d` at their type is proved through `sprop_transport_any` and the
  argument cast along it (omega's `tidyConstraint` on `Int` literals near
  2^32, `decide (256 ∣ 4294967296)` at Lean's `Bool`). The pair gets no
  lemma when a `match`, fixpoint or projection meets anything but a
  constructor or a held operation (a variable, an axiom, an opaque
  constant, a stuck `match`), when one still waits on a held operation
  after the last of 16 rounds of replacement, when an operation has an
  operand of no value or a value of more than 1024 bits, at a held `%`
  and at a closed `Nat.mod` with a value anywhere in a normal form, however
  small (no lemma proves its value), at `Nat.beq` and `Nat.ble` on anything
  but two literals below 65536 (which it computes), when the two values
  differ (the other places of the argument are still cast), and when the
  pair would need more than 200 000 steps, every nested evaluation and the
  tree size of the proof's evaluated terms counted with it: the pass goes on
  with the other places, evaluates no pair inside the declined one, and the
  declined pair's steps stay charged to the argument's part. Two operations
  of one function and values share a representative only when their form and
  operands are the same term or unfold to the same literal, so the kernel
  never converts `2^32` with `4294967296`; a small operation (below 65536)
  in a parameter, proof or type is not held.

What it does not change: an entry's declared type (its statement),
the non-`SProp` arguments (the data, which stay Lean's terms, so that
Lean's `rfl` lemmas about them still check), any kernel check, and
the axioms: no imported entry becomes an axiom, the `toN` lemmas of
`src/Lean.v` are closed under the global context, `Nat_eq_of_toN`
and `sprop_transport` (and literal arithmetic's `toN_of_eq` and
`sprop_transport_any`) rely only on the definitional UIP of `eq` (as
every entry that names `eq` does), and a generated lemma relies on no
axiom of its own (`Print Assumptions`): what it relies on is what the
export's lemmas it names rely on, so a lemma that certifies a held
division (literal arithmetic, through Lean's `Nat.div_eq_of_lt_le`)
relies on that theorem's own `propext` (with the sort eliminations of
`Iff`), as `Print Assumptions Nat_div_eq_of_lt_le` prints. An entry where the pass casts nothing is
declared with Lean's own value; a cheap scan for the export's `Nat`
operations and large literals in the entry and the types of the
constants it names decides which entries are looked at, and it also
passes on an entry that holds itself `OfNat.ofNat T` or a constant
whose declared type ends in `T`, for `T` a record of one relevant
field of an inductive type (`UInt8`, `BitVec w`). Two closed
`Nat` terms of different values give no lemma, and the argument that
holds them no cast: the kernel refuses the entry as before. If the
kernel refuses a transported value, the import logs `line N: NAME:
the transported value is refused (...); Lean's
value goes to the kernel instead` (the kernel's error in the
parentheses only when the transported value has at most 256 nodes;
else `the transported value is refused by the kernel (it has more than
256 nodes: the kernel's error is not printed); Lean's value goes to
the kernel instead`) and submits Lean's value; if the kernel refuses
that too, the entry fails with Lean's error, as without the pass. If
the entry is accepted, the lemmas the pass declared stay declared, even
if another place gets no lemma, the pass stops, or Lean's original
value is used; if the entry is refused, they go with it. A lemma the
kernel refuses, a place's or one generated while the places are found
(a held operation's, a `decide`'s), leaves its whole argument to Lean's
term; no refusal is remembered, so a later argument generates it again.

The pass is optional work, and all of it is charged before it runs
(`tick` and `pay` of its charged term layer, `src/leanChargedTerm.ml`):
each term it visits, copies or builds, each substitution, comparison
and lookup, natural number evaluation (each value, Fin value and
parameter value it does not find in its memo, each step of the Fin
case's head reduction, each unary literal it builds) and certificate
construction, against the `Lean Transport Step Budget` of each part of
an entry (the entry's own scans and walks are one part, and each
argument it looks at is
another), 1 000 000 steps by default, and all the parts of one entry
together against ten times that budget (at most OCaml's `max_int`,
2^62 - 1 on 64-bit systems). One charge comes after its work: the
importer's list of the export's constants of a Lean name, whose length
is known only once the list is returned, is charged by that length
then; the pass asks for 47 fixed names, once per entry, and 56 when
the lemmas of literal arithmetic are registered. A reused
certificate counts again at its full size because the kernel checks
the proof tree. A substitution pays, before it is made, for each node
it visits and, at each place it substitutes, for the size of the
replacement counted as a tree (with its lift under binders), so one
that would build a term of more than `max_int` nodes stops the pass
before it is made; a term instantiated at a universe instance pays its
size with the universe data of each node. The pass keeps, per entry,
the values of constants in tables, which never evict, and the results
it computes for other terms (values, Fin values, parameter values,
certificates, sizes, free variables, beta normal forms) in memos of 512
slots each, one slot per term found by a bounded hash (at most 10 nodes
that carry a value among at most 100 visited): a lookup or a write
costs one step and compares at most one term, by physical identity, and
a result replaced by another term of the same slot is computed again at
its full charge. The memos' hash and the tables' read no module path and
no universe level (a constant counts by the label of its name, a sort
by its kind), so the same export costs the same steps in whatever file
imports it (`tests/fin_transport_budget_name.v`). The pass also caps its
depth at 10 000, counted from the entry's value or type down through
the terms its scans and walks visit
and the `Nat` terms the finder computes, together, a result found in a
memo included. When a limit is reached, the importer logs `line N:
NAME: the transport pass stops: it needs more than N steps or a nesting
deeper than 10000; ...` (for the total, `... more than T steps in
total; ...`) and submits the original value for the usual kernel check.
An error in the pass takes the same path and logs `the transport pass
fails (E); the value is left as Lean's`, `E` the name of the error's
exception only.

The pass reads the types it needs itself, without Rocq's retyping or
reduction: a variable's declared type, a global's declared type at its
universe instance, and the types of applications, lambdas, lets, casts
and projections of records built from those. Where a type must be a
product or a sort it reduces the head as the Fin case does (unfolding a
transparent constant, beta, zeta, a cast, a local definition, the
projection of a constructor; at most 64 steps, every step charged), and
no further: a type behind a `match` or a fixpoint, or any other term,
gives no type, and an argument whose type the pass cannot read gets no
cast; the kernel then checks it as without the pass. It reads no type
for an application of `Nat_succ` or `Nat_double` to one argument, whose
declarations it reads once per entry (one relevant `Nat` argument). A
literal holds no other node, so the walk of the entry's value takes it
whole: a step for the node and one for the walk's own memo of literals
(its own, so that the walk changes no charge of literal arithmetic or
of an argument), and one more to keep its answer at a miss; at a miss
(every unary literal of 10 or more has the same slot, since the hash
reads only its first ten `Nat_succ`), a step for each of the at most 16
literals of 16 levels or more the walk met last that it compares, and,
only if it is none of them, a step per `Nat_succ` and `Nat_double` of
the literal. A literal found among them moves first, and a literal of
16 levels or more walked at a miss is kept first: a step for it and one
for each literal moved one place. A run of `Nat_succ` that is no
literal is asked once whether it is a literal (a step per level to the
point where it is none), then walked in one loop to its base (a step per
level), the base walked once.

Limits: only on the new path; only proof (`SProp`) positions. A
mismatch in a data position, such as `UInt32.toFin : Fin UInt32.size
:= x.toBitVec.toFin` (`Init/Data/UInt/BasicAux.lean:141`), is left to
the kernel. The places are found in the types the arguments and the
function have as written: a `Nat` place is never found by unfolding a
constant, and a Fin place only by the head reduction of the Fin case
(at most 64 steps of each side in all). For a `Nat` place the
operations are the six above; for a `Fin` value also `Nat.mod` and the
seven of the Fin case; `Nat.sub` and `Nat.div` are covered only in the
values literal arithmetic evaluates, not at a `Nat` place; `Nat.ble` and
`Nat.beq` only on two literals below 65536; a `%` of 65536 or more not
at all.
Values are computed up to 1024 bits. `USize.size` (`2 ^
System.Platform.numBits`) has no closed value.

## Additional note on recursors

Coq autogenerates recursors for inductives types called (for an
inductive `foo`) `foo_sind`, `foo_ind`, `foo_rec` and `foo_rect`
(respectively for `SProp`, `Prop`, `Set` and `Type` motives).
These names are automatically detected by tactics like `induction`.

When the inductive is universe polymorphic (which is always the case
for our translations) the recursors are also universe polymorphic, and
notably the motive of the `_rect` version is a universe parameter.

However we cannot directly reuse the generated `_sind` and `_rect`
recursors as the 2 instantiations of the translated Lean recursor:

- In Lean the motive universe is the first parameter, in Coq it is the
  last. This is could be handled during the translation though.
- Coq generates non dependent eliminators for `SProp` inductives, but
  if the original Lean inductive has a non-`Prop` instantiation Lean
  expects a dependent eliminator.
- Each recursive argument of each constructor corresponds to an
  inductive hypothesis in the function for the branch of that
  constructor (the first `P n` in `nat_rect : forall P : nat -> Type,
  P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n`). In
  Coq each inductive hypothesis comes immediately after the recursive
  argument, but in Lean the inductive hypotheses come after all the
  constructor argument.

  This produces different types when a recursive argument is not the
  last constructor argument, for instance with
  ~~~coq
  Inductive bin_tree := Leaf | Node (a b : bin_tree).
  ~~~
  Coq generates
  ~~~
  bin_tree_rect
     : forall P : bin_tree -> Type,
       P Leaf ->
       (forall a : bin_tree, P a -> forall b : bin_tree, P b -> P (Node a b)) ->
       forall b : bin_tree, P b
   ~~~
   but Lean expects
   ~~~
   bin_tree_rect
     : forall P : bin_tree -> Type,
       P Leaf ->
       (forall a b : bin_tree, P a -> P b -> P (Node a b)) ->
       forall b : bin_tree, P b
   ~~~

To avoid these issues, we explicitly ask Coq for a term implementing
the recursor with the expected dependency, then post-process it to fix
universe and argument order. Since the result may not be compatible
with `induction`'s expectation, we use our own suffixes `_indl` and
`_recl` (`l` for `Lean`).

Since we use `_indl` for the `Prop`-motive recursor, any `_inst`
suffix corresponds to the instantiation of the inductive we eliminate.
For instance `psum_inst3_indl` is instance 5 (all universes `Prop`) of
`psum.rec`, its principal argument is of type `psum_inst3`.

# Experimental results

All times are on my laptop, which may have caused variance through
thermal throttling or whatever.

The export for just `core.lean` passes without issue in about 2s.

The whole stdlib cannot be checked as some conversion problems are
pathological. `two_pos` seems a typical example (`0 < 2` in an ordered
field). It's interesting to note that on this specific example,
changing the default conversion procedure to use Coq's VM makes it
succeeds in about 1 second (tested by importing with `Unset Conversion
Checking` (see next section), then `Require Import` the resulting
`.vo` and do `Definition foo := Eval cbv [two_pos] in two_pos.`).
Sadly using the VM makes other declarations take too long, and anyway
it hasn't been updated for proof irrelevance and for UIP's special
reduction.

As a superset of the stdlib, mathlib also cannot be fully checked.
Worse, even with `Unset Conversion Checking` it tries to use more RAM
and takes longer than I was willing to try.

Some stats:

- stdlib:
  lean --export in 46s, about 450MB RAM
  leanchecker in 8s, 80MB RAM

  Lean Import with Unset Conversion Checking: 43s, 723MB RAM
  resulting vo size 53MB

  Lean Import with 10s line timeout: 451s, 720MB RAM
  resulting vo size 50MB
  89 skipped entries out of 10244 (32 timeout, rest due to missing value from previous errors)

- mathlib:
  lean --export: didn't measure, took long enough and enough RAM that I don't want to retry
  (at least 1h / 10GB RAM I guess)
  leanchecker: 6min, 1GB RAM

  Lean Import with Just Parsing: 347s, 745MB RAM

  Lean Import with Unset Conversion Checking: killed at 4GB RAM on filter_mem_inf_sets_of_right

  Lean Import with Unset Conversion Checking and 10s timeout: 1h13min, 10GB RAM
  resulting vo size 1.4GB
  11867 skipped entries out of 66400 (first one is real.linear_order._proof_5)

# Options

## Lean Fancy Universes

See explanation of surrogate universe names.

## Lean Upfront Instantiation

See explanation of universe polymorphism and `Prop`.

## Lean Skip Missing Quotient

On by default, this means that encountering the primitive quotient
entry when the primitive quotient has not been predeclared is not an
error (i.e. when `Coq.Lean` is not loaded).

This means you will instead get a `quot was not instantiated` error
when a declaration refers to it.

## Lean Just Parsing

Off by default, if on `Lean Import` will not actually translate
anything. Useful to get the summary of how many entries are
encountered quickly.

## Lean Print Squash Info

Off by default, this may be useful for debugging if `Lean Import`
misdetects whether Lean would allow unrestricted elimination for some
inductive type.

## Lean Error Mode

A string option: `"Fail"` (the default), `"Stop"` or `"Skip"`. It decides
what `Lean Import` does with a line it refuses: a line whose entry it cannot
declare, or a line it cannot parse. In an NDJSON export, a line before
the first line to import (`Lean Import "file" FROM` starts at line FROM)
is parsed for its metadata, names, levels and expressions only (a declaration
there is not read); when it cannot be parsed, it is refused like any
other line. The old text format reads nothing before line FROM. The
refusal reads `Error at line N (for NAME)`, followed by the
line and the error. NAME is the entry's name. For a line that cannot be
parsed, it is the name the NDJSON parser read before the error, else
`line-N`.

The text parser requires the next id in the name, level or expression
sequence for every recognized numbered line. An unreadable number, an
unknown tag or an out-of-sequence number does not advance a sequence.
After the metadata, the NDJSON parser uses the single next integer id
field (`in`, `il` or `ie`) to choose the sequence. This applies even when
the payload tag belongs to a different kind of record. In either format,
if the parser refuses the payload of a recognized record with the next
id, it keeps that id in the sequence but does not make its value available.

- `Fail`: the import stops there and `Lean Import` fails with the refusal.
- `Stop`: the import stops there and `Lean Import` succeeds, keeping what it
  declared before the refused line.
- `Skip`: the refusal is printed after `Skipping: `, what the refused entry
  had declared is undone, and the import goes on with the next line. An
  entry that uses a refused entry is refused in turn. In either format,
  the parser refuses a line that uses a refused name, level or expression
  id and names that id in the error. The final summary counts the refused
  lines (`Skipped N`).

`Skip` is useful to tell how much the current system can handle.

Note that in `Skip` mode, an interrupt or an outer `Timeout` that arrives
while an entry is being declared refuses that entry like any other error,
and the import goes on. If you start loading mathlib this way and decide to
stop, you will need to kill the Coq process.

## Lean Entry Timeout

An integer option, unset by default. Use `Set Lean Entry Timeout 10.` to
bound the time spent declaring each entry (translating and checking it) to
10 seconds. An entry still being declared after that is refused with
`Timed out after 10 s (Lean Entry Timeout); major heap at the entry's start:
N MiB` (N is the size of the importer's major heap when the entry started),
and `Lean Error Mode` handles it like any other refused entry. The heap is
then compacted (see `Lean Entry Memory Limit`). With `Skip`, this allows
processing all the entries which do not depend on something that takes more
than 10s.

The value must be a positive number of seconds. `Unset Lean Entry Timeout.`
removes the limit. The limit does not bound parsing the entry's line (see
`Lean Line Timeout`). An enclosing `Timeout` shorter than the limit fires
first: in `Skip` mode, when it fires while an entry is being declared, that
entry is refused like any other error and the import runs to its end; Rocq
then prints `Timeout!` when the command returns (see the note under `Lean
Error Mode`).

An importer without this option only warns that the option is unknown and
imports with no limit. A file that sets it should therefore first run `Set
Warnings "+unknown-option".`, so that such an importer fails at the `Set`:

~~~coq
Set Warnings "+unknown-option".
Set Lean Entry Timeout 10.
Set Lean Error Mode "Skip".
Lean Import "/path/to/export.ndjson".
~~~

## Lean Entry Memory Limit

An integer option, unset by default. Use `Set Lean Entry Memory Limit 40.` to
bound how much the importer's major heap may grow while each entry is
declared (translated and checked): by 40 GiB above its size when the entry
started. The limit bounds the growth during the entry, not the size of the
heap, so the heap the import holds before the entry does not count. An entry
during which the heap grows by more is stopped and refused with
`Memory limit of 40 GiB reached (Lean Entry Memory Limit); major heap at the
entry's start: N MiB`, and `Lean Error Mode` handles it like any other
refused entry.

The importer measures the net growth of the major heap, which the whole
process shares, at the end of each major collection of the OCaml heap. It
then stops the entry with Rocq's interrupt exception, `Sys.Break`, which it
raises from an allocation callback of OCaml's memory profiler (`Gc.Memprof`)
at the next allocation the profiler samples in the thread that declares the
entry. So an entry can pass the limit by what the heap grows until the next
collection ends and then until that sample; this is no fixed bound, and
collections come further apart as the heap grows. In the measured case,
Rocq's reduction did not poll the interrupt flag, so setting the flag alone
did not stop the entry. The importer also refuses an entry if it records
excess growth but the entry ends before the next sampled allocation.

The importer runs its profiler only while declaring an entry under the
limit. It never takes over an active profiler. If it cannot start its own
profiler, it refuses the entry before declaring it, with `Lean Entry
Memory Limit cannot watch this entry, which is not declared: ...`.

After an entry is stopped by this limit or by `Lean Entry Timeout`, and what
it had declared is undone, the importer compacts the heap (`Gc.compact`)
before the next entry, so that the space of the stopped entry is given back
and two stopped entries do not add up. On a large heap the compaction takes
seconds or more.

The value must be a positive number of GiB. `Unset Lean Entry Memory
Limit.` removes the limit. A file that sets the option should first run
`Set Warnings "+unknown-option".`.

When both limits are set, the importer compares the entry timer's deadline
with the first heap measurement over the limit. If the heap guard interrupts
the entry, the importer reports a time limit only if it can establish that
the entry's own timer was active and its deadline had passed at that
measurement. An observed enclosing `Timeout` or independent interrupt
keeps its existing `Lean Error Mode` behavior. If asynchronous exceptions
overlap while an entry stops, the runtime may expose only the exception
that survives. The importer cannot always tell whether another interrupt
also occurred.

## Lean Transport Step Budget

A positive integer option, unset by default (1 000 000 steps). `Set
Lean Transport Step Budget N.` gives each part of an entry N steps of
the transport pass and all the parts of one entry together 10 N, or
OCaml's `max_int` (2^62 - 1 on 64-bit systems) when 10 N is larger (see
"Transport of proof arguments across Nat literals"); 0 and negative
values are refused, and `Unset` restores the default. A step pays for
one unit of the pass's work before it is done; a size the pass would
have to pay that is larger than `max_int` stops it as a part over its
budget does. Over a limit, the pass stops and the entry's original
value goes to the kernel. The budget bounds the optional pass only:
the kernel's checks of the generated lemmas and of the entry's value
are not charged, and they run under `Lean Entry Timeout` and
`Lean Entry Memory Limit` as for any entry. Inside one pair of literal
arithmetic the pass also counts the pair's steps, every nested
evaluation with them and the tree size of the evaluated terms its proof
holds, against a cap of 200 000, which declines that pair: no pair inside
it is evaluated again, its steps stay charged to the argument's part (so
that enough declined pairs side by side stop the pass as a part over its
budget does), and the pass goes on with the other places; there is no
other option.

## Corpus import settings

The final corpus import uses `Set Lean Entry Timeout 2400.` (2400 seconds)
and `Set Lean Entry Memory Limit 40.` (40 GiB of major heap growth per
entry). `ci/build-9.2-cut.sh` sets the soft stack limit to 131072 KiB
(128 MiB) for tests, `--import` and `--check` via `CUT_STACK_KIB`.
`--revert-fix` checks that the head passes and that reverting one fix makes
the test fail at its expected entry. Both sides use the head's tests and
dumps, with a separate plugin build for each side.

For a source fix, the parent side builds the source of the parent of the
first fix commit. Both sides use the head's stack unless the row in
`tests/lean434_features.txt` sets `stack`, the seventh tab-separated
column. That column is `-` or a positive whole number of KiB and applies
only to a fixed row's control, not to the suite or `--handoff`.
For a stack fix, both sides build the head's source; the parent side
uses the stack setting of the first fix commit's parent, or the default
soft limit if it has no setting. A control cannot revert both kinds of
change. Its `R5 CONTROL` line records the source commit and the stack
read back for each side.

R5 is the name of this per-fix control: a fix is shown by its test, which
passes at the head and fails when the fix is reverted. "R5 negative" is
that failure on the parent side, and `R5 NEGATIVE MET` is the verdict
line when it fails as its row says: at the row's own entry (`own_entry`,
the fourth column) or, when that is `-`, at its base entry (`base_entry`,
the third column, the first error at the base); an entry `option:NAME`
is a failure at the test's `Set NAME` line, and `check:rocqchk` a
failure of the rocqchk step of `tests/Makefile` on the test's `.vo` (its
line `ROCQCHK FAIL: tests/<name>.vo: ...`; the test must be in
`ROCQCHK_TESTS`). A test whose failure there is
not its first `Error at line N (for X)` says what the failure is
in comment lines that start `(* r5 `: `r5 error: TEXT` (the Rocq error
of the next command holds TEXT and names the entry), `r5 log: "LOG"
TEXT` and `r5 log lacks: "LOG" TEXT` (the log of `Redirect "LOG"` has,
or has not, the line TEXT), and `r5 assertion: "LOG" TEXT` (the test's
`.expect` fails with `unexpected 'TEXT'` on that log). Such a test has
exactly one `r5 error` or `r5 assertion` line; `r5_lines` in
`ci/build-9.2-cut.sh` states each rule in full.

Lean 4.34.0's entry `_private.Init.Data.String.Decode0.Char.toNat_le._proof_1_1`
(as printed by the importer) fails with `Stack overflow.` at 8, 16, 32
and 64 MiB, and imports at 128 MiB, the gVisor stack ceiling.
Run a corpus reading on a machine with a hard stack limit of at least
131072 KiB; the script refuses to run with a lower limit.

## Lean Line Timeout

An integer option, off by default. Use `Set Lean Line Timeout 10.` to
cause a failure whenever parsing a line takes more than 10s. This failure
ends the import whatever `Lean Error Mode`. It does not bound declaring the
line's entry: `Lean Entry Timeout` does.
