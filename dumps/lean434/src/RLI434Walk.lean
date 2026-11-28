import Init

/- BET-1525: fixtures of the transport pass's walk of an entry's value (tests/transport_walk.v, README, "Transport
   of proof arguments across Nat literals"). The importer writes a Nat literal below 5000 as a chain of `Nat_succ`
   (one shared term per value), so a term that holds `1024` and `4096` many times is a small graph and a large
   tree. Each theorem proves `2 ^ 40 = 2 ^ 40` from `h : 2 ^ 39 + 2 ^ 39 = 2 ^ 40` as `(fun _ => h) l`: the
   Nat pair of `h` is cast along a generated lemma, which the kernel checks through Rocq's binary `N`, while
   without the cast the kernel converts the two sides on the unary Nat, far longer than a short entry limit.
   The list `l` is in the value only (the redex's argument), where the walk reads it, and in no type that the
   cast of the argument reads.
   - `walk_lits`: `l` holds `1024` and `4096` in turn, 400 times each, each written `OfNat.ofNat Nat n
     (instOfNatNat n)`, so twice per element: as a tree, the walk of the entry's value meets
     4,096,000 unary levels.
   - `walk_limit`: the same with 160 times each, for the rows at the entry's largest part.
   - `walk_open`: `l` holds `x` under 600 applications of `Nat.succ`, a run of `Nat_succ` that is no
     literal (its base is a variable of the entry).
   - `walk_rebuild`: the cast is inside a run of `Nat_succ` that is no literal: `kf 0 h` (whose second argument
     is expected at `2 ^ 40 = 2 ^ 40`) under 20 applications of `Nat.succ`, the argument of a redex whose value
     is `True.intro`, so that the cast of `h` changes the run's base and the walk rebuilds the run.
   - `walk_evict`: `l` holds the 17 literals `1000` to `1016` in turn, then `1001` to `1016` twice: more than
     the 16 literals the walk keeps, so that the first pass drops `1000`, the least recently met. -/
namespace RLI434Wk

theorem walk_lits (h : 549755813888 + 549755813888 = 1099511627776) : 1099511627776 = 1099511627776 :=
  (fun (_ : List Nat) => h) [
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096]

theorem walk_limit (h : 549755813888 + 549755813888 = 1099511627776) : 1099511627776 = 1099511627776 :=
  (fun (_ : List Nat) => h) [
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096,
    1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096, 1024, 4096]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem walk_open (x : Nat) (h : 549755813888 + 549755813888 = 1099511627776) : 1099511627776 = 1099511627776 :=
  (fun (_ : List Nat) => h) [
    x.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ]

def kf (n : Nat) (_ : 1099511627776 = 1099511627776) : Nat := n

theorem walk_rebuild (h : 549755813888 + 549755813888 = 1099511627776) : True :=
  (fun (_ : Nat) => True.intro)
    (kf 0 h).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ

-- written with `::`, not `[...]`: Lean elaborates a list literal of this length with `let`s over its chunks, which
-- the walk meets out of the list's order
theorem walk_evict (h : 549755813888 + 549755813888 = 1099511627776) : 1099511627776 = 1099511627776 :=
  (fun (_ : List Nat) => h) (
    1000 :: 1001 :: 1002 :: 1003 :: 1004 :: 1005 :: 1006 :: 1007 :: 1008 :: 1009 :: 1010 :: 1011 :: 1012 ::
    1013 :: 1014 :: 1015 :: 1016 ::
    1001 :: 1002 :: 1003 :: 1004 :: 1005 :: 1006 :: 1007 :: 1008 :: 1009 :: 1010 :: 1011 :: 1012 :: 1013 ::
    1014 :: 1015 :: 1016 ::
    1001 :: 1002 :: 1003 :: 1004 :: 1005 :: 1006 :: 1007 :: 1008 :: 1009 :: 1010 :: 1011 :: 1012 :: 1013 ::
    1014 :: 1015 :: 1016 :: [])

end RLI434Wk
