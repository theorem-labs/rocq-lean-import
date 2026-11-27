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
     literal (its base is a variable of the entry). -/
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

end RLI434Wk
