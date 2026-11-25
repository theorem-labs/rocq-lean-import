# Derived text fixtures

| File | Source and edits | SHA-256 |
| --- | --- | --- |
| `parse_text_numbering` | `uint32_dispatch` lines 1–9. Append three out-of-sequence expression records, an unreadable number, and an unknown tag (lines 10–14). Append the refused names and levels, their dependents and their valid successors (lines 15–20). Lines 21–22 declare the axiom `RLITextAfterGaps` with expression 3. | `df1e0020b7afee1c302933a64d9762a7793e8f6027fe948b5fc84b47dedb7a56` |
| `parse_text_recovery` | `uint32_dispatch` lines 1–9. Append a refused expression 3, its successor `4 #EC 2`, and the definitions `RLITextRefused` and `RLITextAfter` using expressions 3 and 4 respectively (lines 10–15). | `cb9c5175e0da82ca0015283dadfc46b32f1f14098eab0be405d338e70c80ed32` |
