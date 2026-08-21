# npdiff

A CHICKEN Scheme library that computes the longest common subsequence of
two sequences and generates a script (in several standard diff
formats) to transform one sequence into the other.

## Overview

`npdiff` implements a sequence-comparison algorithm with a worst-case
running time of `O(N*P)`, where `P` is the number of deletions
required by the shortest edit script between the two sequences. The
algorithm is described in:

> Sun Wu, Udi Manber, Eugene Myers, and Webb Miller. *An O(NP)
> sequence comparison algorithm*. Information Processing Letters,
> volume 35, pages 317-323, September 1990.

The library defines a datatype describing the three basic operations
of an edit script (insert, remove, change) and a procedure that
implements the comparison algorithm for sequences of an arbitrary
type, given an equality predicate and accessors provided by the
`yasos-collections` interface. It can compare lists, vectors, or any
other collection type that implements the `collection` API, including
mixed comparisons between different collection types.

Output can be rendered as `ed`, `normal` (POSIX `diff`), RCS, or
context (`diff -c`) format, or as a list of s-expressions suitable for
consumption by other tools (e.g. the `patch` egg).

## Requirements

- [CHICKEN Scheme](https://www.call-cc.org/) 6
- Eggs: `srfi-1`, `srfi-4`, `datatype`, `yasos` (which provides
  `yasos-collections`), `iset`

## Installation

```bash
chicken-install npdiff
```

## Usage

```scheme
(import npdiff)

(define a '("a" "b" "c"))
(define b '("a" "x" "c"))

;; compare two sequences, with 3 lines of context
(define hunks (npdiff a b 3))

;; render in the classic "normal" diff format
(format-hunks/normal (current-output-port) hunks)
;; 2c2
;; < b
;; ---
;; > x

;; render as unified/context diff
(format-hunks/context (current-output-port) hunks "a.txt" "" "b.txt" "")

;; render as s-expressions, e.g. for the `patch` egg
(map diffop->sexp hunks)
;; => ((c 2 2 2 2 ("b") ("x")))
```

## API

### `(npdiff A B [context-len]) => (hunk ...)`

Compares sequences `A` and `B` and returns a list of `diffop` hunks
describing the edit script that transforms `A` into `B`.

- `A`, `B` -- the two sequences to compare. Any type implementing the
  `yasos-collections` collection interface (lists and vectors are
  supported out of the box).
- `context-len` -- optional; the number of surrounding elements to
  capture as context around each hunk (used by the context-diff
  formatter). Defaults to `0`.

### `(make-hunks A B css [context-len]) => (hunk ...)`

Lower-level procedure used by `npdiff` to construct hunks from the
stack of common substrings found by the comparison algorithm.
Provided for advanced use; most callers should use `npdiff` directly.

### The `diffop` datatype

`(define-datatype diffop diffop? ...)`

Represents the three diff operations: insert, remove, and change. In
each case, `target` refers to a position or range of positions in the
sequence being transformed (`B`), and `source` refers to a range of
positions in the sequence being read from (`A`).

- **`(Insert target source seq context)`**
  - `target` -- index in `B` at which the insertion takes place.
  - `source` -- range `(x . y)` of indices in `A` that are inserted.
  - `seq` -- the inserted elements.
  - `context` -- optional `(before . after)` pair of surrounding elements.

- **`(Remove target seq context)`**
  - `target` -- range `(x . y)` of indices in `A` being removed.
  - `seq` -- the removed elements.
  - `context` -- optional `(before . after)` pair of surrounding elements.

- **`(Change target source seqin seqout contextin contextout)`**
  - `target` -- range `(x . y)` of indices in `A` being replaced.
  - `source` -- range `(x . y)` of indices in `B` replacing them.
  - `seqin` -- the replacement elements (from `B`).
  - `seqout` -- the elements being replaced (from `A`).
  - `contextin`, `contextout` -- optional `(before . after)` context
    pairs for `B` and `A`, respectively.

### Output formatters

Each formatter writes to an output port and takes the list of hunks
returned by `npdiff`, in the order hunks are produced (most recent
first); callers do not need to reverse the list first.

- **`(format-hunks/normal out hunks)`** -- POSIX/classic `diff` format
  (`NcM`, `NaM`, `NdM` with `<`/`>`/`---` markers).
- **`(format-hunks/ed out hunks)`** -- `ed` script format.
- **`(format-hunks/rcs out hunks)`** -- RCS diff format.
- **`(format-hunks/context out hunks fname1 tstamp1 fname2 tstamp2)`**
  -- context diff format (`diff -c`), with adjacent hunks merged into
  shared blocks when their context windows overlap. `fname1`/`tstamp1`
  and `fname2`/`tstamp2` label the `***`/`---` file headers.

### S-expression output

- **`(diffop->sexp h) => sexp`** -- converts a single hunk into an
  s-expression of the form
  `([c|a|d] start end new-start new-end (removed ...) (inserted ...))`.
- **`(hunks->sexp hunks) => (sexp ...)`** -- converts a whole hunk
  list in one pass, in file order. Unlike mapping `diffop->sexp` over
  the list directly, this fills in a real `B`-side position for
  `Remove` hunks (rather than `#f`), which is required by consumers
  such as the `patch` egg when reversing a patch.

## Testing

```bash
csi -s tests/run.scm
```

### License

GPL-3. Copyright 2007-2026 Ivan Raikov. See [LICENSE](LICENSE) for
the full text.
