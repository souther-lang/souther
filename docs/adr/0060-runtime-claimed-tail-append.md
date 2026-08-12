# ADR-0060: A tail slot is claimed, so append does not copy the tail

Status: Accepted. Amends ADR-0042.

## Context

ADR-0042 left fold accumulation with "its persistent per-element allocation" and said to reopen the
question "with a workload, not on principle". Here is the workload.

Allocation per element, measured with `ThreadMXBean.getThreadAllocatedBytes` after warm-up, on
GraalVM 25.0.3 and Zulu 21.0.9 (arm64):

| path | HotSpot 21 (C2) | GraalVM 25 |
| --- | --- | --- |
| `acc ++ [x]` over 1000 elements — what `List.map` emits | 144 B/element | 112 B/element |
| accumulating into an `ArrayList`, converting once at the end | 43.9 B/element | 43.8 B/element |
| an unboxed `long[]` | 8.0 B/element | 8.0 B/element |
| a fold that only reduces (`Int` or `Decimal` sum) | — | ~0.1 B/element |

A fold that only reduces costs nothing: escape analysis erases the per-element `Option.Some` from
`List.get`, the `Object[]` from `Fn.apply`, and `BigDecimal`'s intermediates. A fold that *builds* a
list does not, because the list escapes. Of its 144 bytes, 16 are the boxed `Long`, 40 the new
`PersistentVector`, about 4.5 the trie spine on spill — and about 82 are the tail: `append`
allocated `new Object[tail.length + 1]` and copied the whole tail on every element, an average of 16
element-copies and 80 bytes of zero-fill each time.

## Decision

A tail array is `WIDTH` (32) wide with only `cnt - tailoff()` slots in use, and successive appends
write into the same array instead of copying it.

A `Tail` holds the array, an owning thread, and a count of slots handed out. Slot `j` belongs to
whoever moves `claimed` from `j` to `j + 1`, so **each slot is written at most once, ever**. A
version holding `m` elements reads only `[0, m)`, and `claimed == m` when it was constructed, so
those slots were all written before it existed. A second append off that same version loses the
claim and copies `[0, m)` into a fresh array, so branching keeps working and `EMPTY` — whose tail is
sealed with `claimed == a.length == 0` — can never take an element.

**The claim is confined to one thread rather than made atomic.** Every slot a version can read is
then written by the thread that froze that version, before the freeze, so the JLS 17.5 guarantee for
objects reachable from a final field still covers the whole tail — a vector handed to another thread
reads correctly even when it was published through a data race, exactly as when every append
allocated a fresh array. A compare-and-set would let two threads write one array and lose that
guarantee formally, in a way no test would show and no bug report could be traced back to. It would
also put a lock-prefixed instruction on the path whose whole purpose is to be cheap. An append from
a non-owning thread copies once and owns the copy, which costs nothing on the fold path.

The bulk `Builder` keeps its exact-size array and hands it over sealed. Its "single use" is
documented rather than enforced, and a decoded or sorted list is long-lived: `from(List.of(a, b, c))`
should not carry a 32-wide array for appends that will never come.

Nothing in the compiler changes. The claim is a property of the runtime structure, not of the shape
of a step, so it applies to every `++` — the fourteen distinct combinator shapes in `souther/list.sou`,
the ones threading an accumulator inside a tuple, and user code alike.

## Consequences

Measured the same way as above, before and after:

| path | HotSpot 21 (C2) | GraalVM 25 |
| --- | --- | --- |
| `List.map` building a 1000-element list, through the behavior | 160 → 106 B/element | 112 → 66 B/element |
| `Lists.append`, which is what `acc ++ [x]` emits | 144 → 66 B/element | 112 → 38 B/element |
| `PersistentVector.append` alone, unboxed (the budget test) | 128 → 50 B/element | 128 → 50 B/element |
| a behavior returning a unit data | — | 16 → 0 B/call |

`append`'s constant factor also goes from O(32) to O(1) — an average 16-element `arraycopy` and 80
bytes of zero-fill per element are gone — so the wall-clock gain is larger than the allocation gain.

On C2 this **does not reach** the 43.9 bytes the `ArrayList` route costs. The floor there is the
40-byte `PersistentVector` allocated per append, which cannot be removed here: the previous version's
`cnt` is its identity, so a new object is mandatory. Reaching it needs the per-element vector to
disappear, which needs a real transient accumulator with a linearity guarantee — still what ADR-0042
deferred, and still deferred. On GraalVM it goes *below* 43.9, because once the tail copy is gone the
remaining vector no longer escapes far enough to defeat that compiler's escape analysis. Do not read
the Graal figure as the general case.

Two costs are accepted.

Appending repeatedly to the same retained *small* list allocates more than before. `base ++ [x]`
with a three-element `base` copied 32 bytes each time and now copies 176. The number of copies is
unchanged — every one of them copied before too — but each is bigger, and the crossover is around
six or seven elements. If it matters, the copy path can size its array at `min(WIDTH, nextPow2(n+1))`
and treat `a.length` as the capacity; spill only happens at `n == WIDTH == a.length`, so the sealing
rule survives a variable capacity unchanged.

A retained early version whose descendants grew keeps a 32-wide array alive, pinning up to 31
elements that are not logically part of it — at most 128 bytes and 31 references per retained
vector. This is the `String.slice` retention class of problem. Keeping the `Builder` at exact
size keeps it out of the decode path, where it would be worst.

`arrayFor` now returns an array that may be longer than the logical leaf. Every reader already bounds
itself by `cnt`, and that is the invariant a later change here is most likely to break, so it is
stated on the method.

ADR-0051 is untouched: nothing keys on the name `fold`, and there is still no fold node in the Core
IR.

## References

- ADR-0042 (deferred a compiler-side transient accumulator; this takes the runtime-side half and
  leaves that deferral standing)
- ADR-0051 (`fold` is a recursive helper, not a privileged loop)
- ADR-0039 (Set is a collection type; the persistent collections these decisions sit on)
- `PersistentVectorAllocationTest` (the budget this decision has to keep) and `PersistentVectorTest`
  (`everyIntermediateVersionStaysIntact`, `branchingOffEveryPrefixKeepsAllThreeCorrect`, and the two
  cross-thread cases — the tests that fail if the claim is wrong)
- Prior art: Clojure's transient vectors, which solve the same constant factor with an edit token and
  an ownership discipline the caller has to respect
