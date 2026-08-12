# ADR-0061: CHAMP gets a bulk builder, not a transient

Status: Accepted. Amends ADR-0042.

## Context

ADR-0060 took the fold path's cost out of `PersistentVector` by letting successive appends claim a
slot in a shared tail. The obvious next question is whether the same applies to `PersistentHashMap`
and `PersistentHashSet`, which `groupBy`, `indexBy`, `Map.mapValues`, `Map.filterEntries`, `Set.partition` and
`List.distinct` all grow one entry at a time.

Allocation per entry, measured with `ThreadMXBean.getThreadAllocatedBytes` after warm-up on GraalVM
25.0.3 (arm64), building a 1000-entry map:

| path | before |
| --- | --- |
| `PersistentHashMap.from` — every decoded `Map` field, `Map.fromList` | 406 B/entry |
| `PersistentHashSet.from` — every decoded `Set` field, `Set.map`/`filter`, the set algebra | 415 B/entry |
| `assoc` one entry at a time — `groupBy`, `indexBy`, `Map.mapValues`, `distinct` | 357 B/entry |

`from` costing *more* than the element-wise loop it exists to replace is the first thing to notice:
it had no bulk path at all, and simply looped `assoc` over an intermediate `HashMap`.

## Decision

**The claimed tail does not transfer, and no runtime check can replace it here.** What makes a
vector's in-place write safe is that the slot it writes is one no existing version reads — a version
holding `m` elements reads `[0, m)` and nothing beyond. A CHAMP insert has no such region: it
rewrites the `dataMap`/`nodeMap` bitmaps that older versions read to interpret the very same array,
so any in-place write is observable by every version sharing that node. Ownership cannot be
established after the fact by a claim, a generation counter or a thread check, because the question
is not *who may write* but *who can see* — and the answer is everyone holding an older map.

So the mutation is confined to where linear use is a fact rather than a hope: a **bulk builder**,
package-private, used once, from empty, whose trie never leaves the method building it. It backs
`PersistentHashMap.from`, `Maps.fromList`, `Maps.mapKeys`, `PersistentHashSet.from`, and the
`union`/`intersect`/`difference` algebra. This is the same confinement the vector's `Builder` already
had, and the same reasoning ADR-0042 used to explain why that one was safe while a general transient
was not.

**Ownership is a flag threaded down the call, not a mark on each node.** Starting from the shared
empty node and only ever inserting, every node the builder can reach below the root is one it built —
nothing adopts a node from elsewhere. The empty node is the one it does not own and is never written,
since a write needs an entry or a child to replace and it has neither. Marking each node instead
would have put a reference on every node of every map: measured, that cost the persistent `assoc`
path 6% to speed up the bulk path, which is the wrong trade because `assoc` is the common one.

A node's fields stay final, so a map is still safely published through them (ADR-0060). What the
flag permits is writing an *element* of an array that no other version can reach.

## Consequences

| path | before | after |
| --- | --- | --- |
| `PersistentHashMap.from` | 406 B/entry | 167 B/entry |
| `PersistentHashSet.from` | 415 B/entry | 164 B/entry |
| `assoc` one entry at a time | 357 B/entry | 357 B/entry |

Bulk construction runs about 2.4× leaner, and the persistent path is untouched — deliberately, and
the allocation test asserts the first row so it stays that way.

**The fold-accumulated stdlib is not covered and cannot be, at this layer.** `List.groupBy`,
`List.indexBy`, `List.distinct`, `Map.mapValues`, `Map.filterEntries`, `Map.union`, `Map.intersection` and
`Set.partition` call `Map.insert`/`Set.insert` per element from generated code, where the accumulator
is a genuine persistent value the caller may branch on. Making those cheaper needs the accumulator to
be known linear, which is the compiler-side analysis ADR-0042 deferred and still defers. What did
improve for them is indirect: `Set.map` and `Set.filter` are written over `toList`/`fromList`, so
they take the bulk path, and `groupBy`'s bucket lists were already faster through ADR-0060.

A caller who does want the bulk path can reach it from Souther today by going out through `toList`
and back through `fromList` — which is what `Set.map` does. That is a workaround, not a design, and
it is the shape the deferred analysis would remove the need for.

## References

- ADR-0042 (deferred a transient accumulator "behind a linearity check"; this takes the half where
  linearity is structural rather than checked, and leaves the other half deferred)
- ADR-0060 (the claimed tail, whose argument this one explains does not generalize)
- ADR-0039 (Set is a collection type)
- `PersistentHashMapAllocationTest` (the budget this decision has to keep),
  `PersistentHashMapTest.aBuiltMapIsPersistentAfterwards` and
  `PersistentHashSetTest.aBulkBuiltSetIsPersistentAfterwards` (the tests that fail if ownership
  leaks past `build`)
- Prior art: Clojure's transient maps, which solve the general case with an edit token and require
  the caller to use the value linearly — a contract Souther has no way to state
