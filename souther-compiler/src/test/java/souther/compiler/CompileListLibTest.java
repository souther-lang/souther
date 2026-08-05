package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/** The List standard library beyond map/filter/all/any (spec 18.4): the further Elm combinators
 *  derived from {@code fold}, plus the native {@code sort} primitive and String ordering. */
class CompileListLibTest {

    @Test
    void foldDerivedCombinators() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( reverse, sum, product, contains, isEmpty )

                data In = { ns: List<Int> }
                data Out = {
                    reversed: List<Int>
                    , total: Int
                    , prod: Int
                    , hasTwo: Bool
                    , none: Bool
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    reversed = reverse(i.ns),
                    total = sum(i.ns),
                    prod = product(i.ns),
                    hasTwo = contains(2, i.ns),
                    none = isEmpty(i.ns)
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, decodeIn(loader, List.of(1L, 2L, 3L)));

        Map<?, ?> m = encode(loader, out);
        assertEquals(List.of(3L, 2L, 1L), m.get("reversed"));
        assertEquals(6L, m.get("total"));
        assertEquals(6L, m.get("prod"));
        assertEquals(true, m.get("hasTwo"));
        assertEquals(false, m.get("none"));
    }

    @Test
    void sortOfAnEmptyListLiteralIsAllowedAndYieldsEmpty() throws Exception {
        // The empty-list literal types as `List<Nothing>`; sorting it is valid (it sorts to itself),
        // so the ordered-element guard must let the bottom element through.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort )

                data In = { ns: List<Int> }
                data Out = { xs: List<Int> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { xs = sort([]) }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, decodeIn(loader, List.of()));
        assertEquals(List.of(), ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("xs"));
    }

    @Test
    void flattenAndSortAndStringOrder() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort, concat )

                data In = { tags: List<String> }
                data Out = {
                    sorted: List<String>
                    , joinedNested: List<Int>
                    , ascending: Bool
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    sorted = sort(i.tags),
                    joinedNested = concat([[1, 2], [3]]),
                    ascending = "alpha" < "beta"
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("tags", List.of("gamma", "alpha", "beta")));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        Map<?, ?> m = encode(loader, out);
        assertEquals(List.of("alpha", "beta", "gamma"), m.get("sorted"));
        assertEquals(List.of(1L, 2L, 3L), m.get("joinedNested"));
        assertEquals(true, m.get("ascending"));
    }

    @Test
    void distinctKeepsFirstOccurrenceAndDropsLaterDuplicates() throws Exception {
        // `distinct` reads the accumulator (via `member`) before growing it — the shape whose
        // accumulator element type must be recovered from the block, not the empty `[]` seed.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( distinct )

                data In = { ns: List<Int> }
                data Out = { ys: List<Int> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { ys = distinct(i.ns) }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, decodeIn(loader, List.of(3L, 1L, 3L, 2L, 1L)));
        assertEquals(List.of(3L, 1L, 2L), encode(loader, out).get("ys"));
    }

    @Test
    void partitionSplitsByPredicateKeepingOrderOnEachSide() throws Exception {
        // partition folds a pair of empty lists ([], []) — a tuple accumulator whose real shape is
        // recovered from the block, not the bottom seed.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( partition )

                data In = { ns: List<Int> }
                data Out = { big: List<Int>, small: List<Int> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    let (b, s) = partition(n -> n >= 100, i.ns)
                    Out { big = b, small = s }
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, decodeIn(loader, List.of(50L, 200L, 10L, 300L, 100L)));
        Map<?, ?> m = encode(loader, out);
        assertEquals(List.of(200L, 300L, 100L), m.get("big"));
        assertEquals(List.of(50L, 10L), m.get("small"));
    }

    @Test
    void groupByBucketsByKeyInFirstSeenOrder() throws Exception {
        // groupBy folds Map.empty — a Map accumulator read with Map.get and grown with Map.insert,
        // its key and value types recovered from the block. The result Map is read back in-body.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( groupBy )
                import Map ( size )

                data In = { ns: List<Int> }
                data Out = { groups: Int, positives: List<Int> }

                behavior run : (i: In) -> Out constructs Out

                let 符号 (n: Int) = if n >= 0 then "pos" else "neg"
                let run (i) = Out {
                    groups = Map.size(groupBy(符号, i.ns)),
                    positives = match Map.get("pos", groupBy(符号, i.ns)) with
                        | None -> []
                        | Some b -> b
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, decodeIn(loader, List.of(3L, -1L, 5L, -2L, 8L)));
        Map<?, ?> m = encode(loader, out);
        assertEquals(2L, m.get("groups"), "two buckets: pos and neg");
        assertEquals(List.of(3L, 5L, 8L), m.get("positives"), "the pos bucket keeps first-seen order");
    }

    @Test
    void indexByKeysTheElementsAndLetsTheLastDuplicateWin() throws Exception {
        // The read-then-look-up shape: rows in, one entry per key out, read back with Map.get.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( indexBy )
                import Map ( size )

                data 行 = { 品番: String, 数量: Int }
                data In = { rows: List<行> }
                data Out = { entries: Int, apple: Int, missing: Int }

                behavior run : (i: In) -> Out constructs Out

                let 数量 (品番: String, m: Map<String, 行>): Int =
                    match Map.get(品番, m) with
                        | None -> 0
                        | Some r -> r.数量

                let run (i) = {
                    let idx = indexBy(r -> r.品番, i.rows)
                    Out { entries = size(idx), apple = 数量("apple", idx), missing = 数量("nope", idx) }
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("rows", List.of(
                Map.of("品番", "apple", "数量", 3L),
                Map.of("品番", "orange", "数量", 5L),
                Map.of("品番", "apple", "数量", 9L))));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Map<?, ?> m = encode(loader, Codecs.apply(behavior, in));
        assertEquals(2L, m.get("entries"), "the repeated key holds one entry");
        assertEquals(9L, m.get("apple"), "the later row wins, as Map.fromList does");
        assertEquals(0L, m.get("missing"));
    }

    @Test
    void maxAndMinReturnOptionAndAreNoneForAnEmptyList() throws Exception {
        // max/min are native builtins returning Option, like List.get — fold cannot build them
        // (Souther has no in-language Some/None to fold into).
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( max, min )

                data In = { ns: List<Int> }
                data Out = { hi: Int, lo: Int, hasHi: Bool }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    hi = match List.max(i.ns) with | None -> 0 | Some m -> m,
                    lo = match List.min(i.ns) with | None -> 0 | Some m -> m,
                    hasHi = match List.max(i.ns) with | None -> false | Some m -> true
                }
                """), getClass().getClassLoader());

        Object run = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Map<?, ?> m = encode(loader, Codecs.apply(run, decodeIn(loader, List.of(3L, 9L, 1L, 7L))));
        assertEquals(9L, m.get("hi"));
        assertEquals(1L, m.get("lo"));
        assertEquals(true, m.get("hasHi"));

        Map<?, ?> empty = encode(loader, Codecs.apply(run, decodeIn(loader, List.of())));
        assertEquals(0L, empty.get("hi"), "max of [] is None");
        assertEquals(false, empty.get("hasHi"));
    }

    @Test
    void findReturnsTheFirstMatchOrNone() throws Exception {
        // find takes a predicate as a first-class function value (materialised as an Fn), returns
        // Option; it cannot be a fold (no in-language Some/None).
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( find )

                data In = { ns: List<Int> }
                data Out = { firstBig: Int, found: Bool }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    firstBig = match List.find(n -> n >= 100, i.ns) with | None -> 0 | Some n -> n,
                    found = match List.find(n -> n >= 100, i.ns) with | None -> false | Some n -> true
                }
                """), getClass().getClassLoader());

        Object run = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Map<?, ?> hit = encode(loader, Codecs.apply(run, decodeIn(loader, List.of(3L, 50L, 200L, 400L))));
        assertEquals(200L, hit.get("firstBig"), "the first element >= 100, in order");
        assertEquals(true, hit.get("found"));
        Map<?, ?> miss = encode(loader, Codecs.apply(run, decodeIn(loader, List.of(1L, 2L, 3L))));
        assertEquals(false, miss.get("found"), "no match is None");
    }

    @Test
    void sortByOrdersByAKeyFunction() throws Exception {
        // sortBy takes a key function (an Fn) and sorts by the key's natural order.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sortBy, fold )

                data In = { ns: List<Int> }
                data Out = { byNegation: List<Int> }

                behavior run : (i: In) -> Out constructs Out

                // sort descending by keying on the negated value
                let run (i) = Out {
                    byNegation = List.sortBy(n -> 0 - n, i.ns)
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, decodeIn(loader, List.of(3L, 1L, 4L, 1L, 5L)));
        assertEquals(List.of(5L, 4L, 3L, 1L, 1L), encode(loader, out).get("byNegation"));
    }

    @Test
    void mapIndexedAppliesTheZeroBasedIndexToEachElement() throws Exception {
        // mapIndexed threads a (i, ys) pair through fold — the same tuple-accumulator shape as
        // distinct/partition — so the user writes a positional transform without hand-rolling it.
        // Here it forms the EAN-13 weighted sum: even index weight 1, odd index weight 3.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( mapIndexed, sum )

                data In = { ns: List<Int> }
                data Out = { weighted: List<Int>, checksum: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    let ws = mapIndexed((idx, n) -> (if Int.floorMod(idx, 2) == 0 then 1 else 3) * n, i.ns)
                    Out { weighted = ws, checksum = sum(ws) }
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, decodeIn(loader, List.of(9L, 7L, 8L, 4L)));
        Map<?, ?> m = encode(loader, out);
        // indices 0..3 -> weights 1,3,1,3 -> 9, 21, 8, 12
        assertEquals(List.of(9L, 21L, 8L, 12L), m.get("weighted"));
        assertEquals(50L, m.get("checksum"));

        // empty list -> empty result (the fold never runs, the (0, []) seed is returned unmapped)
        Map<?, ?> empty = encode(loader, Codecs.apply(behavior, decodeIn(loader, List.of())));
        assertEquals(List.of(), empty.get("weighted"));
        assertEquals(0L, empty.get("checksum"));

        // single element -> index 0, weight 1
        Map<?, ?> one = encode(loader, Codecs.apply(behavior, decodeIn(loader, List.of(5L))));
        assertEquals(List.of(5L), one.get("weighted"));
    }

    @Test
    void allDistinctByHoldsWhenTheProjectedKeysAreDistinct() throws Exception {
        // allDistinctBy is the "this projection is a unique id" invariant: true when mapping the key
        // over the list leaves no duplicates. It derives from map/distinct, both fold-based.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( allDistinctBy )

                data Row = { sku: String, qty: Int }
                data In = { rows: List<Row> }
                data Out = { unique: Bool }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { unique = allDistinctBy(r -> r.sku, i.rows) }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();

        Object uniqueIn = Codecs.decoded(loader, "demo.In", Map.of("rows",
                List.of(Map.of("sku", "apple", "qty", 1L), Map.of("sku", "pear", "qty", 2L))));
        assertEquals(true, encode(loader, Codecs.apply(behavior, uniqueIn)).get("unique"));

        Object dupIn = Codecs.decoded(loader, "demo.In", Map.of("rows",
                List.of(Map.of("sku", "apple", "qty", 1L), Map.of("sku", "apple", "qty", 2L))));
        assertEquals(false, encode(loader, Codecs.apply(behavior, dupIn)).get("unique"),
                "a repeated key means the projection is not unique");

        // empty list -> vacuously unique (0 == 0), the edge the ordering.sou invariant relies on
        Object emptyIn = Codecs.decoded(loader, "demo.In", Map.of("rows", List.of()));
        assertEquals(true, encode(loader, Codecs.apply(behavior, emptyIn)).get("unique"),
                "an empty projection has no duplicates");

        // single element -> unique
        Object oneIn = Codecs.decoded(loader, "demo.In", Map.of("rows",
                List.of(Map.of("sku", "apple", "qty", 1L))));
        assertEquals(true, encode(loader, Codecs.apply(behavior, oneIn)).get("unique"));
    }

    /** {@code take}/{@code drop} cut the list at an index (Elm's List.take / List.drop), clamping at
     * both ends: a non-positive count takes nothing, a count past the end takes everything. */
    @Test
    void takeAndDropCutTheListAndClamp() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( take, drop )

                data In = { ns: List<Int> }
                data Out = {
                    firstTwo: List<Int>
                    , rest: List<Int>
                    , none: List<Int>
                    , all: List<Int>
                    , beyond: List<Int>
                    , dropAll: List<Int>
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    firstTwo = take(2, i.ns),
                    rest = drop(2, i.ns),
                    none = take(0, i.ns),
                    all = drop(0, i.ns),
                    beyond = take(99, i.ns),
                    dropAll = drop(99, i.ns)
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Map<?, ?> m = encode(loader, Codecs.apply(behavior, decodeIn(loader, List.of(1L, 2L, 3L, 4L))));

        assertEquals(List.of(1L, 2L), m.get("firstTwo"));
        assertEquals(List.of(3L, 4L), m.get("rest"));
        assertEquals(List.of(), m.get("none"));
        assertEquals(List.of(1L, 2L, 3L, 4L), m.get("all"));
        assertEquals(List.of(1L, 2L, 3L, 4L), m.get("beyond"), "a count past the end takes everything");
        assertEquals(List.of(), m.get("dropAll"), "dropping past the end leaves nothing");

        // a negative count behaves as 0 on both sides, and an empty input stays empty
        Map<?, ?> neg = encode(loader, Codecs.apply(behavior, decodeIn(loader, List.of())));
        assertEquals(List.of(), neg.get("firstTwo"));
        assertEquals(List.of(), neg.get("rest"));
    }

    /** {@code range} is the one list that is neither written out nor read from outside, so a walk
     *  over positions has something to walk. Both ends are included and a start above the end gives
     *  the empty list (Elm's List.rangeInclusive). */
    @Test
    void rangeCountsBetweenBothEndsInclusive() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( rangeInclusive, map )

                data In = { ns: List<Int> }
                data Out = { upTo: List<Int>, single: List<Int>, backwards: List<Int>, doubled: List<Int> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    upTo = rangeInclusive(1, 4),
                    single = rangeInclusive(7, 7),
                    backwards = rangeInclusive(3, 1),
                    doubled = map(n -> n * 2, rangeInclusive(0, 2))
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Map<?, ?> m = encode(loader, Codecs.apply(behavior, decodeIn(loader, List.of())));

        assertEquals(List.of(1L, 2L, 3L, 4L), m.get("upTo"));
        assertEquals(List.of(7L), m.get("single"), "both ends are included, so one value is one element");
        assertEquals(List.of(), m.get("backwards"), "a start above the end gives nothing");
        assertEquals(List.of(0L, 2L, 4L), m.get("doubled"));
    }

    /** A span longer than a list can hold aborts before the walk starts, rather than filling memory
     *  until it dies — the treatment an Int overflow gets (spec 18.2). */
    @Test
    void aRangeWiderThanAListCanHoldAborts() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( rangeInclusive, length )

                data In = { to: Int }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { n = length(rangeInclusive(1, i.to)) }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Object tooWide = Codecs.decoded(loader, "demo.In", Map.of("to", 3_000_000_000L));
        assertThrows(souther.runtime.ConstraintViolation.class, () -> Codecs.apply(behavior, tooWide));
    }

    /** {@code flatMap} maps to a list and joins in one pass; {@code foldRight} walks from the end.
     *  Both are the shapes a caller otherwise hand-rolls as a fold with {@code ++} in the step.
     *
     *  <p>{@code foldRight}'s step takes the element first and the accumulator second, the opposite
     *  of {@code fold}'s. Writing the same combination through both is what shows the walk really
     *  runs the other way: with a non-commutative step the two answers differ. */
    @Test
    void flatMapAndFoldRightWalkTheListWhole() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( flatMap, foldRight, fold )

                data In = { ns: List<Int> }
                data Out = { spread: List<Int>, rightward: String, leftward: String }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    spread = flatMap(n -> [n, n * 10], i.ns),
                    rightward = foldRight((n, acc) -> acc ++ String.fromInt(n), "", i.ns),
                    leftward = fold((acc, n) -> acc ++ String.fromInt(n), "", i.ns)
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Map<?, ?> m = encode(loader, Codecs.apply(behavior, decodeIn(loader, List.of(1L, 2L, 3L))));

        assertEquals(List.of(1L, 10L, 2L, 20L, 3L, 30L), m.get("spread"));
        assertEquals("321", m.get("rightward"), "foldRight sees the elements from the end");
        assertEquals("123", m.get("leftward"), "the left fold sees them from the head");

        Map<?, ?> empty = encode(loader, Codecs.apply(behavior, decodeIn(loader, List.of())));
        assertEquals(List.of(), empty.get("spread"));
        assertEquals("", empty.get("rightward"));
    }

    /** {@code zip} pairs two lists and truncates to the shorter one (Elm's {@code map2}); {@code
     *  unzip} takes the pairs apart again. The tuples stay inside the behavior — a tuple has no
     *  external form — so the boundary sees the two lists and a rendering of the pairs. */
    @Test
    void zipPairsTwoListsAndUnzipTakesThemApart() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( zipShortest, unzip, map )

                data In = { ns: List<Int>, ss: List<String> }
                data Out = { labels: List<String>, lefts: List<Int>, rights: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let label (p: (Int, String)): String = {
                    let (n, s) = p
                    s ++ String.fromInt(n)
                }

                let run (i) = {
                    let pairs = zipShortest(i.ns, i.ss)
                    let (ls, rs) = unzip(pairs)
                    Out { labels = map(label, pairs), lefts = ls, rights = rs }
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("ns", List.of(1L, 2L, 3L), "ss", List.of("a", "b")));
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));

        assertEquals(List.of("a1", "b2"), m.get("labels"), "the longer list is cut to the shorter one");
        assertEquals(List.of(1L, 2L), m.get("lefts"));
        assertEquals(List.of("a", "b"), m.get("rights"));

        Object none = Codecs.decoded(loader, "demo.In", Map.of("ns", List.of(), "ss", List.of("a")));
        Map<?, ?> empty = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, none));
        assertEquals(List.of(), empty.get("labels"));
        assertEquals(List.of(), empty.get("rights"), "nothing to pair leaves both sides empty");
    }

    private static Object decodeIn(BytesClassLoader loader, List<Long> ns) throws Exception {
        return Codecs.decoded(loader, "demo.In", Map.of("ns", ns));
    }

    private static Map<?, ?> encode(BytesClassLoader loader, Object out) throws Exception {
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
    }
}
