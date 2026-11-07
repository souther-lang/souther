package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A relation over how often a key occurs, read off a fold that counts under each key, is reached
 * at every value of the count: the count's own steps stop no run on the way to it.
 *
 * <p>By induction over the walk. A run that gets to an element got past every step before it, so
 * what it files into holds no more keys than the elements before, and what it finds under the key
 * is what the law makes of the elements before that have it — fewer than a collection holds. So
 * neither the filing nor the move of the count stops it. And where the list it walks is built of a
 * piece of each element, a count taking a value is reached on a row whose elements each hold the
 * key once, which holds no more pieces than a list does. That is so of every count of the elements
 * of one container: how often a key the caller names occurs, read through a lookup the way only
 * passes where it occurs, and how many issues there are beside a list built of their labels.
 *
 * <p>What is shown is shown of the count's own operations where they stand in its step, and of
 * nothing else: a key worked out by an operation that may pass an {@code Int}, a move by more than
 * a full collection keeps inside an {@code Int}, a move written as a closure handed by name, a
 * walk of its own inside what is counted, and a product past an {@code Int} worked out after the
 * count each still stop a run on the places they read, which a relation after the count then
 * reads.
 *
 * <p>And the witness of a count holds the counted container at the most it holds, which a rule of
 * the container may lower, and does not claim a row where what is inside the container is held to
 * more than one element: a count of copies then holds more pieces than the walk's list may. Which
 * values the count takes is a claim of its own, of rows of copies, and the witness makes none.
 */
class ACountAFoldFilesUnderEachKeyGetsARunToEveryValueItTakesTest {

    private static final String DECLARED = """
            module example.counts

            data Label = String
                invariant String.length(value) >= 1
            data Issue = { labels: Set<Label>, n: Int }
            data Board = { issues: List<Issue> }
            data FewIssues = { issues: List<Issue> }
                invariant List.length(issues) <= 3
            data ManyIssues = { issues: List<Issue> }
                invariant List.length(issues) >= 2
            data Ticket = { id: String, labels: Set<Label> }
            data Apart = { issues: List<Ticket> }
                invariant List.allDistinctBy(t -> t.id, issues)
            data Paired = { labels: Set<Label> }
                invariant Set.size(labels) >= 2
            data Pairs = { issues: List<Paired> }
            data Usage = { counts: Map<String, Int> }
            data Item = { code: Label }
            data Seen = { keys: List<String>, busy: Bool }
            data No

            let keysOf (issues: List<Issue>): List<String> =
                List.flatMap(i -> List.map(l -> l.value, Set.toList(i.labels)), issues)
            let ticketKeys (issues: List<Ticket>): List<String> =
                List.flatMap(i -> List.map(l -> l.value, Set.toList(i.labels)), issues)
            let pairKeys (issues: List<Paired>): List<String> =
                List.flatMap(i -> List.map(l -> l.value, Set.toList(i.labels)), issues)

            let byOne (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty, ks)
            let oneBy (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> 1 + n, acc), Map.empty, ks)
            let byTwo (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 2, acc), Map.empty, ks)
            let byTooMuch (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 4294967301, acc),
                        Map.empty, ks)
            let looked (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> match Map.get(k, acc) with
                    | Some n -> Map.insert(k, n + 1, acc)
                    | None -> Map.insert(k, 1, acc), Map.empty, ks)
            let stepNamed (ks: List<String>): Map<String, Int> = {
                let step: (Map<String, Int>, String) -> Map<String, Int> =
                    (acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc)
                List.fold(step, Map.empty, ks)
            }
            let moveNamed (ks: List<String>): Map<String, Int> = {
                let bump: (Int) -> Int = n -> n + 1
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, bump, acc), Map.empty, ks)
            }
            let byNext (issues: List<Issue>): Map<String, Int> =
                List.fold((acc, i) -> Map.updateOrInsert(String.fromInt(i.n + 1), 1, n -> n + 1,
                        acc), Map.empty, issues)
            let byOwn (issues: List<Issue>): Map<String, Int> =
                List.fold((acc, i) -> Map.updateOrInsert(String.fromInt(i.n), 1, n -> n + 1,
                        acc), Map.empty, issues)
            let nextOf (issues: List<Issue>): List<String> =
                List.fold((l, i) -> List.append(l, [String.fromInt(i.n + 1)]), [], issues)
            let byDown (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n - 1, acc), Map.empty, ks)
            let lessInside (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> {
                    let less = n - 1
                    n + 1
                }, acc), Map.empty, ks)
            let doubledInside (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> {
                    let twice = n * 2
                    n + 1
                }, acc), Map.empty, ks)
            let farInside (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> {
                    let far = n * 4294967301
                    n + 1
                }, acc), Map.empty, ks)
            let walkInStep (ks: List<String>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> {
                    let inner = List.fold((a, _) -> a * 3, n, ks)
                    n + 1
                }, acc), Map.empty, ks)
            let gathered (ks: List<String>): Set<String> =
                List.fold((s, k) -> Set.insert(k, s), Set.empty, ks)
            let doubled (ks: List<String>): List<String> =
                List.fold((l, _) -> List.append(l, l), ks, ks)

            behavior countedByOne : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedByOne (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        byOne(keysOf(board.issues))) }

            behavior countedOneBy : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedOneBy (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        oneBy(keysOf(board.issues))) }

            behavior countedLooked : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedLooked (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        looked(keysOf(board.issues))) }

            behavior countedStepNamed : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedStepNamed (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        stepNamed(keysOf(board.issues))) }

            behavior countedMoveNamed : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedMoveNamed (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        moveNamed(keysOf(board.issues))) }

            behavior countedFew : (board: FewIssues, atLeast: Int) -> Usage
                constructs Usage
            let countedFew (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        byOne(keysOf(board.issues))) }

            behavior countedMany : (board: ManyIssues, atLeast: Int) -> Usage
                constructs Usage
            let countedMany (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        byOne(keysOf(board.issues))) }

            behavior countedApart : (board: Apart, atLeast: Int) -> Usage
                constructs Usage
            let countedApart (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        byOne(ticketKeys(board.issues))) }

            behavior outsideThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let outsideThenGuard (board, atLeast) = {
                let counts = byOne(keysOf(board.issues))
                let far = List.length(board.issues) * 4611686018427387904
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = Map.insert("far", far, counts) }
            }

            behavior countedPaired : (board: Pairs, atLeast: Int) -> Usage
                constructs Usage
            let countedPaired (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        byOne(pairKeys(board.issues))) }

            behavior countedOfAKey : (board: Board, key: String, atLeast: Int) -> Bool
            let countedOfAKey (board, key, atLeast) =
                match Map.get(key, byOne(keysOf(board.issues))) with
                    | Some c -> c >= atLeast
                    | None -> false

            behavior issuesBesideTheirKeys : (board: Board, atLeast: Int) -> Seen
                constructs Seen
            let issuesBesideTheirKeys (board, atLeast) = {
                let ks = keysOf(board.issues)
                Seen { keys = ks, busy = List.length(board.issues) >= atLeast }
            }

            behavior byOneThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let byOneThenGuard (board, atLeast) = {
                let counts = byOne(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior byTwoThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let byTwoThenGuard (board, atLeast) = {
                let counts = byTwo(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior byTooMuchThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let byTooMuchThenGuard (board, atLeast) = {
                let counts = byTooMuch(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior ownKeyThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let ownKeyThenGuard (board, atLeast) = {
                let counts = byOwn(board.issues)
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior nextKeyThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let nextKeyThenGuard (board, atLeast) = {
                let counts = byNext(board.issues)
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior moveNamedThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let moveNamedThenGuard (board, atLeast) = {
                let counts = moveNamed(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior walkInsideThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let walkInsideThenGuard (board, atLeast) = {
                let counts = byOne(nextOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior downThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let downThenGuard (board, atLeast) = {
                let counts = byDown(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior lessInsideThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let lessInsideThenGuard (board, atLeast) = {
                let counts = lessInside(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior doubledInsideThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let doubledInsideThenGuard (board, atLeast) = {
                let counts = doubledInside(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior farInsideThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let farInsideThenGuard (board, atLeast) = {
                let counts = farInside(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior walkInStepThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let walkInStepThenGuard (board, atLeast) = {
                let counts = walkInStep(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior lookedThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let lookedThenGuard (board, atLeast) = {
                let counts = looked(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior stepNamedThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let stepNamedThenGuard (board, atLeast) = {
                let counts = stepNamed(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = counts }
            }

            behavior gatheredThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let gatheredThenGuard (board, atLeast) = {
                let seen = gathered(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = Map.insert("seen", Set.size(seen), Map.empty) }
            }

            behavior doubledThenGuard : (board: Board, atLeast: Int) -> Usage | No
                constructs Usage
            let doubledThenGuard (board, atLeast) = {
                let twice = doubled(keysOf(board.issues))
                guard List.length(board.issues) >= atLeast else No
                Usage { counts = Map.insert("twice", List.length(twice), Map.empty) }
            }
            """;

    private static final String THE_COUNT = "occurrences(board.issues[*].labels[*])";
    private static final String HOW_MANY_ISSUES = "List.length(board.issues)";

    private static final UndividedPosition.Reason RELATES =
            UndividedPosition.Reason.RULE_RELATING_TWO_VALUES;
    private static final UndividedPosition.Reason NOT_REACHED =
            UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE;
    private static final UndividedPosition.Reason NOT_TO_REACH =
            UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE;

    private static final Map<String, PartitionEvidence> COVERAGE = coverage();

    @Test
    void eachWayOfWritingTheCountIsReachedAtEveryValueAndAMoveHandedByNameIsNot() {
        Map<String, List<UndividedPosition.Reason>> expected = new LinkedHashMap<>();
        expected.put("countedByOne", List.of(RELATES));
        expected.put("countedOneBy", List.of(RELATES));
        expected.put("countedLooked", List.of(RELATES));
        expected.put("countedStepNamed", List.of(RELATES));
        expected.put("countedFew", List.of(RELATES));
        expected.put("countedMany", List.of(RELATES));
        expected.put("countedApart", List.of(RELATES));
        expected.put("countedMoveNamed", List.of(NOT_REACHED));
        assertEquals(expected, reasonsAt(THE_COUNT, expected.keySet()));
    }

    /**
     * That a count takes every value is a claim of the rows of copies of one element, and the
     * witness's bound on how many the counted container holds is none of it. So the bar is read
     * with its lines where a row of copies takes every count, and is not shown reached where the
     * container is held to a few, or to two at least, where its elements are kept apart by an id
     * so no element is held over again, or where what is inside each is held to two.
     */
    @Test
    void theBarIsReadOnlyWhereARowOfCopiesTakesEveryCount() {
        Map<String, List<UndividedPosition.Reason>> expected = new LinkedHashMap<>();
        expected.put("countedByOne", List.of());
        expected.put("countedFew", List.of(NOT_TO_REACH));
        expected.put("countedMany", List.of(NOT_TO_REACH));
        expected.put("countedApart", List.of(NOT_TO_REACH));
        expected.put("countedPaired", List.of(NOT_TO_REACH));
        assertEquals(expected, reasonsAt("atLeast", expected.keySet()));
    }

    @Test
    void everyCountOfOneContainersElementsIsReachedBesideAListBuiltOfThem() {
        assertEquals(List.of(RELATES),
                reasonsAt("occurrences(board.issues[*].labels[*] equal to key)",
                        List.of("countedOfAKey")).get("countedOfAKey"));
        assertEquals(List.of(RELATES),
                reasonsAt(HOW_MANY_ISSUES, List.of("issuesBesideTheirKeys"))
                        .get("issuesBesideTheirKeys"));
    }

    /** A count of copies of an issue held to two labels holds twice the pieces it counts, which
     *  a list built of them may not hold at every count: no row is claimed. */
    @Test
    void aCountOverContainersHeldToMoreThanOneElementIsNotClaimed() {
        List<UndividedPosition.Reason> paired =
                reasonsAt(THE_COUNT, List.of("countedPaired")).get("countedPaired");
        assertFalse(paired.contains(RELATES), paired.toString());
    }

    /** The places the count's walk reads, read after it: the count's own operations stop no run
     *  there, and any other operation that may stops a run as it did. */
    @Test
    void onlyTheCountsOwnOperationsAreShownToStopNoRun() {
        Map<String, List<UndividedPosition.Reason>> expected = new LinkedHashMap<>();
        expected.put("byOneThenGuard", List.of(RELATES));
        expected.put("byTwoThenGuard", List.of(RELATES));
        expected.put("ownKeyThenGuard", List.of(RELATES));
        expected.put("byTooMuchThenGuard", List.of(NOT_REACHED));
        expected.put("nextKeyThenGuard", List.of(NOT_REACHED));
        expected.put("moveNamedThenGuard", List.of(NOT_REACHED));
        expected.put("walkInsideThenGuard", List.of(NOT_REACHED));
        expected.put("outsideThenGuard", List.of(NOT_REACHED));
        expected.put("downThenGuard", List.of(RELATES));
        expected.put("lookedThenGuard", List.of(RELATES));
        expected.put("stepNamedThenGuard", List.of(RELATES));
        assertEquals(expected, reasonsAt(HOW_MANY_ISSUES, expected.keySet()));
    }

    /**
     * What the count finds under a key lies between one and the elements before the last of a
     * full collection, and any arithmetic over it is asked against that: one less and twice stay
     * within an {@code Int}, a product by more than a full collection keeps inside one may pass
     * it. A walk inside the step is asked of its own: what it carries holds nothing the count
     * says.
     */
    @Test
    void whatIsWorkedOutOfTheValueFoundIsAskedOfWhereThatValueLies() {
        Map<String, List<UndividedPosition.Reason>> expected = new LinkedHashMap<>();
        expected.put("lessInsideThenGuard", List.of(RELATES));
        expected.put("doubledInsideThenGuard", List.of(RELATES));
        expected.put("farInsideThenGuard", List.of(NOT_REACHED));
        expected.put("walkInStepThenGuard", List.of(NOT_REACHED));
        assertEquals(expected, reasonsAt(HOW_MANY_ISSUES, expected.keySet()));
    }

    /**
     * A walk that puts one element in what it carries at each element holds no more than the
     * elements it walks, whatever it is built for: a set gathered from the empty set fits on every
     * run. One that joins what it carries to itself doubles it, and still stops a run.
     */
    @Test
    void aWalkPuttingInOneElementAtEachFitsOnEveryRun() {
        Map<String, List<UndividedPosition.Reason>> expected = new LinkedHashMap<>();
        expected.put("gatheredThenGuard", List.of(RELATES));
        expected.put("doubledThenGuard", List.of(NOT_REACHED));
        assertEquals(expected, reasonsAt(HOW_MANY_ISSUES, expected.keySet()));
    }

    /** For each of {@code behaviors}, the reasons its rules give at {@code place}. */
    private static Map<String, List<UndividedPosition.Reason>> reasonsAt(
            String place, Iterable<String> behaviors) {
        Map<String, List<UndividedPosition.Reason>> out = new LinkedHashMap<>();
        for (String each : behaviors) {
            PartitionEvidence evidence = COVERAGE.get(each);
            assertNotNull(evidence, "the model under test compiles: " + each);
            out.put(each, evidence.notRead().stream()
                    .filter(one -> one.at().equals(place))
                    .map(PartitionEvidence.NotRead::reason).sorted().distinct().toList());
        }
        return out;
    }

    private static Map<String, PartitionEvidence> coverage() {
        Compilation compilation = Compilation.ofSource(DECLARED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db().ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
    }
}
