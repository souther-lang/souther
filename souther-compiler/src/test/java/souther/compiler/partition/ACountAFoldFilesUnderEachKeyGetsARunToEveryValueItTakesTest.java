package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
 * <p>Each holds only of the walk the step is applied by: a move written as a closure handed by
 * name may be applied to other values too, and is left as any operator is.
 */
class ACountAFoldFilesUnderEachKeyGetsARunToEveryValueItTakesTest {

    private static final String DECLARED = """
            module example.counts

            data Label = String
                invariant String.length(value) >= 1
            data Issue = { labels: Set<Label> }
            data Board = { issues: List<Issue> }
            data Usage = { counts: Map<String, Int> }
            data Item = { code: Label }
            data Seen = { keys: List<String>, busy: Bool }

            let keysOf (issues: List<Issue>): List<String> =
                List.flatMap(i -> List.map(l -> l.value, Set.toList(i.labels)), issues)

            let byOne (issues: List<Issue>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty,
                        keysOf(issues))
            let oneBy (issues: List<Issue>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> 1 + n, acc), Map.empty,
                        keysOf(issues))
            let looked (issues: List<Issue>): Map<String, Int> =
                List.fold((acc, k) -> match Map.get(k, acc) with
                    | Some n -> Map.insert(k, n + 1, acc)
                    | None -> Map.insert(k, 1, acc), Map.empty, keysOf(issues))
            let stepNamed (issues: List<Issue>): Map<String, Int> = {
                let step: (Map<String, Int>, String) -> Map<String, Int> =
                    (acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc)
                List.fold(step, Map.empty, keysOf(issues))
            }
            let moveNamed (issues: List<Issue>): Map<String, Int> = {
                let bump: (Int) -> Int = n -> n + 1
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, bump, acc), Map.empty,
                        keysOf(issues))
            }
            let flat (items: List<Item>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty,
                        List.map(i -> i.code.value, items))

            behavior countedByOne : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedByOne (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast, byOne(board.issues)) }

            behavior countedOneBy : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedOneBy (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast, oneBy(board.issues)) }

            behavior countedLooked : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedLooked (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast, looked(board.issues)) }

            behavior countedStepNamed : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedStepNamed (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        stepNamed(board.issues)) }

            behavior countedMoveNamed : (board: Board, atLeast: Int) -> Usage
                constructs Usage
            let countedMoveNamed (board, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast,
                        moveNamed(board.issues)) }

            behavior countedOfAKey : (board: Board, key: String, atLeast: Int) -> Bool
            let countedOfAKey (board, key, atLeast) =
                match Map.get(key, byOne(board.issues)) with
                    | Some c -> c >= atLeast
                    | None -> false

            behavior issuesBesideTheirKeys : (board: Board, atLeast: Int) -> Seen
                constructs Seen
            let issuesBesideTheirKeys (board, atLeast) = {
                let ks = keysOf(board.issues)
                Seen { keys = ks, busy = List.length(board.issues) >= atLeast }
            }

            behavior countedFlat : (items: List<Item>, atLeast: Int) -> Usage
                constructs Usage
            let countedFlat (items, atLeast) =
                Usage { counts = Map.filterEntries((_, c) -> c >= atLeast, flat(items)) }
            """;

    private static final List<String> THE_COUNT = List.of("occurrences(board.issues[*].labels[*])");

    @Test
    void eachWayOfWritingTheCountIsReachedAtEveryValueAndTheOthersAreNot() {
        Map<String, List<String>> expected = Map.of(
                "countedByOne", List.of(),
                "countedOneBy", List.of(),
                "countedLooked", List.of(),
                "countedStepNamed", List.of(),
                "countedFlat", List.of(),
                "countedOfAKey", List.of(),
                "issuesBesideTheirKeys", List.of(),
                "countedMoveNamed", THE_COUNT);
        assertEquals(expected, notReachedAtEveryValue(expected.keySet().stream().toList()));
    }

    /** For each of {@code behaviors}, the places a relation is read at that the run is not shown
     *  to get to at every value. */
    private static Map<String, List<String>> notReachedAtEveryValue(List<String> behaviors) {
        Compilation compilation = Compilation.ofSource(DECLARED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        return behaviors.stream().collect(Collectors.toMap(each -> each, each -> {
            PartitionEvidence evidence = coverage.get(each);
            assertNotNull(evidence, "the model under test compiles");
            return evidence.notRead().stream()
                    .filter(one -> one.reason()
                            == UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)
                    .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
        }));
    }
}
