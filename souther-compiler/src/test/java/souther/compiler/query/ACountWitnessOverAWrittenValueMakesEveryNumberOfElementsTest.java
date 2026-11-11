package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.check.Sig;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.inputs.InputReading;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.CountWitnesses;
import souther.compiler.partition.FixtureTemplate;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A count of the elements whose container holds a value the statement writes is witnessed by a
 * row, and the row's elements are counted by the count itself: with none of them kept the count
 * is none, with one it is one, and with both it is two.
 *
 * <p>The counts asked are the ones the compiled source led to, found among what the measure of
 * the model asked and not written here by hand, and the rows counted are the ones the boundary
 * builds from the elements the witness names.
 */
class ACountWitnessOverAWrittenValueMakesEveryNumberOfElementsTest {

    private static final String SOURCE = """
            module demo

            data Code = String

            data Line = { rates: Map<String, Int>, tags: List<String>, nums: Set<Int>,
                          coded: Map<Code, Int> }

            behavior viaMapSize : (lines: List<Line>, k: Int) -> Bool
            let viaMapSize (lines, k) =
                List.length(List.filter(l -> Map.size(l.rates) == 2
                    && Map.containsKey("USD", l.rates), lines)) == k

            behavior viaSetSize : (lines: List<Line>, k: Int) -> Bool
            let viaSetSize (lines, k) =
                List.length(List.filter(l -> Set.size(l.nums) == 3
                    && Set.contains(0, l.nums) && Bool.not(Set.contains(1, l.nums)),
                    lines)) == k

            behavior viaMap : (lines: List<Line>, k: Int) -> Bool
            let viaMap (lines, k) =
                List.length(List.filter(l -> Map.containsKey("USD", l.rates), lines)) == k

            behavior viaMapNot : (lines: List<Line>, k: Int) -> Bool
            let viaMapNot (lines, k) =
                List.length(List.filter(l -> Bool.not(Map.containsKey("USD", l.rates)), lines))
                    == k

            behavior viaList : (lines: List<Line>, k: Int) -> Bool
            let viaList (lines, k) =
                List.length(List.filter(l -> List.contains("K", l.tags), lines)) == k

            behavior viaSet : (lines: List<Line>, k: Int) -> Bool
            let viaSet (lines, k) =
                List.length(List.filter(l -> Set.contains(7, l.nums), lines)) == k

            behavior viaNewtype : (lines: List<Line>, k: Int) -> Bool
            let viaNewtype (lines, k) =
                List.length(List.filter(l -> Map.containsKey(Code("USD"), l.coded), lines)) == k

            behavior viaSizeAndMember : (lines: List<Line>, k: Int) -> Bool
            let viaSizeAndMember (lines, k) =
                List.length(List.filter(l -> List.length(l.tags) == 3
                    && List.contains("K", l.tags), lines)) == k
            """;

    /** The behaviors the model writes, each counted over its lines. */
    private static final List<String> BEHAVIORS = List.of("viaMap", "viaMapNot", "viaList",
            "viaSet", "viaNewtype", "viaSizeAndMember", "viaMapSize", "viaSetSize");

    /** The counts the measure of the model asked a witness of, by behavior. */
    private static Map<String, List<Adequacy.WitnessOfACount>> askedOf(Compilation compilation) {
        Set<Key<?>> reached = new HashSet<>();
        Deque<Key<?>> left = new ArrayDeque<>(List.of(new Adequacy.Coverage("demo")));
        Map<String, List<Adequacy.WitnessOfACount>> out = new LinkedHashMap<>();
        while (!left.isEmpty()) {
            for (Key<?> each : compilation.db().dependenciesOf(left.pop())) {
                if (reached.add(each)) {
                    if (each instanceof Adequacy.WitnessOfACount asked) {
                        out.computeIfAbsent(asked.behavior(), _ -> new ArrayList<>()).add(asked);
                    }
                    left.push(each);
                }
            }
        }
        return out;
    }

    /** {@code witness}'s row with the container holding {@code kept} of the elements the
     *  witness keeps and the rest of the ones it drops, two in all. */
    private static List<FixtureTemplate> rowKeeping(CountWitnesses.Witness witness, int kept) {
        List<FixtureTemplate> elements = new ArrayList<>();
        for (int each = 0; each < 2; each++) {
            elements.add(each < kept ? witness.kept() : witness.dropped());
        }
        List<FixtureTemplate> row = new ArrayList<>(witness.inputs());
        row.set(witness.container(), FixtureTemplate.collection(elements));
        return row;
    }

    private static Optional<Integer> countedOn(Compilation compilation, String behavior,
                                               Adequacy.WitnessOfACount asked,
                                               List<FixtureTemplate> row) {
        Db db = compilation.db();
        Sig sig = db.ask(new Bodies.Signatures("demo")).value().get(behavior);
        FixturesAtTheBoundary building = Adequacy.constructing(db, "demo");
        InputReading read = db.ask(new Adequacy.Inputs("demo")).value().get(behavior)
                .reading(RuleReadings.of(compilation, "demo"));
        return CountWitnesses.metOn(asked.count(), behavior, read, row,
                (at, fixture) -> building.build(sig.ins().get(at), fixture)
                        instanceof BoundaryValues.Built.Value(ObservedValue value)
                        ? Optional.of(value) : Optional.<ObservedValue>empty());
    }

    @Test
    void aRowOfTwoElementsIsCountedAtNoneOneAndTwoWhereTheyAreKeptOrDropped() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        compilation.db().ask(new Adequacy.Coverage("demo"));
        Map<String, List<Adequacy.WitnessOfACount>> asked = askedOf(compilation);
        for (String behavior : BEHAVIORS) {
            List<Adequacy.WitnessOfACount> counts = asked.getOrDefault(behavior, List.of());
            assertTrue(!counts.isEmpty(), () -> behavior + " asked a witness of its count");
            for (Adequacy.WitnessOfACount count : counts) {
                Optional<CountWitnesses.Witness> found =
                        compilation.db().ask(count).value().found();
                assertTrue(found.isPresent(), () -> behavior + " has a witness");
                for (int kept = 0; kept <= 2; kept++) {
                    List<FixtureTemplate> row = rowKeeping(found.get(), kept);
                    assertEquals(Optional.of(kept), countedOn(compilation, behavior, count, row),
                            behavior + " with " + kept + " kept: " + row);
                }
            }
        }
    }
}
