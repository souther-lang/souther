package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AsACompilationAllows;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What is kept for every reading of a row is kept by what reading it asked of the asking walk's
 * choices, and by nothing said beside it: a walk that chose alike there is handed it, one that
 * chose otherwise there reads it afresh, and something handed over that asks a choice later,
 * which the answer was not kept by, is refused rather than read as the asking walk's.
 */
class AnAnswerKeptForEveryReadingIsKeptByWhatReadingItAskedTest {

    private static final String MODEL = """
            module g

            data Line = { sku: String }

            data Order = { lines: List<Line>, rank: Int }

            behavior decide : (orders: List<Order>) -> Int
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());

    private static final TermPath ORDERS = TermPath.of("orders");

    private static final TermPath LINES = ORDERS.element().then("lines");

    private static final TermPath SKU = LINES.element().then("sku");

    /** The skus of the lines of the order a reading chose, by asking for each line. */
    private record SkusOfItsOrder() implements BorderQuantity.ReadAlike<List<ObservedValue>> {

        @Override
        public List<ObservedValue> readAt(BorderQuantity.Observation reading) {
            List<BorderQuantity.Observation> lines =
                    ((WalkResult.Reached<List<BorderQuantity.Observation>>)
                            reading.eachElementOf(LINES)).value();
            return lines.stream().map(line -> ((ObservationAtPoint.Value)
                    ((WalkResult.Reached<ObservationAtPoint>) line.at(SKU)).value()).value())
                    .toList();
        }
    }

    /** The orders, handed over to be read later. */
    private record TheOrders()
            implements BorderQuantity.ReadAlike<List<BorderQuantity.Observation>> {

        @Override
        public List<BorderQuantity.Observation> readAt(BorderQuantity.Observation reading) {
            return ((WalkResult.Reached<List<BorderQuantity.Observation>>)
                    reading.eachElementOf(ORDERS)).value();
        }
    }

    @Test
    void walksThatChoseAlikeWhereReadingAskedAreHandedOneAnswer() {
        StandingAtAPoint.RowWalk walk = walk();
        List<ObservedValue> first = reading(walk, 0, 0).keptOf(new SkusOfItsOrder());
        assertSame(first, reading(walk, 0, 1).keptOf(new SkusOfItsOrder()),
                "the line chosen is not asked, its order is");
        assertEquals(List.of(new ObservedValue.Text("c")),
                reading(walk, 1, 0).keptOf(new SkusOfItsOrder()), "another order is read afresh");
        assertEquals(2, walk.answersRead());
    }

    @Test
    void whatIsHandedOverAndAsksAChoiceLaterIsRefused() {
        StandingAtAPoint.RowWalk walk = walk();
        List<BorderQuantity.Observation> orders = reading(walk, 0, 1).keptOf(new TheOrders());
        // The order's own rank is under the order it chose, which the answer never turned on.
        orders.getFirst().at(ORDERS.element().then("rank"));
        // A line of it is under the line the asking walk chose, which reading it never asked.
        assertThrows(IllegalStateException.class, () -> orders.getFirst().at(SKU));
    }

    private static StandingAtAPoint.OneReadingOfARow reading(StandingAtAPoint.RowWalk walk,
                                                             int order, int line) {
        return new StandingAtAPoint.OneReadingOfARow(walk, Map.of(ORDERS, order, LINES, line));
    }

    private static StandingAtAPoint.RowWalk walk() {
        return new StandingAtAPoint.RowWalk(
                new BehaviorInputs(List.of("orders"),
                        List.of(new Type.ListOf(Type.ref(sym("Order")))),
                        RuleReadings.ofSource(MODEL), POLICY),
                new ObservedInputs(List.of(new ObservedValue.Sequence(List.of(
                        order(1, "a", "b"), order(2, "c")))),
                        new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()));
    }

    private static ObservedValue order(long rank, String... skus) {
        return new ObservedValue.Constructed(sym("Order"), Map.of(
                "lines", new ObservedValue.Sequence(Arrays.stream(skus)
                        .<ObservedValue>map(sku -> new ObservedValue.Constructed(sym("Line"),
                                Map.of("sku", new ObservedValue.Text(sku))))
                        .toList()),
                "rank", new ObservedValue.Integer(rank)));
    }

    private static TypeSymbol sym(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }
}
