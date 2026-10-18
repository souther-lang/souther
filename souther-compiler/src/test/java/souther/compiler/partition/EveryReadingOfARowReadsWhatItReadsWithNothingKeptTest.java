package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.Extreme;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;
import souther.compiler.values.AsACompilationAllows;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every reading of a row reads what it reads with nothing kept between the readings: what one
 * reading of an occurrence read for the others is what each would have read for itself.
 *
 * <p>Held over rows where the occurrences are not alike — orders whose lines are the same values,
 * orders of different lengths so that some readings choose a line their order does not have, an
 * order with no lines, values that were not read — and over a quantity reading a number of an
 * element among its neighbours, at two containers chosen apart, beside a run over every value.
 */
class EveryReadingOfARowReadsWhatItReadsWithNothingKeptTest {

    private static final String MODEL = """
            module g

            data Line = { sku: String, qty: Int }

            data Order = { lines: List<Line>, tags: List<String> }

            behavior decide : (orders: List<Order>) -> Int
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());

    private static final TermPath ORDERS = TermPath.of("orders");

    private static final TermPath LINES = ORDERS.element().then("lines");

    private static final TermPath TAGS = ORDERS.element().then("tags");

    private static final Carrier WHOLE = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);

    private static final ObservedValue TRUNCATED =
            new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure());

    @Test
    void ordersOfAlikeLinesAreEachTheirOwnOccurrence() {
        everyReadingReadsAlike(order(List.of(line("x", 9), line("x", 2)), List.of("a", "a")),
                order(List.of(line("x", 2)), List.of("a")));
    }

    @Test
    void aReadingOfALineItsOrderDoesNotHaveReadsAsItDoesAlone() {
        everyReadingReadsAlike(
                order(List.of(line("x", 1), line("y", 2), line("x", 3), line("z", 4)),
                        List.of("a", "b", "a")),
                order(List.of(line("y", 5)), List.of()),
                order(List.of(), List.of("c")));
    }

    @Test
    void whatWasNotReadStopsEachReadingAsItDoesAlone() {
        everyReadingReadsAlike(
                order(List.of(line(new ObservedValue.Text("x"), TRUNCATED), line("x", 3),
                        line(TRUNCATED, new ObservedValue.Integer(1)), line("y", 2)),
                        List.of("a")),
                order(List.of(line("y", 7)), List.of("b", "b")));
    }

    /**
     * Reads every reading of a row holding {@code orders} at the quantity, as the measurement
     * reads them and through a walk that keeps nothing, and holds them equal term by term.
     */
    private static void everyReadingReadsAlike(ObservedValue... orders) {
        NumericTerm.Multiplicity often = NumericTerm.Multiplicity.of(LINES,
                LINES.element().then("sku"));
        NumericTerm.ExtremeOfItsKey least = NumericTerm.ExtremeOfItsKey.of(LINES,
                LINES.element().then("sku"), LINES.element().then("qty"), Extreme.LEAST);
        NumericTerm.Multiplicity tagged = NumericTerm.Multiplicity.of(TAGS, TAGS.element());
        RuleReadingSource rules = RuleReadings.ofSource(MODEL);
        Symbols symbols = rules.symbols();
        NumericTerm.TakenOver total = NumericTerm.TakenOver.of(
                ValueName.Stdlib.operation("List", "sum"),
                new RunSource.FlattenedOccurrences(LINES.element().then("qty")), Type.Prim.INT,
                ScopedDeclarations.wrapsOf(symbols), symbols);
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(often, TermOrdersFixtures.orders(often, Carrier.TEXT, WHOLE));
        on.put(least, TermOrdersFixtures.computed(least, WHOLE, WHOLE,
                Map.of(least.keyField(), Carrier.TEXT)));
        on.put(tagged, TermOrdersFixtures.orders(tagged, Carrier.TEXT, WHOLE));
        on.put(total, TermOrdersFixtures.itself(total, WHOLE));
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        on.keySet().forEach(term -> coefs.put(term, ExactRatio.ONE));
        LinearQuantity quantity = new BorderQuantity.OverAForm("decide",
                new LinearForm<>(ExactRatio.ZERO, coefs), on);
        BehaviorInputs where = new BehaviorInputs(List.of("orders"),
                List.of(new Type.ListOf(named("Order"))), rules, POLICY);
        StandingAtAPoint.Readings readings = StandingAtAPoint.readings(where,
                new ObservedInputs(List.of(new ObservedValue.Sequence(List.of(orders))),
                        new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()),
                quantity);
        assertTrue(readings.tried().size() > 1, "a row with a reading per element");
        for (BorderQuantity.Observation reading : readings.tried()) {
            QuantityReading kept = quantity.read(reading);
            QuantityReading alone = quantity.read(new KeepingNothing(reading));
            for (TermOrders each : on.values()) {
                assertEquals(alone.of(each), kept.of(each), () -> each + " at " + reading);
            }
        }
    }

    /** A reading of a row that keeps nothing it read for another, and is otherwise the reading. */
    private record KeepingNothing(BorderQuantity.Observation within)
            implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            return within.at(path);
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            return within.everyValueAt(path);
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
            return within.eachElementOf(container);
        }

        @Override
        public BorderQuantity.Lastness lastToHold(TermPath container, TermPath position) {
            return within.lastToHold(container, position);
        }

        @Override
        public WalkResult<BorderQuantity.Among> among(TermPath container) {
            return within.among(container);
        }

        @Override
        public WalkResult<List<BorderQuantity.AnElement>> elementsOf(TermPath container) {
            return within.elementsOf(container);
        }

        @Override
        public boolean choseAnElement() {
            return within.choseAnElement();
        }
    }

    private static ObservedValue order(List<ObservedValue> lines, List<String> tags) {
        List<ObservedValue> written = new ArrayList<>();
        tags.forEach(tag -> written.add(new ObservedValue.Text(tag)));
        return new ObservedValue.Constructed(sym("Order"), Map.of(
                "lines", new ObservedValue.Sequence(lines),
                "tags", new ObservedValue.Sequence(written)));
    }

    private static ObservedValue line(String sku, long qty) {
        return line(new ObservedValue.Text(sku), new ObservedValue.Integer(qty));
    }

    private static ObservedValue line(ObservedValue sku, ObservedValue qty) {
        return new ObservedValue.Constructed(sym("Line"), Map.of("sku", sku, "qty", qty));
    }

    private static Type named(String data) {
        return Type.ref(sym(data));
    }

    private static TypeSymbol sym(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }
}
