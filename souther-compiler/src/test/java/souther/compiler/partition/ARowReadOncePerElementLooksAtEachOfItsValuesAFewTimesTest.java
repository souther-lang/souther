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
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
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
 * A row has a reading per element of its container, and each reading asks a number of its
 * element read off the others and whether it is the last to hold its key. Every value the row
 * wrote is still looked at a few times in all, however long the container: what one reading of an
 * occurrence read is what the others are told, and a value under a reading's elements is looked
 * up and not looked for.
 *
 * <p>Counted in values looked at, and not in time, so a reading that looked at every element
 * again for each element is the square of the container whatever the machine.
 */
class ARowReadOncePerElementLooksAtEachOfItsValuesAFewTimesTest {

    private static final String MODEL = """
            module g

            data Row = { sku: String, qty: Int }

            behavior decide : (rows: List<Row>) -> Int
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());

    private static final TermPath ROWS = TermPath.of("rows");

    private static final TermPath SKU = ROWS.element().then("sku");

    private static final Carrier WHOLE = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);

    /** How many times each value may be looked at: once for each way it is found. */
    private static final int A_FEW = 16;

    @Test
    void eachValueIsLookedAtAFewTimesHoweverLongTheContainer() {
        long readFirst = -1;
        for (int length : List.of(8, 32, 128, 256)) {
            StandingAtAPoint.RowWalk walk = readEveryReading(length);
            assertTrue(walk.occurrencesLookedAt() <= (long) A_FEW * length,
                    () -> walk.occurrencesLookedAt() + " values looked at over " + length
                            + " elements");
            if (readFirst < 0) {
                readFirst = walk.answersRead();
            }
            assertEquals(readFirst, walk.answersRead(),
                    "what an occurrence came to is read once however many readings ask it");
        }
    }

    private static final String NESTED = """
            module g

            data Row = { sku: String, qty: Int }

            data Order = { rows: List<Row> }

            behavior decide : (orders: List<Order>) -> Int
            """;

    private static final TermPath ORDERS = TermPath.of("orders");

    private static final TermPath LINES = ORDERS.element().then("rows");

    /**
     * The same of the rows of an order beside an order that was not read, which stands at every
     * path below it under every row: the values at one path are not all reached through the same
     * containers, and each is still looked up once.
     */
    @Test
    void eachValueIsLookedAtAFewTimesBesideAnOrderThatWasNotRead() {
        for (int length : List.of(8, 32, 127)) {
            NumericTerm.Multiplicity often = NumericTerm.Multiplicity.of(LINES,
                    LINES.element().then("sku"));
            NumericTerm.ExtremeOfItsKey least = NumericTerm.ExtremeOfItsKey.of(LINES,
                    LINES.element().then("sku"), LINES.element().then("qty"), Extreme.LEAST);
            LinearQuantity quantity = form(Map.of(
                    often, TermOrdersFixtures.orders(often, Carrier.TEXT, WHOLE),
                    least, TermOrdersFixtures.computed(least, WHOLE, WHOLE,
                            Map.of(least.keyField(), Carrier.TEXT))));
            List<ObservedValue> rows = new ArrayList<>();
            for (int each = 0; each < length; each++) {
                rows.add(new ObservedValue.Constructed(sym("Row"), Map.of(
                        "sku", new ObservedValue.Text("sku" + each % 5),
                        "qty", new ObservedValue.Integer(each))));
            }
            BehaviorInputs where = new BehaviorInputs(List.of("orders"),
                    List.of(new Type.ListOf(Type.ref(sym("Order")))),
                    RuleReadings.ofSource(NESTED), POLICY);
            StandingAtAPoint.Readings readings = StandingAtAPoint.readings(where,
                    new ObservedInputs(List.of(new ObservedValue.Sequence(List.of(
                            new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()),
                            new ObservedValue.Constructed(sym("Order"),
                                    Map.of("rows", new ObservedValue.Sequence(rows)))))),
                            new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()),
                    quantity);
            assertEquals(2 * length, readings.tried().size(), "a reading per order and row");
            for (BorderQuantity.Observation reading : readings.tried()) {
                quantity.read(reading);
                reading.lastToHold(LINES, LINES.element().then("sku"));
            }
            StandingAtAPoint.RowWalk walk =
                    ((StandingAtAPoint.WalkOfARow) readings.tried().getFirst()).walk();
            assertTrue(walk.occurrencesLookedAt() <= (long) A_FEW * 2 * length,
                    () -> walk.occurrencesLookedAt() + " values looked at over " + length
                            + " rows");
        }
    }

    private static final String BESIDE = """
            module g

            data Row = { sku: String, qty: Int }

            behavior decide : (rows: List<Row>, tags: List<String>, scores: List<Int>) -> Int
            """;

    private static final TermPath TAGS = TermPath.of("tags");

    private static final TermPath SCORES = TermPath.of("scores");

    /**
     * What is read of the elements of one container together is read once however many elements
     * of another container the readings choose between: the tags are the same tags under every
     * row, so how often a tag occurs and how many tags are there are asked of them once.
     */
    @Test
    void whatOneContainerComesToIsNotReadAgainForEachElementOfAnother() {
        long readFirst = -1;
        for (int length : List.of(4, 8, 16)) {
            NumericTerm.Multiplicity tagged = NumericTerm.Multiplicity.of(TAGS, TAGS.element());
            NumericTerm.ValueOf qty = new NumericTerm.ValueOf(ROWS.element().then("qty"));
            RuleReadingSource rules = RuleReadings.ofSource(BESIDE);
            Symbols symbols = rules.symbols();
            ElementProjection itself = new ElementProjection(List.of());
            NumericTerm.TakenOver scored = NumericTerm.TakenOver.of(
                    ValueName.Stdlib.operation("List", "sum"),
                    new RunSource.ComputedOccurrences(SCORES.element(), new ElementValue.Affine(
                            new LinearForm<>(ExactRatio.ZERO, Map.of(itself, ExactRatio.ONE))),
                            Type.Prim.INT, null),
                    Type.Prim.INT, ScopedDeclarations.wrapsOf(symbols), symbols);
            LinearQuantity quantity = form(Map.of(
                    tagged, TermOrdersFixtures.orders(tagged, Carrier.TEXT, WHOLE),
                    qty, TermOrdersFixtures.itself(qty, WHOLE),
                    scored, TermOrdersFixtures.computed(scored, WHOLE, WHOLE,
                            Map.of(itself, WHOLE))));
            Proposition aTag =
                    new Proposition.Present(new DecisionSubject.AnInput(TAGS.element()), true);
            AStatementAtARow someTag = AStatementAtARow.of(new Proposition.Some(
                    new DecisionSubject.AnInput(TAGS), aTag, true), "decide", null);
            MetOnARow stoppedAtATag = MetOnARow.of(new ElementsMetOn(
                    List.of(new ElementsMetOn.Level.StopsAt(TAGS, aTag)),
                    new Proposition.Always(true)), "decide", null);
            List<ObservedValue> rows = new ArrayList<>();
            List<ObservedValue> tags = new ArrayList<>();
            List<ObservedValue> scores = new ArrayList<>();
            for (int each = 0; each < length; each++) {
                rows.add(new ObservedValue.Constructed(sym("Row"), Map.of(
                        "sku", new ObservedValue.Text("sku"),
                        "qty", new ObservedValue.Integer(each))));
                tags.add(new ObservedValue.Text("tag" + each % 3));
                scores.add(new ObservedValue.Integer(each));
            }
            BehaviorInputs where = new BehaviorInputs(List.of("rows", "tags", "scores"),
                    List.of(new Type.ListOf(Type.ref(sym("Row"))),
                            new Type.ListOf(Type.Prim.STRING), new Type.ListOf(Type.Prim.INT)),
                    rules, POLICY);
            StandingAtAPoint.Readings readings = StandingAtAPoint.readings(where,
                    new ObservedInputs(List.of(new ObservedValue.Sequence(rows),
                            new ObservedValue.Sequence(tags), new ObservedValue.Sequence(scores)),
                            new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()),
                    quantity);
            assertEquals(length * length, readings.tried().size(), "a reading per row and tag");
            for (BorderQuantity.Observation reading : readings.tried()) {
                quantity.read(reading);
                someTag.at(reading);
                stoppedAtATag.at(reading);
            }
            StandingAtAPoint.RowWalk walk =
                    ((StandingAtAPoint.WalkOfARow) readings.tried().getFirst()).walk();
            if (readFirst < 0) {
                readFirst = walk.answersRead();
            }
            assertEquals(readFirst, walk.answersRead(), () -> "over " + length + " rows");
        }
    }

    /** A sum of each of {@code on}'s terms, each read on its own orders. */
    private static LinearQuantity form(Map<NumericTerm, TermOrders> on) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        on.keySet().forEach(term -> coefs.put(term, ExactRatio.ONE));
        return new BorderQuantity.OverAForm("decide", new LinearForm<>(ExactRatio.ZERO, coefs),
                on);
    }

    /** A row of {@code length} elements, every reading of it asked its numbers and its lastness. */
    private static StandingAtAPoint.RowWalk readEveryReading(int length) {
        NumericTerm.Multiplicity often = NumericTerm.Multiplicity.of(ROWS, SKU);
        NumericTerm.ExtremeOfItsKey least = NumericTerm.ExtremeOfItsKey.of(ROWS, SKU,
                ROWS.element().then("qty"), Extreme.LEAST);
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(often, TermOrdersFixtures.orders(often, Carrier.TEXT, WHOLE));
        on.put(least, TermOrdersFixtures.computed(least, WHOLE, WHOLE,
                Map.of(least.keyField(), Carrier.TEXT)));
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        on.keySet().forEach(term -> coefs.put(term, ExactRatio.ONE));
        LinearQuantity quantity = new BorderQuantity.OverAForm("decide",
                new LinearForm<>(ExactRatio.ZERO, coefs), on);
        RuleReadingSource rules = RuleReadings.ofSource(MODEL);
        BehaviorInputs where = new BehaviorInputs(List.of("rows"),
                List.of(new Type.ListOf(Type.ref(sym("Row")))), rules, POLICY);
        List<ObservedValue> rows = new ArrayList<>();
        for (int each = 0; each < length; each++) {
            rows.add(new ObservedValue.Constructed(sym("Row"), Map.of(
                    "sku", new ObservedValue.Text("sku" + each % 5),
                    "qty", new ObservedValue.Integer(each))));
        }
        StandingAtAPoint.Readings readings = StandingAtAPoint.readings(where,
                new ObservedInputs(List.of(new ObservedValue.Sequence(rows)),
                        new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()),
                quantity);
        assertEquals(length, readings.tried().size(), "a reading per element");
        for (BorderQuantity.Observation reading : readings.tried()) {
            quantity.read(reading);
            reading.lastToHold(ROWS, SKU);
        }
        return ((StandingAtAPoint.WalkOfARow) readings.tried().getFirst()).walk();
    }

    private static TypeSymbol sym(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }
}
