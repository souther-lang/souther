package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeView;
import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.IntFunction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The values offered for the elements of a set and the keys of a map differ by a step of the order
 * the element is compared on: a date by a day, a time of day and a date-time by a second, a moment
 * by a nanosecond — as a whole number differs by one.
 *
 * <p>Inside what the element's own rules leave, and away from the one end they give.
 */
class AnElementIsSteppedOnTheOrderItsValuesAreComparedOnTest {

    private static final String TYPES = """
            data October = Date
              invariant value >= Date("2026-10-01") && value <= Date("2026-10-31")
            data Until = Date
              invariant value <= Date("2026-10-12")
            data AtMost = Int
              invariant value <= 0
            data Late = Time
              invariant value >= Time("23:59:58")
            data Level = Low | Mid | High
            """;

    private static final String MODEL = """
            module p
            %s
            behavior f : (s: %s) -> Int
            let f (s) = if %s == %d then 1 else 2
            """;

    /**
     * A set or a map of three of them is built, and every point of the line owed a row — at it,
     * beside it, and in the regions either side — has one the search wrote.
     */
    @Test
    void aCollectionOfTemporalValuesIsBuiltPastOneElement() {
        record Case(String type, String size) {}
        for (Case each : List.of(
                new Case("Set<Date>", "Set.size(s)"),
                new Case("Set<Time>", "Set.size(s)"),
                new Case("Set<DateTime>", "Set.size(s)"),
                new Case("Set<Instant>", "Set.size(s)"),
                new Case("Set<October>", "Set.size(s)"),
                new Case("Set<Until>", "Set.size(s)"),
                new Case("Map<Date, Bool>", "Map.size(s)"))) {
            BorderAssessment line = lineOf(MODEL.formatted(TYPES, each.type(), each.size(), 3));

            for (DomainPoint point : List.of(new DomainPoint.AtTheLine(),
                    new DomainPoint.BesideTheLine(Towards.BELOW),
                    new DomainPoint.BesideTheLine(Towards.ABOVE),
                    new DomainPoint.InTheRegion(Towards.BELOW),
                    new DomainPoint.InTheRegion(Towards.ABOVE))) {
                assertTrue(line.items().get(point) instanceof ItemAssessment.Owed owed
                        && owed.searches().each().stream()
                                .anyMatch(ItemAssessment.Attempt.Certified.class::isInstance),
                        () -> each.type() + " " + point + " " + line.items().get(point));
            }
        }
    }

    /** Worked out by hand: one step of each order from where an unbounded range is entered. */
    @Test
    void eachOrderStepsByItsOwnUnit() {
        assertEquals(List.of("Date(\"1970-01-01\")", "Date(\"1970-01-02\")",
                        "Date(\"1970-01-03\")"),
                stepped(Type.DATE, 3));
        assertEquals(List.of("Time(\"00:00:00\")", "Time(\"00:00:01\")"),
                stepped(Type.TIME, 2));
        assertEquals(List.of("DateTime(\"1970-01-01T00:00:00\")",
                        "DateTime(\"1970-01-01T00:00:01\")"),
                stepped(Type.DATETIME, 2));
        assertEquals(List.of("Instant(\"1970-01-01T00:00:00Z\")",
                        "Instant(\"1970-01-01T00:00:00.000000001Z\")"),
                stepped(Type.INSTANT, 2));
    }

    /** From the lower end of a range bounded at both, under the name the element wears. */
    @Test
    void aBoundedElementIsSteppedFromItsLowerEndUnderItsName() {
        assertEquals(List.of("October(Date(\"2026-10-01\"))", "October(Date(\"2026-10-02\"))",
                        "October(Date(\"2026-10-03\"))"),
                stepped(declared("October"), 3));
    }

    /** Down from the end of a range bounded only above, which a step up would leave. */
    @Test
    void anElementBoundedOnlyAboveIsSteppedDownFromThatEnd() {
        assertEquals(List.of("AtMost(0)", "AtMost(-1)", "AtMost(-2)"),
                stepped(declared("AtMost"), 3));
        assertEquals(List.of("Until(Date(\"2026-10-12\"))", "Until(Date(\"2026-10-11\"))",
                        "Until(Date(\"2026-10-10\"))"),
                stepped(declared("Until"), 3));
    }

    /** Past the last second of the day there is no time, so a step there is no value. */
    @Test
    void noStepIsTakenPastTheLastTimeOfTheDay() {
        assertEquals(List.of("Late(Time(\"23:59:58\"))", "Late(Time(\"23:59:59\"))"),
                stepped(declared("Late"), 3));
    }

    private static final String NOT_THE_DAY = """
            module p
            data NotTheDay = Date
              invariant value /= Date("1970-01-01")
            behavior h : (d: NotTheDay) -> Int
            let h (d) = 1
            """;

    /**
     * A position whose rule refuses the one value it is ordinarily offered is offered the one beside
     * it on the same order, a date as much as a whole number: the day after the day where an
     * unbounded range of dates is entered.
     */
    @Test
    void aDateItsRuleRefusesIsDisplacedAlongItsOrder() {
        Compilation compilation = Compilation.ofSource(NOT_THE_DAY, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Adequacy.Filling filling = Adequacy.generatedOf(compilation.db(), "p").get("h");
        assertNotNull(filling, "the behavior under test is generated for");
        List<String> written = filling.rules().byRule().values().stream()
                .map(row -> row.inputs().get(0).text())
                .toList();

        assertEquals(List.of("NotTheDay(Date(\"1970-01-02\"))"), written);
    }

    /**
     * Only a value of its own that counts is stepped. An enumeration's cases are what the position
     * divides into, and a string is ordered with no count under it.
     */
    @Test
    void neitherACaseNorAStringIsStepped() {
        assertEquals(List.of(), stepped(declared("Level"), 3));
        assertEquals(List.of(), stepped(Type.STRING, 3));
    }

    /** Between two decimals there is no next one, and none is made up. */
    @Test
    void aDecimalIsNotStepped() {
        assertEquals(1, stepped(Type.DECIMAL, 3).size());
    }

    /** What stepping alone offers: the values {@link Partitions#valuesInside} names, in order, up
     *  to the first it has none for. */
    private static List<String> stepped(Type type, int many) {
        RuleReadingContext reading = reading();
        TypeView view = TypeView.of(type, reading.source().inners(), reading.source().symbols(),
                reading.source().kinds(), reading.source().sums());
        IntFunction<FixtureTemplate> inside = Partitions.valuesInside(view, reading);
        List<String> out = new ArrayList<>();
        for (int i = 0; i < many; i++) {
            FixtureTemplate each = inside.apply(i);
            if (each == null) {
                break;
            }
            out.add(each.text());
        }
        return out;
    }

    private static RuleReadingContext reading() {
        Compilation compilation = Compilation.ofSource(
                MODEL.formatted(TYPES, "Set<Date>", "Set.size(s)", 3), "Main");
        compilation.answerEverything();
        return RuleReadingContext.unshared(RuleReadings.of(compilation, "p"),
                ReadAs.THE_COMPILATION_DOES);
    }

    private static Type declared(String name) {
        return Type.ref(TypeSymbols.declared(new TypeKey("p", name)));
    }

    private static BorderAssessment lineOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "p");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        for (BorderAssessment border : lines) {
            if (border.value().equals("3")) {
                return border;
            }
        }
        throw new AssertionError("no line at 3 among " + lines);
    }
}
