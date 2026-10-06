package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value the body asks the truth of asks of a row what the comparison it means asks.
 *
 * <p>Held against the comparison written out and not against a spelling of the demand. What an
 * emptiness check means is a size against nought, and the claim is that a row composed past one is
 * held to exactly what a row past the other is — so the two are asked and their answers compared,
 * and a reading that came to a different form for either would show here as the two parting.
 */
class ATruthAsksOfARowWhatTheComparisonItMeansAsksTest {

    private static final String MODEL = """
            module example.truths

            data Line = { price: Int }
            data Order = { lines: List<Line>, floor: Int }

            behavior someDear : (o: Order) -> Bool
            let someDear (o) = List.any(l -> l.price >= 10, o.lines)

            behavior allCheap : (o: Order) -> Bool
            let allCheap (o) = List.all(l -> l.price < 10, o.lines)

            behavior allAboveTheFloor : (o: Order) -> Bool
            let allAboveTheFloor (o) = List.all(l -> o.floor > 3, o.lines)

            behavior emptyAsked : (o: Order) -> Bool
            let emptyAsked (o) = List.isEmpty(o.lines)

            behavior emptyCompared : (o: Order) -> Bool
            let emptyCompared (o) = List.length(o.lines) == 0

            behavior emptyDenied : (o: Order) -> Bool
            let emptyDenied (o) = Bool.not(List.isEmpty(o.lines))

            behavior memberAsked : (o: Order, l: Line) -> Bool
            let memberAsked (o, l) = List.contains(l, o.lines)
            """;

    /** Either way it comes out, an emptiness check asks what the size against nought asks. */
    @Test
    void anEmptinessCheckAsksWhatItsSizeAgainstNoughtAsks() {
        for (boolean holding : List.of(true, false)) {
            assertEquals(demandOf("emptyCompared", holding), demandOf("emptyAsked", holding),
                    "List.isEmpty coming out " + holding + " asks what the size against nought"
                            + " coming out " + holding + " asks");
        }
        assertNotEquals(demandOf("emptyAsked", true), demandOf("emptyAsked", false),
                "and the two ways it comes out ask different things of a row");
    }

    /** A denial is the comparison under it the other way round. */
    @Test
    void aDeniedEmptinessCheckAsksWhatTheComparisonFailingAsks() {
        for (boolean holding : List.of(true, false)) {
            assertEquals(demandOf("emptyCompared", !holding), demandOf("emptyDenied", holding),
                    "Bool.not(List.isEmpty(...)) coming out " + holding + " is the size against"
                            + " nought coming out " + !holding);
        }
    }

    /**
     * A truth that means no comparison is declined as one nothing here has words for, and is not
     * read as something it does not say.
     */
    @Test
    void aTruthThatMeansNoComparisonIsDeclined() {
        for (boolean holding : List.of(true, false)) {
            OnTheWay.Declined declined = assertInstanceOf(OnTheWay.Declined.class,
                    only("memberAsked", holding));
            assertEquals(new OnTheWay.Why.NoWordsForTheShape(), declined.why());
        }
    }

    /**
     * Some element meeting a predicate and every element failing it are the two ways one
     * quantifier comes out, and the other quantifier over the denied predicate asks the same.
     */
    @Test
    void aQuantifierAsksWhatTheOtherAsksOfTheDeniedPredicate() {
        for (boolean holding : List.of(true, false)) {
            assertEquals(demandsOf("allCheap", !holding), demandsOf("someDear", holding),
                    "List.any(p) coming out " + holding + " asks what List.all(not p) coming out "
                            + !holding + " asks");
        }
    }

    /**
     * Every element meeting it is a relation of the elements alone, and some element meeting it
     * is the container holding one and an element that meets it — which no region is narrowed by.
     */
    @Test
    void everyElementIsARelationAndSomeElementIsNot() {
        List<RowDemand> every = demandsOf("someDear", false);
        assertEquals(1, every.size(), () -> "one relation of the elements: " + every);
        assertInstanceOf(RowDemand.Relational.class, every.getFirst());

        List<RowDemand> some = demandsOf("someDear", true);
        assertEquals(1, some.size(), () -> "an element, with the container holding it: " + some);
        RowDemand.Exists element = assertInstanceOf(RowDemand.Exists.class, some.getFirst(),
                "an element that meets the predicate");
        assertTrue(element.holdingOne().isPresent(), "and the container holding at least one");
        assertNotEquals(every.getFirst(), element.ofAnElement().getFirst(),
                "what some element meets is the predicate, and what every element meets when it"
                        + " fails is its denial");
    }

    /** What every element has to meet is not narrowed on where it is about more than the element:
     *  an empty list meets it whatever the rest says. */
    @Test
    void everyElementMeetingWhatIsNotAboutTheElementIsDeclined() {
        OnTheWay.Declined declined = assertInstanceOf(OnTheWay.Declined.class,
                only("allAboveTheFloor", true));
        assertEquals(new OnTheWay.Why.MoreThanEachElement(), declined.why());
    }

    /** Everything the body's single condition asks of a row, coming out {@code holding}. */
    private static List<RowDemand> demandsOf(String behavior, boolean holding) {
        return readingOf(behavior).stating(holding).stream()
                .map(each -> (RowDemand) assertInstanceOf(OnTheWay.TakenIn.class, each,
                        () -> behavior + " asks something of a row: " + each).demand())
                .toList();
    }

    /** What the body's single condition asks of a row, coming out {@code holding}. */
    private static RowDemand demandOf(String behavior, boolean holding) {
        return assertInstanceOf(OnTheWay.TakenIn.class, only(behavior, holding),
                () -> behavior + " coming out " + holding + " asks something of a row").demand();
    }

    private static OnTheWay only(String behavior, boolean holding) {
        List<OnTheWay> stated = readingOf(behavior).stating(holding);
        assertEquals(1, stated.size(), () -> behavior + " is one condition: " + stated);
        return stated.getFirst();
    }

    /** One behavior of the model, read once. */
    private record Read(Core body, InputReading read, InputReads reads, RuleReadingSource rules,
                        String module, String behavior) {

        List<OnTheWay> stating(boolean holding) {
            return ReachingCuts.stating(Condition.of(body, reads, rules.symbols(),
                    rules.newtypes(), new ConditionNumbering(module, behavior)), read, holding);
        }
    }

    private static final Map<String, Read> READINGS = new ConcurrentHashMap<>();

    private static Read readingOf(String behavior) {
        return READINGS.computeIfAbsent(behavior, name -> {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
            compilation.answerEverything();
            String module = compilation.modules().getFirst();
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            assertNotNull(checked, "the model under test compiles");
            // The tree the analysis reads, where the language's operations still stand as written
            // — which is the one a condition on the way is read off.
            AnalysisBody analysis = checked.analysisBodies().get(name);
            assertNotNull(analysis, () -> "the model under test writes " + name);
            RuleReadingSource rules = RuleReadings.of(compilation, module);
            InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(name);
            InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                    ElementBindings.of(analysis, rules.newtypes()));
            return new Read(analysis.core(), inputs.reading(rules), reads, rules, module, name);
        });
    }
}
