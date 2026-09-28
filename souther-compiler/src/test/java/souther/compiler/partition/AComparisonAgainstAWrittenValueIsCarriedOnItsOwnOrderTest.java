package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison whose written value the arithmetic cannot carry is carried on the order instead.
 *
 * <p>What divides the two vocabularies is whether the reading of the form reached the end, and not
 * which operator was written or which type the values have. A string against another string is a
 * distance between two positions and the arithmetic carries it; a string against a written string
 * has no number for the written one, and what the rule says is where on the order the position
 * lies. Read as one vocabulary, the second was recorded as a condition nothing could state, and a
 * search below it composed against rules wider than the rows that reach it.
 *
 * <p>Every operator is here for both, because the operator is what a reader would expect to divide
 * them and it does not. And a comparison whose positions cancel is here beside them: that one is
 * read to the end and constrains nothing, which is neither of the two and is not a shortfall.
 */
class AComparisonAgainstAWrittenValueIsCarriedOnItsOwnOrderTest {

    private static final String MODEL = """
            module example.written

            data Pair = { a: String, b: String, m: Int, n: Int }

            behavior textBelowAWrittenValue : (p: Pair) -> Bool
            let textBelowAWrittenValue (p) = p.a < "t"

            behavior textApartFromAWrittenValue : (p: Pair) -> Bool
            let textApartFromAWrittenValue (p) = p.a /= "t"

            behavior textAtAWrittenValue : (p: Pair) -> Bool
            let textAtAWrittenValue (p) = p.a == "t"

            behavior textAboveAWrittenValue : (p: Pair) -> Bool
            let textAboveAWrittenValue (p) = p.a >= "t"

            behavior textBelowAnotherPosition : (p: Pair) -> Bool
            let textBelowAnotherPosition (p) = p.a < p.b

            behavior textApartFromAnotherPosition : (p: Pair) -> Bool
            let textApartFromAnotherPosition (p) = p.a /= p.b

            behavior countBelowAWrittenValue : (p: Pair) -> Bool
            let countBelowAWrittenValue (p) = p.m < 1

            behavior countApartFromAWrittenValue : (p: Pair) -> Bool
            let countApartFromAWrittenValue (p) = p.m /= 1

            behavior positionsCancel : (p: Pair) -> Bool
            let positionsCancel (p) = p.m - p.m > 0
            """;

    /**
     * A written value on an order that counts nothing is a bound on that order.
     *
     * <p>Both ways round, because what the path met is what is carried: an arm reached by the
     * condition failing has what holds exactly where the comparison does not, and a bound recorded
     * facing the way the author wrote it would narrow the region to the side no row on that arm is
     * on.
     */
    @Test
    void aWrittenValueOnAnOrderThatCountsNothingIsABoundOnIt() {
        assertEquals(Map.of(true, "p.a LT t", false, "p.a GE t"),
                bothWays("textBelowAWrittenValue"));
        assertEquals("p.a EQ t", said(taken("textApartFromAWrittenValue", false)));
        assertEquals("p.a EQ t", said(taken("textAtAWrittenValue", true)));
    }

    /**
     * A relation that leaves a hole is carried as one, and not as a bound.
     *
     * <p>Two shapes because a reader does two things with them. An end moves where a chooser looks;
     * a hole leaves the run where it was and takes one value out of it. Carried as a bound, the
     * value the rule refuses would become an end and one whole side of the order would go with it.
     *
     * <p>Both spellings of it, since which relation reaches this is what the path met and not what
     * the author wrote: {@code /= } holding and {@code ==} denied are one relation.
     */
    @Test
    void aRelationThatLeavesAHoleIsCarriedAsAHole() {
        for (Map.Entry<String, Boolean> each : Map.of(
                "textApartFromAWrittenValue", true, "textAtAWrittenValue", false).entrySet()) {
            TakenConstraint.AwayFrom away = assertInstanceOf(TakenConstraint.AwayFrom.class,
                    taken(each.getKey(), each.getValue()),
                    each.getKey() + " comes out " + each.getValue() + " as a hole in the order");
            assertEquals("t", away.at().spelled());
        }
    }

    /**
     * And the region it reaches refuses a row standing at the place the rule holds apart.
     *
     * <p>The other end of the same contract. A hole a region took in and then had no answer about
     * would be a condition recorded as narrowing a search that goes on offering the one value it
     * refuses — which is what a reader of a condition taken in is entitled to assume did not
     * happen.
     */
    @Test
    void aRowStandingInTheHoleIsRefused() {
        TakenConstraint.AwayFrom away = assertInstanceOf(TakenConstraint.AwayFrom.class,
                taken("textApartFromAWrittenValue", true));
        SearchRegion narrowed = new WayToTheBorder(stating("textApartFromAWrittenValue", true))
                .narrowing(regionOf("textApartFromAWrittenValue"));

        assertInstanceOf(EmptyInput.WhereARuleHoldsThePositionApart.class,
                narrowed.given(away.term(), away.at()).emptiness().orElse(null),
                "a row standing where the rule holds the position away cannot be written");
        assertTrue(narrowed.given(away.term(), souther.compiler.numeric.Text.of("autumn"))
                        .emptiness().isEmpty(),
                "and the rest of the order is left where it was, which is what a hole is");
    }

    /**
     * And what is taken in narrows the region a row is looked for in.
     *
     * <p>Against the region this compiler builds and not a stand-in that records what it was told.
     * A reading that produced the right constraint and handed it to an implementation with nothing
     * to do with it would pass every question asked of the reading alone, and the search below the
     * guard would go on running over the rows the guard excludes.
     */
    @Test
    void whatIsTakenInNarrowsWhereARowIsLookedFor() {
        assertEquals("[t, null]", runsAt("textAboveAWrittenValue"),
                "a bound above a written value moves the end the run starts at");
        assertEquals("[t, t]", runsAt("textAtAWrittenValue"),
                "and an equality leaves the one place the rule names");
    }

    /**
     * And two positions of that order are the arithmetic's, whichever operator holds them apart.
     *
     * <p>The negative control the claim above needs. What the arithmetic cannot carry is the written
     * value and not the carrier: a distance between two positions is a form over both of them
     * whether or not either counts to a number, so a reading that sent every string comparison to
     * the order would take these away from the vocabulary that already carried them.
     */
    @Test
    void twoPositionsOfThatOrderStayWithTheArithmetic() {
        for (String behavior : List.of("textBelowAnotherPosition", "textApartFromAnotherPosition")) {
            for (boolean holding : List.of(true, false)) {
                TakenConstraint.Affine carried = assertInstanceOf(TakenConstraint.Affine.class,
                        taken(behavior, holding),
                        behavior + " is a distance between two positions, which the arithmetic"
                                + " carries");
                assertEquals(2, carried.form().coefs().size(),
                        "over both of the positions it holds apart");
            }
        }
    }

    /** And so is a written value the carrier counts, which is what keeps the split at the reading
     *  of the form rather than at the type of the values. */
    @Test
    void aWrittenValueOnACountedOrderStaysWithTheArithmetic() {
        for (String behavior : List.of("countBelowAWrittenValue", "countApartFromAWrittenValue")) {
            assertInstanceOf(TakenConstraint.Affine.class, taken(behavior, true),
                    behavior + " names a number, and a number is what the form is over");
        }
    }

    /**
     * A comparison read to the end whose positions cancel says so, and is not the other word.
     *
     * <p>The two used to arrive as one absence. A reading that stopped is this compiler falling
     * short of a rule the model states; a quantity that cancelled is a rule that constrains no
     * position, and there is nothing for an author to change — so a report that gave them one word
     * described a rule read in full as one whose shape defeated the reader.
     */
    @Test
    void aComparisonWhosePositionsCancelSaysThatAndNotTheOtherWord() {
        OnTheWay.Declined left = assertInstanceOf(OnTheWay.Declined.class,
                only("positionsCancel", true));
        assertEquals(new OnTheWay.Why.ComparisonStatesNoQuantity(), left.why());
    }

    /**
     * A bound as the position, the relation and the place it names.
     *
     * <p>Spelled rather than built here. What a term of this input is is the reading's to make, and
     * a term this test assembled would be compared against the reading's by whether two
     * constructions happened to agree — which is a question about this test and not about the rule.
     * The place is asked for its key, which is what makes two places one line.
     */
    private static String said(TakenConstraint taken) {
        TakenConstraint.Ordered bound = assertInstanceOf(TakenConstraint.Ordered.class, taken,
                "a written value on an order that counts nothing is a bound on it");
        return bound.term() + " " + bound.rel() + " " + bound.at().spelled();
    }

    /**
     * Where the bounded position runs once the region has been narrowed by what the way took in,
     * as the two ends the rules leave it.
     *
     * <p>Asked of the position the condition is about, which is the one shape a carrier that counts
     * nothing is ever asked in. The ends are places and are spelled by what they are: two writings
     * of one place are one end, and a test keyed on a spelling would be about the writing.
     */
    private static String runsAt(String behavior) {
        TakenConstraint.Ordered bound = assertInstanceOf(TakenConstraint.Ordered.class,
                taken(behavior, true), behavior + " is a bound on an order");
        SearchRegion narrowed = new WayToTheBorder(stating(behavior, true))
                .narrowing(regionOf(behavior));
        NumericDomain.Bounds runs =
                narrowed.projectionOf(bound.term()) instanceof NumericDomain.FormProjection.Within(
                        NumericDomain.Bounds held) ? held : null;
        return "[" + end(runs == null ? null : runs.min()) + ", "
                + end(runs == null ? null : runs.max()) + "]";
    }

    /** One end as the place it is at, or the word for no end. */
    private static String end(Endpoint at) {
        return at == null ? "null" : at.at().spelled();
    }

    /** What the body states coming out each way, which is one condition read twice and never two
     *  readings. */
    private static Map<Boolean, String> bothWays(String behavior) {
        return Map.of(true, said(taken(behavior, true)), false, said(taken(behavior, false)));
    }

    /** The constraint the body's single condition landed in. */
    private static TakenConstraint taken(String behavior, boolean holding) {
        return assertInstanceOf(OnTheWay.TakenIn.class, only(behavior, holding),
                behavior + " states something a search can compose against").taken();
    }

    /** The one thing the body's single condition states. */
    private static OnTheWay only(String behavior, boolean holding) {
        List<OnTheWay> stated = stating(behavior, holding);
        assertEquals(1, stated.size(), () -> behavior + " is one condition: " + stated);
        return stated.get(0);
    }

    private static List<OnTheWay> stating(String behavior, boolean holding) {
        return readingOf(behavior).stating(holding);
    }

    /** The region this compiler builds for the behavior's input, off the reading its conditions
     *  were read against — so a term of one is a term of the other. */
    private static SearchRegion regionOf(String behavior) {
        return readingOf(behavior).read().quantities().region();
    }

    /**
     * One behavior of the model, read once.
     *
     * <p>Kept per behavior, because the reading of an input is what the conditions are read against
     * and the region is built from: asked twice, a term of the one would be compared against a term
     * of the other, and what the test established would be that two readings of one model agree.
     */
    private record Read(Core body, souther.compiler.inputs.InputReading read, InputReads reads,
                        RuleReadingSource rules, String module, String behavior) {

        List<OnTheWay> stating(boolean holding) {
            return ReachingCuts.stating(Condition.of(body, reads, rules.symbols(),
                    rules.newtypes(), new ConditionNumbering(module, behavior)), read, holding);
        }
    }

    private static final Map<String, Read> READINGS = new java.util.concurrent.ConcurrentHashMap<>();

    private static Read readingOf(String behavior) {
        return READINGS.computeIfAbsent(behavior, name -> {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
            compilation.answerEverything();
            String module = compilation.modules().get(0);
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            assertNotNull(checked, "the model under test compiles");
            Core body = checked.behaviorBodies().get(name);
            assertNotNull(body, () -> "the model under test writes " + name);
            RuleReadingSource rules = RuleReadings.of(compilation, module);
            souther.compiler.inputs.InputDomain inputs =
                    compilation.db().ask(new Adequacy.Inputs(module)).value().get(name);
            InputReads reads = InputReads.ofParameters(inputs.parameterReads(),
                    checked.elementBindings().get(name));
            return new Read(body, inputs.reading(rules), reads, rules, module, name);
        });
    }
}
