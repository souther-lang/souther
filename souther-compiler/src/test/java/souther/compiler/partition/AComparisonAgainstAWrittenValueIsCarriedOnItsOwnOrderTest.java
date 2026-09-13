package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

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
        assertEquals(Map.of(true, "p.a NE t", false, "p.a EQ t"),
                bothWays("textApartFromAWrittenValue"));
        assertEquals(Map.of(true, "p.a EQ t", false, "p.a NE t"),
                bothWays("textAtAWrittenValue"));
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
        return bound.term() + " " + bound.rel() + " " + bound.at().key();
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
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, () -> "the model under test writes " + behavior);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        souther.compiler.inputs.InputDomain inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        InputReads reads = InputReads.ofParameters(inputs.parameterReads(),
                checked.elementBindings().get(behavior));
        return ReachingCuts.stating(Condition.of(body, reads, rules.symbols(), rules.newtypes(),
                new ConditionNumbering(module, behavior)), inputs.reading(rules), holding);
    }
}
