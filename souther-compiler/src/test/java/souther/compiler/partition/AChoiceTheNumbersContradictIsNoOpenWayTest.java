package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A choice whose numbers contradict what the way already holds is no open way, and is not counted
 * against the figure.
 *
 * <p>Put to the way directly, with the alternatives written as the conditions of a body leave them:
 * every one a statement of numbers against nought. What is shown contradictory is closed before it
 * is added to the open ways; what is not shown contradictory is open, whether or not a row is
 * there; and two choices that look alike are two choices.
 */
class AChoiceTheNumbersContradictIsNoOpenWayTest {

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0));

    private static final NumericTerm X = term("x");
    private static final NumericTerm Y = term("y");

    private static NumericTerm term(String field) {
        return new NumericTerm.ValueOf(TermPath.of("r").then(field));
    }

    /** {@code weight * term + constant} against nought, as a body's comparison leaves it. */
    private static OnTheWay holds(NumericTerm term, long weight, long constant, Rel rel) {
        return new OnTheWay.TakenIn(WHERE, new RowDemand.Relational(
                new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant),
                        Map.of(term, ExactRatio.of(weight))), rel)));
    }

    private static OnTheWay.OneOf oneOf(int occurrence, OnTheWay one, OnTheWay other) {
        return new OnTheWay.OneOf(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, occurrence),
                WHERE, List.of(List.of(one), List.of(other)), Optional.empty());
    }

    private static Reachability of(OnTheWay... onTheWay) {
        return Reachability.of(new WayToTheBorder(List.of(onTheWay)), region());
    }

    /** How many ways a row past the conditions is looked for along, each of them open. */
    private static int openWays(Reachability reachability) {
        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                reachability, () -> "some way is open: " + reachability);
        return assertInstanceOf(Reachability.Ways.Each.class, reaching.ways(),
                () -> "every way was looked along: " + reaching.ways()).along().size();
    }

    /**
     * A year difference of at least seventy-one and one below seventy hold one form nowhere, so
     * of the four ways the two choices make, that one is not a way.
     */
    @Test
    void twoAlternativesOfOneFormThatLeaveNoLevelAreNotAnOpenWay() {
        assertEquals(3, openWays(of(
                oneOf(1, holds(X, 1, -71, Rel.GE), holds(X, 1, -71, Rel.LT)),
                oneOf(2, holds(X, 1, -70, Rel.LT), holds(X, 1, -70, Rel.GE)))));
    }

    @Test
    void whereEveryWayLeavesNoLevelNothingReachesAndTheStatementsAreTheProof() {
        Reachability reachability = of(
                oneOf(1, holds(X, 1, -71, Rel.GE), holds(X, 1, -72, Rel.GE)),
                oneOf(2, holds(X, 1, -70, Rel.LT), holds(X, 1, -60, Rel.LT)));

        assertInstanceOf(Reachability.NumbersLeaveNone.class, reachability,
                () -> "no way is open: " + reachability);
    }

    /**
     * Over the integers nothing lies between zero and one, but over the reals something does, and
     * the reading proves over the reals: a way not shown to leave none is open.
     */
    @Test
    void whatIsNotShownToLeaveNoLevelIsAnOpenWay() {
        assertEquals(3, openWays(of(
                oneOf(1, holds(X, 1, 0, Rel.GT), holds(X, 1, 0, Rel.LE)),
                oneOf(2, holds(X, 1, -1, Rel.LT), holds(X, 1, -1, Rel.GE)))),
                "x > 0 beside x < 1 is open, and only x <= 0 beside x >= 1 is closed");
    }

    /** Statements of two forms say nothing of each other, so none of the four is closed. */
    @Test
    void choicesOnTwoFormsAreFourWays() {
        assertEquals(4, openWays(of(
                oneOf(1, holds(X, 1, -71, Rel.GE), holds(X, 1, -71, Rel.LT)),
                oneOf(2, holds(Y, 1, -71, Rel.GE), holds(Y, 1, -71, Rel.LT)))));
    }

    /**
     * Two choices written alike are two choices: the way takes one alternative of each, and the
     * ones that agree are the ways, where merging them by what they say would leave one.
     */
    @Test
    void twoChoicesWrittenAlikeAreTwoChoices() {
        assertEquals(2, openWays(of(
                oneOf(1, holds(X, 1, -71, Rel.GE), holds(X, 1, -71, Rel.LT)),
                oneOf(2, holds(X, 1, -71, Rel.GE), holds(X, 1, -71, Rel.LT)))));
    }

    /** A choice of {@code levels} alternatives, the {@code k}-th of which holds {@code x == k}. */
    private static OnTheWay.OneOf atEachLevelUpTo(int occurrence, int levels) {
        List<List<OnTheWay>> alternatives = new ArrayList<>();
        for (int level = 0; level < levels; level++) {
            alternatives.add(List.of(holds(X, 1, -level, Rel.EQ)));
        }
        return new OnTheWay.OneOf(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, occurrence),
                WHERE, alternatives, Optional.empty());
    }

    /**
     * More ways than are looked along, none of which the statements contradict, are looked along
     * whole past the figure. Nothing here reads a declaration, so what the declarations leave of
     * the type is no part of whether this holds.
     */
    @Test
    void waysThatNothingClosesPastTheFigureAreLookedAlongWhole() {
        int levels = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum() + 1;

        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                of(atEachLevelUpTo(1, levels)));

        Reachability.Ways.Whole whole = assertInstanceOf(Reachability.Ways.Whole.class,
                reaching.ways(), () -> "the ways past the figure: " + reaching.ways());
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, whole.figure());
    }

    /**
     * The same number of ways, all but one of which the numbers close, are no more than are looked
     * along: what is closed is not counted against the figure.
     */
    @Test
    void waysTheNumbersCloseDoNotCountAgainstTheFigure() {
        int levels = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum() + 1;

        assertEquals(1, openWays(of(holds(X, 1, -3, Rel.EQ), atEachLevelUpTo(1, levels))),
                "x == 3 leaves the alternative x == 3 alone");
    }

    private static SearchRegion region() {
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { x: Int, y: Int }
                data Yes

                behavior f : (r: R) -> Yes
                let f (r) = Yes
                """, "Main");
        compilation.answerEverything();
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        InputReading reading = inputs.reading(RuleReadings.of(compilation, "m"));
        return reading.quantities().region();
    }
}
