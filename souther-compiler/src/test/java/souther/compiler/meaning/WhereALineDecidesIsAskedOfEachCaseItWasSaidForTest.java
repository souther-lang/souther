package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a line decides in a case said for several is asked of each of them, and a case chosen
 * part by part is given up as soon as what it has chosen leaves no row on one side of the line.
 *
 * <p>Put to the asking with the answer for each condition written here, so what is checked is what
 * the asking makes of the answers: which conditions it asks, when it stops, and what it says when a
 * figure stopped it. Whether a region holds rows on both sides of a line is
 * {@code Cutting.crossedIn}'s, and is asked of models elsewhere.
 */
class WhereALineDecidesIsAskedOfEachCaseItWasSaidForTest {

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    private static final Proposition A = truth("a");
    private static final Proposition B = truth("b");
    private static final Proposition C = truth("c");
    private static final Proposition D = truth("d");

    private static DecidingCase.Cases one(Proposition condition) {
        return new DecidingCase.Cases.One(condition);
    }

    /** Any one of {@code a} and {@code b}, taken together with any one of {@code c} and
     *  {@code d}: four cases. */
    private static final DecidingCase.Cases FOUR = new DecidingCase.Cases.Together(List.of(
            new DecidingCase.Cases.EachOf(List.of(one(A), one(B))),
            new DecidingCase.Cases.EachOf(List.of(one(C), one(D)))));

    /** Asks, answering each condition by {@code crossed} and keeping what was asked. */
    private record Asking(Predicate<Proposition> crossed, List<Proposition> asked) {

        Asking(Predicate<Proposition> crossed) {
            this(crossed, new ArrayList<>());
        }

        CasesOfALineAsked.Found of(DecidingCase.Cases cases) {
            return new CasesOfALineAsked(condition -> {
                asked.add(condition);
                return crossed.test(condition);
            }).inSomeOf(cases);
        }
    }

    /**
     * A line no case holds rows on both sides of decides in none of them, however their union
     * stands. Each of the four is asked, and nothing else is taken for one of them.
     */
    @Test
    void aLineNoCaseDividesDecidesInNone() {
        Set<Proposition> crossing = Set.of(A, B, C, D);
        Asking asking = new Asking(crossing::contains);

        assertInstanceOf(CasesOfALineAsked.Found.InNone.class, asking.of(FOUR),
                "no case of the four holds rows on both sides, though each part alone does");
        assertEquals(List.of(A, Proposition.all(List.of(A, C)), Proposition.all(List.of(A, D)),
                        B, Proposition.all(List.of(B, C)), Proposition.all(List.of(B, D))),
                asking.asked(), "each case, part by part as it is chosen");
    }

    /** One case dividing rows is enough, and the asking stops at it. */
    @Test
    void oneCaseDividingRowsIsEnough() {
        Proposition bd = Proposition.all(List.of(B, D));
        Asking asking = new Asking(each -> Set.of(A, B, bd).contains(each));

        assertInstanceOf(CasesOfALineAsked.Found.InSome.class, asking.of(FOUR),
                () -> "b with d holds rows on both sides: " + asking.asked());
        assertEquals(bd, asking.asked().getLast(), "and nothing is asked past it");
    }

    /**
     * What has been chosen leaving no row on one side settles every case chosen past it, which are
     * not asked: two cases under {@code a} cost one question.
     */
    @Test
    void aChoiceDividingNoRowsSettlesEveryCaseChosenPastIt() {
        Asking asking = new Asking(each -> !each.equals(A));

        asking.of(new DecidingCase.Cases.Together(List.of(one(A),
                new DecidingCase.Cases.EachOf(List.of(one(C), one(D))))));
        assertEquals(List.of(A), asking.asked(), "a alone settles a with c and a with d");
    }

    /**
     * Past the figure, what was asked is no proof either way: the line is one where it decides was
     * not worked out, and the figure is the one counting the questions.
     */
    @Test
    void pastTheFigureNothingIsProvedAndTheFigureIsSaid() {
        List<DecidingCase.Cases> many = new ArrayList<>();
        int most = CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum();
        for (int i = 0; i <= most; i++) {
            many.add(one(truth("t" + i)));
        }
        Asking asking = new Asking(_ -> false);

        CasesOfALineAsked.Found found = asking.of(new DecidingCase.Cases.EachOf(many));
        assertEquals(new CasesOfALineAsked.Found.NotWorkedOut(
                        CompositionBudget.CASES_A_LINE_IS_ASKED_IN), found,
                "one more case than are asked is not one found to divide no rows");
        assertEquals(most, asking.asked().size(), "every question the figure allows was asked");
    }

    /** And as many cases as the figure allows are asked to the end. */
    @Test
    void asManyCasesAsTheFigureAllowsAreAskedToTheEnd() {
        List<DecidingCase.Cases> many = new ArrayList<>();
        for (int i = 0; i < CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum(); i++) {
            many.add(one(truth("t" + i)));
        }

        assertInstanceOf(CasesOfALineAsked.Found.InNone.class,
                new Asking(_ -> false).of(new DecidingCase.Cases.EachOf(many)));
    }

    /** Cases more than were taken apart are not asked at all, and say the figure that left them
     *  whole. */
    @Test
    void casesNotTakenApartAreNotWorkedOut() {
        Asking asking = new Asking(_ -> true);

        assertEquals(new CasesOfALineAsked.Found.NotWorkedOut(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO),
                asking.of(new DecidingCase.Cases.MoreThanWereTakenApart()));
        assertTrue(asking.asked().isEmpty(), () -> "nothing asked: " + asking.asked());
    }
}
