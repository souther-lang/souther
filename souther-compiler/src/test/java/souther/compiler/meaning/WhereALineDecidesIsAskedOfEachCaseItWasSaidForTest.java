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

    /** The condition a case said for several is said as, which the asking reads only where its
     *  cases were not taken apart. */
    private static final Proposition SAID = truth("said");

    /** Where some one of the four holds: {@code a} or {@code b}, and {@code c} or {@code d}. */
    private static final Proposition SOME_OF_FOUR = Proposition.all(List.of(
            Proposition.any(List.of(A, B)), Proposition.any(List.of(C, D))));

    /** Asks, answering each condition by {@code crossed} and keeping what was asked. */
    private record Asking(Predicate<Proposition> crossed, List<Proposition> asked) {

        Asking(Predicate<Proposition> crossed) {
            this(crossed, new ArrayList<>());
        }

        CasesOfALineAsked.Found of(DecidingCase.Cases cases) {
            return new CasesOfALineAsked(condition -> {
                asked.add(condition);
                return crossed.test(condition);
            }).inSomeOf(new DecidingCase(SAID, cases));
        }
    }

    /**
     * A line no case holds rows on both sides of decides in none of them, though rows stand on
     * both sides where some one of them holds. That is asked first, and then each of the four,
     * part by part as it is chosen; nothing else is taken for one of them.
     */
    @Test
    void aLineNoCaseDividesDecidesInNone() {
        Set<Proposition> crossing = Set.of(SOME_OF_FOUR, A, B, C, D);
        Asking asking = new Asking(crossing::contains);

        assertInstanceOf(CasesOfALineAsked.Found.InNone.class, asking.of(FOUR),
                "no case of the four holds rows on both sides, though each part alone does");
        assertEquals(List.of(SOME_OF_FOUR, A, Proposition.all(List.of(A, C)),
                        Proposition.all(List.of(A, D)), B, Proposition.all(List.of(B, C)),
                        Proposition.all(List.of(B, D))),
                asking.asked(), "where some one holds, then each case part by part");
    }

    /**
     * Where some one of the cases holds no row on one side of the line, no case does, and that one
     * question settles all of them. It is asked of the cases and not of the condition they were
     * said as.
     */
    @Test
    void whereSomeOneHoldingDividesNoRowsNoneIsAsked() {
        Asking asking = new Asking(each -> !each.equals(SOME_OF_FOUR));

        assertInstanceOf(CasesOfALineAsked.Found.InNone.class, asking.of(FOUR));
        assertEquals(List.of(SOME_OF_FOUR), asking.asked(),
                "one question, of the cases themselves");
    }

    /** One case dividing rows is enough, and the asking stops at it. */
    @Test
    void oneCaseDividingRowsIsEnough() {
        Proposition bd = Proposition.all(List.of(B, D));
        Asking asking = new Asking(each -> Set.of(SOME_OF_FOUR, A, B, bd).contains(each));

        assertInstanceOf(CasesOfALineAsked.Found.InSome.class, asking.of(FOUR),
                () -> "b with d holds rows on both sides: " + asking.asked());
        assertEquals(bd, asking.asked().getLast(), "and nothing is asked past it");
    }

    /**
     * What has been chosen leaving no row on one side settles every case chosen past it, which are
     * not asked: two cases under {@code a} cost one question past the first.
     */
    @Test
    void aChoiceDividingNoRowsSettlesEveryCaseChosenPastIt() {
        Asking asking = new Asking(each -> !each.equals(A));

        asking.of(new DecidingCase.Cases.Together(List.of(one(A),
                new DecidingCase.Cases.EachOf(List.of(one(C), one(D))))));
        assertEquals(List.of(Proposition.all(List.of(A, Proposition.any(List.of(C, D)))), A),
                asking.asked(), "a alone settles a with c and a with d");
    }

    /**
     * Past the figure, what was asked is no proof either way: the line is one where it decides was
     * not worked out, and the figure is the one counting the questions.
     */
    @Test
    void pastTheFigureNothingIsProvedAndTheFigureIsSaid() {
        int most = CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum();
        DecidingCase.Cases many = manyCases(most);
        Proposition someOne = many.holdingInSome().orElseThrow();
        Asking asking = new Asking(someOne::equals);

        CasesOfALineAsked.Found found = asking.of(many);
        assertEquals(new CasesOfALineAsked.Found.NotWorkedOut(
                        CompositionBudget.CASES_A_LINE_IS_ASKED_IN), found,
                "one more question than are asked is not a proof that no case divides rows");
        assertEquals(most, asking.asked().size(), "every question the figure allows was asked");
    }

    /** And as many questions as the figure allows are asked to the end. */
    @Test
    void asManyQuestionsAsTheFigureAllowsAreAskedToTheEnd() {
        DecidingCase.Cases many =
                manyCases(CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum() - 1);
        Proposition someOne = many.holdingInSome().orElseThrow();

        assertInstanceOf(CasesOfALineAsked.Found.InNone.class,
                new Asking(someOne::equals).of(many));
    }

    /** {@code count} cases of one truth each. */
    private static DecidingCase.Cases manyCases(int count) {
        List<DecidingCase.Cases> many = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            many.add(one(truth("t" + i)));
        }
        return new DecidingCase.Cases.EachOf(many);
    }

    /**
     * Cases more than were taken apart are asked only as the condition they were said as, which
     * is all that says where they hold: where rows stand on both sides of it, they say the figure
     * that left them whole; where none do, none of them divides rows.
     */
    @Test
    void casesNotTakenApartAreAskedAsTheirConditionAndNoFurther() {
        Asking dividing = new Asking(_ -> true);
        assertEquals(new CasesOfALineAsked.Found.NotWorkedOut(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO),
                dividing.of(new DecidingCase.Cases.MoreThanWereTakenApart()));
        assertEquals(List.of(SAID), dividing.asked(), "the condition alone");

        assertInstanceOf(CasesOfALineAsked.Found.InNone.class,
                new Asking(_ -> false).of(new DecidingCase.Cases.MoreThanWereTakenApart()));
    }
}
