package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * Which of the cases a case said for several stands for a line decides in is asked of each of
 * them, and a case chosen part by part is given up as soon as what it has chosen leaves no row on
 * one side of the line.
 *
 * <p>Put to the asking with the answer for each condition written here, so what is checked is what
 * the asking makes of the answers: which conditions it asks, which cases it keeps, when it stops,
 * and what it says when a figure stopped it. Whether a region holds rows on both sides of a line is
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

    private static Proposition both(Proposition one, Proposition other) {
        return Proposition.all(List.of(one, other));
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

    private static final CasesOfALineAsked.Found IN_NONE =
            new CasesOfALineAsked.Found(List.of(), Set.of());

    /** Asks, answering each condition by {@code crossed} and keeping what was asked. */
    private record Asking(Predicate<Proposition> crossed, List<Proposition> asked) {

        Asking(Predicate<Proposition> crossed) {
            this(crossed, new ArrayList<>());
        }

        CasesOfALineAsked.Found of(DecidingCase.Cases cases) {
            return new CasesOfALineAsked(condition -> {
                asked.add(condition);
                return crossed.test(condition);
            }).casesOf(new DecidingCase(SAID, cases));
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

        assertEquals(IN_NONE, asking.of(FOUR),
                "no case of the four holds rows on both sides, though each part alone does");
        assertEquals(List.of(SOME_OF_FOUR, A, both(A, C), both(A, D), B, both(B, C), both(B, D)),
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

        assertEquals(IN_NONE, asking.of(FOUR));
        assertEquals(List.of(SOME_OF_FOUR), asking.asked(),
                "one question, of the cases themselves");
    }

    /**
     * The cases that divide rows are the ones kept, each under its own condition, and the ones that
     * do not are gone: a row in one of those is somewhere the line turns nothing. Every case is
     * asked, since one dividing rows is no answer about another.
     */
    @Test
    void onlyTheCasesDividingRowsAreKept() {
        Asking asking = new Asking(each ->
                Set.of(SOME_OF_FOUR, A, B, both(A, C), both(B, D)).contains(each));

        CasesOfALineAsked.Found found = asking.of(FOUR);
        assertEquals(List.of(DecidingCase.alone(both(A, C)), DecidingCase.alone(both(B, D))),
                found.decidesIn(), "a with c and b with d, and neither of the other two");
        assertEquals(Set.of(), found.notWorkedOut());
        assertEquals(List.of(SOME_OF_FOUR, A, both(A, C), both(A, D), B, both(B, C), both(B, D)),
                asking.asked(), "past the first that divides rows, to the last case");
    }

    /**
     * Where every case divides rows, the case is kept as it was said: it is already where the line
     * decides, and said again it would be read under another condition for nothing.
     */
    @Test
    void whereEveryCaseDividesRowsTheCaseIsKeptAsItWasSaid() {
        assertEquals(new CasesOfALineAsked.Found(List.of(new DecidingCase(SAID, FOUR)), Set.of()),
                new Asking(_ -> true).of(FOUR));
    }

    /**
     * Past as many as the cases where a line decides are said in, the ones that divide rows are
     * said as one again, standing for each of them and for no other.
     */
    @Test
    void pastAsManyAsAreSaidTheCasesKeptAreSaidAsOne() {
        int count = WhereEachLineDecides.MOST_CASES + 2;
        DecidingCase.Cases many = manyCases(count);
        Proposition dropped = truth("t0");
        Asking asking = new Asking(each -> !each.equals(dropped));

        CasesOfALineAsked.Found found = asking.of(many);
        assertEquals(1, found.decidesIn().size(), () -> "one case: " + found);
        DecidingCase kept = found.decidesIn().getFirst();
        List<Proposition> standsFor = DecidingCases.eachOf(kept.standsFor());
        assertEquals(DecidingCases.eachOf(many).subList(1, count), standsFor,
                "every case but the one that divides no rows");
        assertEquals(kept.standsFor().holdingInSome().orElseThrow(), kept.condition(),
                "said as where some one of them holds");

        int few = WhereEachLineDecides.MOST_CASES + 1;
        CasesOfALineAsked.Found asFew = new Asking(each -> !each.equals(dropped))
                .of(manyCases(few));
        assertEquals(DecidingCases.eachOf(manyCases(few)).subList(1, few).stream()
                        .map(DecidingCase::alone).toList(), asFew.decidesIn(),
                "as many as are said one by one are each a case of their own");
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
     * Rows on both sides of what has been chosen so far are no proof about a case chosen further:
     * they may each be in a case of their own. A case is kept only once chosen to the end.
     */
    @Test
    void aChoiceDividingRowsKeepsOnlyTheCasesChosenToTheEnd() {
        Asking asking = new Asking(each -> !each.equals(both(A, D)));

        CasesOfALineAsked.Found found = asking.of(new DecidingCase.Cases.Together(List.of(one(A),
                new DecidingCase.Cases.EachOf(List.of(one(C), one(D))))));
        assertEquals(List.of(DecidingCase.alone(both(A, C))), found.decidesIn(),
                "a divides rows, and of the cases under it only a with c does");
    }

    /**
     * Past the figure, what was asked is no proof either way: the line is one where it decides was
     * not worked out, and the figure is the one counting the questions.
     */
    @Test
    void pastTheFigureNothingIsProvedAndTheFigureIsSaid() {
        DecidingCase.Cases many = manyCases(ALTERNATIVES_THE_STEPS_ALLOW + 1);
        Proposition someOne = many.holdingInSome().orElseThrow();
        Asking asking = new Asking(someOne::equals);

        assertEquals(new CasesOfALineAsked.Found(List.of(),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_ASKED_IN)), asking.of(many),
                "one more case than the steps allow is not a proof that no case divides rows");
        assertEquals(ALTERNATIVES_THE_STEPS_ALLOW + 1, asking.asked().size(),
                "where some one holds, and every case the steps allowed");
    }

    /**
     * The cases shown to divide rows before the steps ran out are kept, beside the figure the rest
     * stopped at: neither speaks for the other.
     */
    @Test
    void theCasesShownBeforeTheFigureAreKeptBesideIt() {
        DecidingCase.Cases many = manyCases(ALTERNATIVES_THE_STEPS_ALLOW + 1);
        Proposition first = truth("t0");
        Proposition someOne = many.holdingInSome().orElseThrow();
        Asking asking = new Asking(each -> each.equals(someOne) || each.equals(first));

        assertEquals(new CasesOfALineAsked.Found(List.of(DecidingCase.alone(first)),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_ASKED_IN)), asking.of(many));
    }

    /** And as many cases as the steps allow are asked to the end. */
    @Test
    void asManyCasesAsTheStepsAllowAreAskedToTheEnd() {
        DecidingCase.Cases many = manyCases(ALTERNATIVES_THE_STEPS_ALLOW);
        Proposition someOne = many.holdingInSome().orElseThrow();

        assertEquals(IN_NONE, new Asking(someOne::equals).of(many));
    }

    /**
     * How many alternatives of one part each the steps allow: one step asks where some one holds,
     * and each alternative is two, the choosing of it and the asking of its part.
     */
    private static final int ALTERNATIVES_THE_STEPS_ALLOW =
            (CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum() - 1) / 2;

    /**
     * Choosing among alternatives that ask nothing is counted too. Twenty-odd choices of two, one
     * below the other, over cases nobody took apart are more ways than any run walks; counted by
     * the questions alone, the one question asked would have left them all to walk. Counted by the
     * step, the choosing stops where the steps do, and says both figures: the steps, and the cases
     * nobody took apart that were met and that are left.
     */
    @Test
    void choosingThatAsksNothingRunsOutOfStepsAndStops() {
        DecidingCase.Cases cases = new DecidingCase.Cases.MoreThanWereTakenApart();
        for (int i = 0; i < 40; i++) {
            cases = new DecidingCase.Cases.Together(List.of(
                    new DecidingCase.Cases.EachOf(List.of(
                            new DecidingCase.Cases.Together(List.of()),
                            new DecidingCase.Cases.Together(List.of()))),
                    cases));
        }
        DecidingCase.Cases deep = cases;
        Asking asking = new Asking(_ -> true);

        CasesOfALineAsked.Found found = assertTimeoutPreemptively(Duration.ofSeconds(10),
                () -> asking.of(deep), "the choosing stops where the steps do");
        assertEquals(new CasesOfALineAsked.Found(List.of(), Set.of(
                        CompositionBudget.CASES_A_LINE_IS_ASKED_IN,
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)), found);
        assertEquals(List.of(SAID), asking.asked(), "and asked nothing but the condition");
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
        assertEquals(new CasesOfALineAsked.Found(List.of(),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)),
                dividing.of(new DecidingCase.Cases.MoreThanWereTakenApart()));
        assertEquals(List.of(SAID), dividing.asked(), "the condition alone");

        assertEquals(IN_NONE,
                new Asking(_ -> false).of(new DecidingCase.Cases.MoreThanWereTakenApart()));
    }

    /**
     * One alternative stopping is no answer about another: a case after it dividing rows is kept,
     * beside the figure the other stopped at, whichever of the two is asked first.
     */
    @Test
    void anAlternativeThatStoppedDoesNotHideOneThatDividesRows() {
        DecidingCase.Cases notTakenApart = new DecidingCase.Cases.MoreThanWereTakenApart();
        for (List<DecidingCase.Cases> order : List.of(List.of(notTakenApart, one(A)),
                List.of(one(A), notTakenApart))) {
            assertEquals(new CasesOfALineAsked.Found(List.of(DecidingCase.alone(A)),
                            Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)),
                    new Asking(_ -> true).of(new DecidingCase.Cases.EachOf(order)),
                    () -> "a divides rows, asked in the order " + order);
        }
    }

    /**
     * Alternatives stopped at two figures, and none dividing rows, are not worked out at both,
     * whichever is asked first: which figure was met first is what happened on the way.
     */
    @Test
    void alternativesStoppedAtTwoFiguresSayBoth() {
        DecidingCase.Cases notTakenApart = new DecidingCase.Cases.MoreThanWereTakenApart();
        DecidingCase.Cases tooMany =
                manyCases(CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum());
        Proposition someOne = new DecidingCase.Cases.EachOf(List.of(notTakenApart, tooMany))
                .holdingInSome().orElse(SAID);
        for (List<DecidingCase.Cases> order : List.of(List.of(notTakenApart, tooMany),
                List.of(tooMany, notTakenApart))) {
            assertEquals(new CasesOfALineAsked.Found(List.of(), Set.of(
                            CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO,
                            CompositionBudget.CASES_A_LINE_IS_ASKED_IN)),
                    new Asking(each -> each.equals(someOne))
                            .of(new DecidingCase.Cases.EachOf(order)),
                    () -> "both figures, asked in the order " + order);
        }
    }
}
