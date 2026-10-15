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
            return CasesOfALineAsked.casesOf(new DecidingCase(SAID, cases), condition -> {
                asked.add(condition);
                return crossed.test(condition);
            });
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
     * The cases kept are each a case of their own however many there are: how many a line is read
     * in one by one is counted over the line, and not over one case it held.
     */
    @Test
    void theCasesKeptAreEachACaseOfTheirOwn() {
        int count = WhereEachLineDecides.MOST_CASES + 2;
        DecidingCase.Cases many = manyCases(count);
        Proposition dropped = truth("t0");

        assertEquals(DecidingCases.eachOf(many).subList(1, count).stream()
                        .map(DecidingCase::alone).toList(),
                new Asking(each -> !each.equals(dropped)).of(many).decidesIn(),
                "every case but the one that divides no rows");
    }

    /**
     * Past as many as the cases where a line decides are said in, a line's cases are said as one,
     * standing for each of them; and what every one of them holds is said once, ahead of some one
     * of what tells them apart.
     */
    @Test
    void pastAsManyAsAreSaidALinesCasesAreSaidAsOne() {
        List<DecidingCase> each = new ArrayList<>();
        for (int i = 0; i <= WhereEachLineDecides.MOST_CASES; i++) {
            each.add(DecidingCase.alone(Proposition.all(List.of(A, truth("t" + i)))));
        }
        List<DecidingCase> asMany = each.subList(0, WhereEachLineDecides.MOST_CASES);
        assertEquals(asMany, DecidingCase.saidInAsFewAsMay(asMany),
                "as many as are said one by one are each a case of their own");

        List<DecidingCase> said = DecidingCase.saidInAsFewAsMay(each);
        assertEquals(1, said.size(), () -> "one case: " + said);
        assertEquals(each.stream().map(DecidingCase::condition).toList(),
                DecidingCases.eachOf(said.getFirst().standsFor()), "standing for each of them");
        assertEquals(Proposition.all(List.of(A, Proposition.any(each.stream()
                        .map(one -> ((Proposition.All) one.condition()).parts().stream()
                                .filter(part -> !part.equals(A)).findFirst().orElseThrow())
                        .toList()))),
                said.getFirst().condition(), "a once, and some one of the truths beside it");
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

    private static final int TAKEN_APART =
            CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum();

    /**
     * More ways of choosing a case than cases are taken apart are more cases than were taken
     * apart, and none is asked: where some one holds is the one question, and the figure is the
     * one bounding how many cases are taken apart.
     */
    @Test
    void moreWaysOfChoosingThanCasesAreTakenApartAreNotAsked() {
        DecidingCase.Cases many = manyCases(TAKEN_APART + 1);
        Proposition someOne = many.holdingInSome().orElseThrow();
        Asking asking = new Asking(_ -> true);

        assertEquals(new CasesOfALineAsked.Found(List.of(),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)),
                asking.of(many));
        assertEquals(List.of(someOne), asking.asked(), "where some one holds, and nothing else");
    }

    /**
     * Ways of choosing written as choices are counted as the cases they make, without choosing
     * any: forty choices of two, one below the other, are more ways than are taken apart, and the
     * choosing is not begun.
     */
    @Test
    void waysWrittenAsChoicesAreCountedWithoutChoosing() {
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
                () -> asking.of(deep), "nothing is chosen");
        assertEquals(new CasesOfALineAsked.Found(List.of(),
                Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)), found);
        assertEquals(List.of(SAID), asking.asked(), "and nothing asked but the condition");
    }

    /** And as many cases as are taken apart are asked to the end. */
    @Test
    void asManyCasesAsAreTakenApartAreAskedToTheEnd() {
        DecidingCase.Cases many = manyCases(TAKEN_APART);
        Proposition someOne = many.holdingInSome().orElseThrow();
        Asking asking = new Asking(someOne::equals);

        assertEquals(IN_NONE, asking.of(many));
        assertEquals(TAKEN_APART + 1, asking.asked().size(),
                "where some one holds, and every case");
    }

    /**
     * Cases chosen through several parts each cost a step for each part and each alternative
     * taken; past the steps, what was asked is no proof either way, and the figure is the one
     * counting the steps. As many cases as are taken apart, each chosen through four parts no two
     * of them share, every part but the last leaving rows on both sides, are more steps than that.
     */
    @Test
    void pastTheStepsNothingIsProvedAndTheFigureIsSaid() {
        Asking asking = new Asking(each -> !isACaseOf(each, DEPTH));

        assertEquals(new CasesOfALineAsked.Found(List.of(),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_ASKED_IN)),
                asking.of(deepCases(TAKEN_APART, DEPTH)),
                "one more step than the figure allows is not a proof that no case divides rows");
    }

    /**
     * The cases shown to divide rows before the steps ran out are kept, beside the figure the rest
     * stopped at: neither speaks for the other.
     */
    @Test
    void theCasesShownBeforeTheStepsRanOutAreKeptBesideTheFigure() {
        Proposition first = deepCase(0, DEPTH);
        Asking asking = new Asking(each -> !isACaseOf(each, DEPTH) || each.equals(first));

        assertEquals(new CasesOfALineAsked.Found(List.of(DecidingCase.alone(first)),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_ASKED_IN)),
                asking.of(deepCases(TAKEN_APART, DEPTH)));
    }

    /** And as many as the steps allow are asked to the end: one step asks where some one holds,
     *  and each case is one alternative taken and a step for each of its parts. */
    @Test
    void asManyCasesAsTheStepsAllowAreAskedToTheEnd() {
        int allowed = (CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum() - 1) / (DEPTH + 1);

        assertEquals(IN_NONE, new Asking(each -> !isACaseOf(each, DEPTH))
                .of(deepCases(allowed, DEPTH)));
    }

    /**
     * Choosing among alternatives that ask nothing is counted too: as many cases as are taken
     * apart, each reached through choices of one alternative that ask nothing, over cases nobody
     * took apart. Counted by the questions alone, the one question asked would leave all of it to
     * walk; counted by the step, the choosing stops where the steps do, and says both figures: the
     * steps, and the cases nobody took apart that were met and that are left.
     */
    @Test
    void choosingThatAsksNothingRunsOutOfStepsAndStops() {
        List<DecidingCase.Cases> each = new ArrayList<>();
        for (int i = 0; i < TAKEN_APART; i++) {
            DecidingCase.Cases chain = new DecidingCase.Cases.MoreThanWereTakenApart();
            for (int level = 0; level < DEPTH; level++) {
                chain = new DecidingCase.Cases.Together(List.of(new DecidingCase.Cases.EachOf(
                        List.of(new DecidingCase.Cases.Together(List.of()))), chain));
            }
            each.add(chain);
        }
        Asking asking = new Asking(_ -> true);

        assertEquals(new CasesOfALineAsked.Found(List.of(), Set.of(
                        CompositionBudget.CASES_A_LINE_IS_ASKED_IN,
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)),
                asking.of(new DecidingCase.Cases.EachOf(each)));
        assertEquals(List.of(SAID), asking.asked(), "and asked nothing but the condition");
    }

    /** How many parts each of {@link #deepCases} is chosen through. */
    private static final int DEPTH = 4;

    /** {@code count} cases of one truth each. */
    private static DecidingCase.Cases manyCases(int count) {
        List<DecidingCase.Cases> many = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            many.add(one(truth("t" + i)));
        }
        return new DecidingCase.Cases.EachOf(many);
    }

    /** {@code count} cases, each {@code depth} truths of its own held together. */
    private static DecidingCase.Cases deepCases(int count, int depth) {
        List<DecidingCase.Cases> many = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            List<DecidingCase.Cases> parts = new ArrayList<>();
            for (int at = 0; at < depth; at++) {
                parts.add(one(truth("t" + i + "." + at)));
            }
            many.add(new DecidingCase.Cases.Together(parts));
        }
        return new DecidingCase.Cases.EachOf(many);
    }

    /** The {@code i}th of {@link #deepCases}, as the condition it is chosen to. */
    private static Proposition deepCase(int i, int depth) {
        List<Proposition> parts = new ArrayList<>();
        for (int at = 0; at < depth; at++) {
            parts.add(truth("t" + i + "." + at));
        }
        return Proposition.all(parts);
    }

    /** Whether {@code condition} is one of {@link #deepCases} chosen to the end. */
    private static boolean isACaseOf(Proposition condition, int depth) {
        return condition instanceof Proposition.All all && all.parts().size() == depth
                && all.parts().stream().allMatch(Proposition.Truth.class::isInstance);
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
        DecidingCase.Cases tooDeep = deepCases(TAKEN_APART - 1, DEPTH);
        for (List<DecidingCase.Cases> order : List.of(List.of(notTakenApart, tooDeep),
                List.of(tooDeep, notTakenApart))) {
            assertEquals(new CasesOfALineAsked.Found(List.of(), Set.of(
                            CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO,
                            CompositionBudget.CASES_A_LINE_IS_ASKED_IN)),
                    new Asking(each -> !isACaseOf(each, DEPTH))
                            .of(new DecidingCase.Cases.EachOf(order)),
                    () -> "both figures, asked in the order " + order);
        }
    }
}
