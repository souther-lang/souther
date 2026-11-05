package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which of the cases a case said for several stands for a line decides in is asked of each of
 * them, and a case chosen part by part is given up as soon as what it has chosen leaves no row on
 * one side of the line.
 *
 * <p>Put to the asking with the answer for each condition written here, so what is checked is what
 * the asking makes of the answers: which conditions it asks, which cases it keeps, when it stops,
 * and what it says when a figure stopped it. Whether regions hold rows on both sides of a line is
 * {@code Cutting.Sides}'s, and is asked of models elsewhere.
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

    /** Asks, answering each condition by {@code crossing} and keeping what was asked. */
    private record Asking(Function<Proposition, CasesOfALineAsked.Crossing> crossing,
                          List<Proposition> asked) {

        /** Each condition {@code crossed} holds of may be crossed, and the others hold rows on
         *  one side alone. */
        Asking(Predicate<Proposition> crossed) {
            this(condition -> crossed.test(condition) ? CasesOfALineAsked.Crossing.MAY_CROSS
                    : CasesOfALineAsked.Crossing.CANNOT_CROSS, new ArrayList<>());
        }

        CasesOfALineAsked.Found of(DecidingCase.Cases cases) {
            return CasesOfALineAsked.casesOf(new DecidingCase(SAID, cases), condition -> {
                asked.add(condition);
                return crossing.apply(condition);
            });
        }
    }

    /** {@code noRows} are shown to hold no row, and the rest may be crossed. */
    private static Asking noRowsIn(Set<Proposition> noRows) {
        return new Asking(condition -> noRows.contains(condition)
                ? CasesOfALineAsked.Crossing.NO_ROWS : CasesOfALineAsked.Crossing.MAY_CROSS,
                new ArrayList<>());
    }

    /**
     * A prefix no row is in leaves none in any case past it: nothing past it is asked, nor said
     * as not worked out, and the cases past the other prefixes are asked as they were.
     */
    @Test
    void aPrefixNoRowIsInIsNotWalkedPast() {
        Asking asking = noRowsIn(Set.of(A));

        CasesOfALineAsked.Found found = asking.of(FOUR);
        assertEquals(List.of(new DecidingCase(SAID, FOUR)), found.decidesIn(),
                "the cases of b divide and those of a hold no row: the four as said");
        assertEquals(Set.of(), found.notWorkedOut(), "a case no row is in is worked out");
        assertEquals(List.of(SOME_OF_FOUR, A, B, both(B, C), both(B, D)), asking.asked(),
                "nothing past a");
    }

    /**
     * Every case with a row in it dividing rows makes the case what it was said as, though one it
     * stands for holds no row: that one adds no row to where the case holds, so the rows of the
     * case are the rows of the ones the line decides in.
     */
    @Test
    void aCaseNoRowIsInLeavesTheCaseWhatItWasSaidAs() {
        CasesOfALineAsked.Found found = noRowsIn(Set.of(both(A, D))).of(FOUR);

        assertEquals(List.of(new DecidingCase(SAID, FOUR)), found.decidesIn(),
                "the four as said, the one with no row among them");
        assertEquals(Set.of(), found.notWorkedOut());
    }

    /**
     * A case whose rows are on one side of the line keeps the case from being what it was said
     * as, where every other case with a row divides and one holds none: its rows would be counted
     * at the line, which turns nothing between them.
     */
    @Test
    void aCaseOnOneSideBesideOneNoRowIsInLeavesTheOthersEachByItself() {
        CasesOfALineAsked.Found found = new Asking(condition -> condition.equals(both(A, D))
                ? CasesOfALineAsked.Crossing.NO_ROWS : condition.equals(both(B, C))
                ? CasesOfALineAsked.Crossing.CANNOT_CROSS : CasesOfALineAsked.Crossing.MAY_CROSS,
                new ArrayList<>()).of(FOUR);

        assertEquals(List.of(DecidingCase.alone(both(A, C)), DecidingCase.alone(both(B, D))),
                found.decidesIn(), "the two that divide, each by itself");
    }

    /** Where some one of the cases holding is shown to hold no row, none does, and that one
     *  question settles all of them as it does where no row is on one side. */
    @Test
    void whereSomeOneHoldingHoldsNoRowNoneIsAsked() {
        Asking asking = noRowsIn(Set.of(SOME_OF_FOUR));

        assertEquals(IN_NONE, asking.of(FOUR));
        assertEquals(List.of(SOME_OF_FOUR), asking.asked());
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

    /** Whether {@code condition} can hold: no part of it is the denial of another. */
    private static boolean consistent(Proposition condition) {
        if (condition instanceof Proposition.Always always) {
            return always.holds();
        }
        List<Proposition> parts = condition instanceof Proposition.All all
                ? all.parts() : List.of(condition);
        return parts.stream().noneMatch(part -> parts.contains(part.denied()));
    }

    /**
     * What every case a line is asked in holds is chosen before the alternatives are, so that an
     * alternative contradicting it is given up where it is met. Chosen after them, the
     * contradiction is met once every alternative of every choice has been walked to, and the
     * asking is as long as all the ways of choosing and not as long as the ones that can hold.
     *
     * <p>Six choices of {@code c} or not {@code c}, with three of the six held beside them, are
     * eight cases and not sixty-four: the three choices the held parts settle are not walked both
     * ways to the end.
     */
    @Test
    void whatEveryCaseHoldsIsChosenBeforeTheAlternativesAreWalked() {
        int choices = 6;
        int held = 3;
        List<DecidingCase.Cases> factors = new ArrayList<>();
        for (int at = 0; at < choices; at++) {
            Proposition yes = truth("c" + at);
            factors.add(new DecidingCase.Cases.EachOf(List.of(one(yes), one(yes.denied()))));
        }
        for (int at = 0; at < held; at++) {
            factors.add(one(truth("c" + at)));
        }
        Asking asking = new Asking(WhereALineDecidesIsAskedOfEachCaseItWasSaidForTest::consistent);

        CasesOfALineAsked.Found found = asking.of(new DecidingCase.Cases.Together(factors));

        assertEquals(1 << (choices - held), found.decidesIn().size(),
                "a case for each way of choosing the three left open");
        assertEquals(Set.of(), found.notWorkedOut());
        assertEquals(24, asking.asked().size(),
                "some one holding, the three held, each of the three they settle both ways, and"
                        + " the tree of the three left open");
    }

    /** The parts {@code condition} is the conjunction of. */
    private static List<Proposition> partsOf(Proposition condition) {
        return condition instanceof Proposition.All all ? all.parts() : List.of(condition);
    }

    /**
     * The cases kept are the ones that hold, wherever among the choices the parts every case holds
     * are written: before them, between them, or after. A conjunction is the same conjunction
     * whichever part was chosen first, so the order of choosing is not a thing a case can be told
     * by.
     */
    @Test
    void theCasesKeptDoNotDependOnWhereTheHeldPartsAreWritten() {
        Proposition[] yes = {truth("c0"), truth("c1"), truth("c2")};
        List<DecidingCase.Cases> written = List.of(
                one(yes[0]),
                new DecidingCase.Cases.EachOf(List.of(one(yes[0]), one(yes[0].denied()))),
                one(yes[1]),
                new DecidingCase.Cases.EachOf(List.of(one(yes[1]), one(yes[1].denied()))),
                new DecidingCase.Cases.EachOf(List.of(one(yes[2]), one(yes[2].denied()))),
                one(yes[2]));

        Set<Proposition> expected = new LinkedHashSet<>();
        for (int mask = 0; mask < 8; mask++) {
            List<Proposition> chosen = new ArrayList<>();
            for (int at = 0; at < 3; at++) {
                chosen.add(yes[at]);
                chosen.add((mask >> at & 1) == 0 ? yes[at] : yes[at].denied());
            }
            Proposition all = Proposition.all(chosen);
            if (consistent(all)) {
                expected.add(all);
            }
        }
        Set<Proposition> every = new LinkedHashSet<>(expected);
        every.add(new Proposition.Always(false));
        DecidingCase.Cases together = new DecidingCase.Cases.Together(written);

        Asking asking = new Asking(WhereALineDecidesIsAskedOfEachCaseItWasSaidForTest::consistent);
        CasesOfALineAsked.Found found = asking.of(together);

        assertEquals(expected, found.decidesIn().stream()
                .map(DecidingCase::condition).collect(Collectors.toSet()),
                "the cases that can hold, as the conjunction of what each chose and what every"
                        + " case holds");
        assertEquals(Set.of(), found.notWorkedOut());

        CasesOfALineAsked.Atoms<Proposition> atoms =
                CasesOfALineAsked.atomsOf(new DecidingCase(SAID, together), condition -> condition);
        assertEquals(8, atoms.each().size(),
                "asked of every case, none given up, whichever order they are chosen in");
        assertEquals(every, atoms.each().stream().map(CasesOfALineAsked.Atom::condition)
                .collect(Collectors.toSet()),
                "each as what its choices leave of it: one whose choices deny each other holds"
                        + " nowhere");
        assertEquals(Set.of(), atoms.notWorkedOut());
    }

    /**
     * A case is asked as what its choices leave of it: a condition every case holds is asked of
     * each case with what the case chose put in it. {@code a} and {@code b} coming out alike,
     * held by every way of choosing each of them: once {@code a} is chosen it is {@code b}, once
     * {@code b} is chosen too it is nothing more, and with {@code b} failing it is nowhere. Asked
     * as it was written, it would be beside every case in full, which is as long as the statement
     * it came from.
     */
    @Test
    void aCaseIsAskedAsWhatItsChoicesLeaveOfIt() {
        Proposition alike = Proposition.any(List.of(both(A, B),
                both(A.denied(), B.denied())));
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(List.of(one(alike),
                new DecidingCase.Cases.EachOf(List.of(one(A), one(A.denied()))),
                new DecidingCase.Cases.EachOf(List.of(one(B), one(B.denied())))));
        Asking asking = new Asking(WhereALineDecidesIsAskedOfEachCaseItWasSaidForTest::consistent);

        CasesOfALineAsked.Found found = asking.of(cases);

        Proposition nowhere = new Proposition.Always(false);
        Proposition neither = both(A.denied(), B.denied());
        assertEquals(List.of(cases.holdingInSome(TAKEN_APART).orElseThrow(), alike,
                        both(A, B), both(A, B), nowhere, neither, nowhere, neither),
                asking.asked(), "the condition every case holds, and then each case as its"
                        + " choices leave it");
        assertEquals(List.of(DecidingCase.alone(both(A, B)), DecidingCase.alone(neither)),
                found.decidesIn(), "the two cases it holds in, each as what it chose");
    }

    /**
     * What every case holds is chosen first however deep in the choices it is written, since
     * choosing together is associative: the parts every case holds are the same whether they were
     * written beside the choices or as a group of their own.
     *
     * <p>Seven choices and six parts every case holds: written as a group, the walk is as long as
     * it is written flat, and short of the steps it is allowed. Chosen after the choices, each of
     * the hundred and twenty-eight ways would choose six more and the steps would run out.
     */
    @Test
    void whatEveryCaseHoldsIsChosenFirstWhetherItIsWrittenBesideTheChoicesOrAsAGroup() {
        int choices = 7;
        int held = 6;
        List<DecidingCase.Cases> flat = new ArrayList<>();
        List<DecidingCase.Cases> group = new ArrayList<>();
        for (int at = 0; at < choices; at++) {
            Proposition yes = truth("c" + at);
            flat.add(new DecidingCase.Cases.EachOf(List.of(one(yes), one(yes.denied()))));
        }
        List<DecidingCase.Cases> grouped = new ArrayList<>(flat);
        for (int at = 0; at < held; at++) {
            flat.add(one(truth("u" + at)));
            group.add(one(truth("u" + at)));
        }
        grouped.add(new DecidingCase.Cases.Together(group));
        Asking beside = new Asking(_ -> true);
        Asking asGroup = new Asking(_ -> true);

        CasesOfALineAsked.Found written = beside.of(new DecidingCase.Cases.Together(flat));
        CasesOfALineAsked.Found nested = asGroup.of(new DecidingCase.Cases.Together(grouped));

        assertEquals(Set.of(), written.notWorkedOut(), "written beside the choices");
        assertEquals(Set.of(), nested.notWorkedOut(), "written as a group of their own");
        assertEquals(beside.asked().size(), asGroup.asked().size(),
                "the same questions however the parts every case holds are written");
    }

    /**
     * What holds only in one alternative stays in it: a part written under a choice is chosen when
     * the choice is, and is not what every case holds.
     */
    @Test
    void whatOneAlternativeHoldsIsNotChosenForTheOthers() {
        Proposition x = truth("x");
        Proposition y = truth("y");
        Proposition z = truth("z");
        DecidingCase.Cases cases = new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.Together(List.of(one(x), one(y))), one(z)));

        CasesOfALineAsked.Found found = new Asking(_ -> true).of(cases);

        assertEquals(new CasesOfALineAsked.Found(List.of(new DecidingCase(SAID, cases)), Set.of()),
                found, "every case divides rows, and they are the two that were said");
        CasesOfALineAsked.Found withoutZ = new Asking(each -> !partsOf(each).contains(z)).of(cases);
        assertEquals(List.of(DecidingCase.alone(both(x, y))), withoutZ.decidesIn(),
                "x and y together, which z being refuted does not take away");
    }

    /**
     * Where the steps run out, the cases kept are among the ones that hold and the figure the
     * asking stopped at is said: a case not reached is not taken for one that does not hold.
     *
     * <p>Eight choices of two parts each, so that the walk is longer than it is allowed to be
     * though every way of choosing is a case that can be taken apart.
     */
    @Test
    void whereTheStepsRunOutWhatWasNotReachedIsSaidAndNotTakenForAnswered() {
        int choices = 8;
        Proposition common = truth("u");
        List<DecidingCase.Cases> factors = new ArrayList<>();
        Set<Proposition> holding = new LinkedHashSet<>();
        for (int at = 0; at < choices; at++) {
            Proposition yes = truth("c" + at);
            factors.add(new DecidingCase.Cases.EachOf(List.of(
                    new DecidingCase.Cases.Together(List.of(one(yes), one(common))),
                    new DecidingCase.Cases.Together(List.of(one(yes.denied()), one(common))))));
        }
        for (int mask = 0; mask < 1 << choices; mask++) {
            List<Proposition> chosen = new ArrayList<>();
            chosen.add(common);
            for (int at = 0; at < choices; at++) {
                Proposition yes = truth("c" + at);
                chosen.add((mask >> at & 1) == 0 ? yes : yes.denied());
            }
            holding.add(Proposition.all(chosen));
        }
        Asking asking = new Asking(_ -> true);

        CasesOfALineAsked.Found found = asking.of(new DecidingCase.Cases.Together(factors));

        assertEquals(Set.of(CompositionBudget.CASES_A_LINE_IS_ASKED_IN), found.notWorkedOut(),
                "the walk is longer than the steps it is allowed");
        Set<Proposition> kept = found.decidesIn().stream().map(DecidingCase::condition)
                .collect(Collectors.toSet());
        assertTrue(holding.containsAll(kept), "every case kept is one that holds");
        assertTrue(!kept.isEmpty() && kept.size() < holding.size(),
                "some were walked to, and not all");
    }

    /**
     * A choice nobody took apart is said as the figure it stopped at where a case can hold in it,
     * and not where the parts every case holds already leave no row on one side of the line: no
     * case in it decides, whichever way it would have been taken apart.
     */
    @Test
    void aChoiceNobodyTookApartIsSaidOnlyWhereACaseCouldHoldInIt() {
        CompositionBudget figure = CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO;
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(List.of(
                new DecidingCase.Cases.EachOf(List.of(one(A),
                        new DecidingCase.Cases.NotTakenApart(figure))),
                one(B)));

        CasesOfALineAsked.Found holding = new Asking(_ -> true).of(cases);
        assertEquals(List.of(DecidingCase.alone(both(A, B))), holding.decidesIn(),
                "the case that was taken apart is kept");
        assertEquals(Set.of(figure), holding.notWorkedOut(),
                "and the one that was not is said, beside it");

        CasesOfALineAsked.Found refuted = new Asking(each -> !partsOf(each).contains(B)
                && !each.equals(SOME_OF_FOUR)).of(cases);
        assertEquals(List.of(), refuted.decidesIn());
        assertEquals(Set.of(), refuted.notWorkedOut(),
                "B leaves no row on one side, so nothing in the choice nobody took apart decides");
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
     * More ways of choosing a case than are taken apart are not chosen: where some one holds is
     * asked of the condition they were said as, which holds exactly there and is no longer for
     * their being many, and past that the line is not worked out in them, at the figure.
     */
    @Test
    void moreWaysOfChoosingThanAreTakenApartAreAskedOnlyAsTheConditionTheyWereSaidAs() {
        DecidingCase.Cases many = manyCases(TAKEN_APART + 1);
        Asking asking = new Asking(_ -> true);

        assertEquals(new CasesOfALineAsked.Found(List.of(), Set.of(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)),
                asking.of(many), "more ways than are taken apart, and none is chosen");
        assertEquals(List.of(SAID), asking.asked(), "where some one holds, as it was said");
    }

    /**
     * Ways of choosing written as choices are counted before any is chosen: forty choices of two,
     * one below the other, are more ways than are taken apart, and nothing is chosen, saying also
     * the figure the cases at the bottom were never taken apart at.
     */
    @Test
    void waysWrittenAsChoicesAreCountedBeforeAnyIsChosen() {
        DecidingCase.Cases cases = new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO);
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
                () -> asking.of(deep), "the count bounds the choosing");
        assertEquals(new CasesOfALineAsked.Found(List.of(), Set.of(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)), found);
        assertEquals(List.of(SAID), asking.asked(), "and nothing asked but the condition");
    }

    /**
     * What stopped a taking apart is said, whichever way the asking comes to it: met as the
     * choosing walks, left among what the steps did not walk to, or among more ways of choosing
     * than are taken apart, where nothing is walked. That one figure stops the asking says nothing
     * about another one the cases already stopped at.
     */
    @Test
    void whatStoppedATakingApartIsSaidWhicheverWayTheAskingComesToIt() {
        DecidingCase.Cases readTooLong = new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN);

        assertEquals(new CasesOfALineAsked.Found(List.of(DecidingCase.alone(A)),
                        Set.of(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN)),
                new Asking(_ -> true).of(new DecidingCase.Cases.EachOf(
                        List.of(readTooLong, one(A)))),
                "met as it walks");

        assertEquals(new CasesOfALineAsked.Found(List.of(), Set.of(
                        CompositionBudget.CASES_A_LINE_IS_ASKED_IN,
                        CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN)),
                new Asking(each -> !isACaseOf(each, DEPTH)).of(new DecidingCase.Cases.EachOf(
                        List.of(deepCases(TAKEN_APART - 1, DEPTH), readTooLong))),
                "left where the steps ran out");

        List<DecidingCase.Cases> many = new ArrayList<>(
                ((DecidingCase.Cases.EachOf) manyCases(TAKEN_APART)).alternatives());
        many.add(readTooLong);
        assertEquals(new CasesOfALineAsked.Found(List.of(), Set.of(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO,
                        CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN)),
                new Asking(_ -> true).of(new DecidingCase.Cases.EachOf(many)),
                "among more ways of choosing than are taken apart, where nothing is walked");
    }

    /** And as many cases as are taken apart are asked to the end. */
    @Test
    void asManyCasesAsAreTakenApartAreAskedToTheEnd() {
        DecidingCase.Cases many = manyCases(TAKEN_APART);
        Proposition someOne = many.holdingInSome(TAKEN_APART).orElseThrow();
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
            DecidingCase.Cases chain = new DecidingCase.Cases.NotTakenApart(
                    CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO);
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
                dividing.of(new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)));
        assertEquals(List.of(SAID), dividing.asked(), "the condition alone");

        assertEquals(IN_NONE,
                new Asking(_ -> false).of(new DecidingCase.Cases.NotTakenApart(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)));
    }

    /**
     * One alternative stopping is no answer about another: a case after it dividing rows is kept,
     * beside the figure the other stopped at, whichever of the two is asked first.
     */
    @Test
    void anAlternativeThatStoppedDoesNotHideOneThatDividesRows() {
        DecidingCase.Cases notTakenApart = new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO);
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
        DecidingCase.Cases notTakenApart = new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO);
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
