package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A choice among the parts of a case that is about positions none of the way, the line, what every
 * case holds and the other choices are about is asked on its own, beside what every case holds.
 * The cases that divide rows are then asked of in the number of the alternatives each choice has
 * added up, and not multiplied.
 *
 * <p>Where a choice shares a position with something held, or a position is not known, or the
 * cases were never taken apart, it is asked with the rest and the answer is the one that asking
 * every case gives.
 */
class AChoiceAboutPositionsNothingElseIsAboutIsAskedOnItsOwnTest {

    private static final Proposition HELD = truth("held");

    /** The positions each truth is about; a truth not put here is about none that is known. */
    private final Map<Proposition, Set<TermPath>> positions = new HashMap<>();

    private static Proposition truth(String name) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(name)), true);
    }

    /** A choice of three alternatives, each a truth about the one position {@code position}. */
    private DecidingCase.Cases choiceOf(String position) {
        List<DecidingCase.Cases> alternatives = new ArrayList<>();
        for (String each : List.of("a", "b", "c")) {
            Proposition alternative = truth(position + "." + each);
            positions.put(alternative, Set.of(TermPath.of(position)));
            alternatives.add(new DecidingCase.Cases.One(alternative));
        }
        return new DecidingCase.Cases.EachOf(alternatives);
    }

    private List<DecidingCase.Cases> choices(int count) {
        List<DecidingCase.Cases> out = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            out.add(choiceOf("p" + i));
        }
        return out;
    }

    /** What every case holds, and then {@code choices} among the rest. */
    private DecidingCase said(List<DecidingCase.Cases> choices) {
        positions.put(HELD, Set.of(TermPath.of("held")));
        List<DecidingCase.Cases> factors = new ArrayList<>();
        factors.add(new DecidingCase.Cases.One(HELD));
        factors.addAll(choices);
        return new DecidingCase(truth("said"), new DecidingCase.Cases.Together(factors));
    }

    private CasesOfALineAsked.Bearings apart(Set<TermPath> held) {
        return new CasesOfALineAsked.Bearings(positions::get, held);
    }

    /** Rows stand on both sides of the line in a condition unless it takes a blocked alternative. */
    private static boolean passes(Proposition condition, Set<Proposition> blocked) {
        return switch (condition) {
            case Proposition.All all -> all.parts().stream()
                    .allMatch(part -> passes(part, blocked));
            case Proposition.Any any -> any.parts().stream()
                    .anyMatch(part -> passes(part, blocked));
            case Proposition.Truth truth -> !blocked.contains(truth);
            case Proposition.Always always -> always.holds();
            default -> throw new IllegalArgumentException("a truth, or truths put together: "
                    + condition);
        };
    }

    /** Each case that divides rows, as the truths it chose. */
    private static Set<Set<Proposition>> leavesOf(CasesOfALineAsked.Found found) {
        Set<Set<Proposition>> out = new HashSet<>();
        for (DecidingCase each : found.decidesIn()) {
            for (Proposition leaf : DecidingCases.eachOf(each.standsFor())) {
                Set<Proposition> chosen = new HashSet<>();
                truthsOf(leaf, chosen);
                out.add(chosen);
            }
        }
        return out;
    }

    private static void truthsOf(Proposition condition, Set<Proposition> into) {
        switch (condition) {
            case Proposition.All all -> all.parts().forEach(part -> truthsOf(part, into));
            case Proposition.Truth truth -> into.add(truth);
            default -> throw new IllegalArgumentException("a truth, or truths put together: "
                    + condition);
        }
    }

    private record Asked(CasesOfALineAsked.Found found, int calls) {}

    private static Asked asked(DecidingCase said, Set<Proposition> blocked,
                               CasesOfALineAsked.Bearings apart) {
        AtomicInteger calls = new AtomicInteger();
        CasesOfALineAsked.Found found = CasesOfALineAsked.casesOf(said, condition -> {
            calls.incrementAndGet();
            return passes(condition, blocked);
        }, apart);
        return new Asked(found, calls.get());
    }

    @Test
    void choicesAboutPositionsOfTheirOwnAreAskedInTheNumberOfTheirAlternativesAddedUp() {
        DecidingCase said = said(choices(12));

        Asked asked = asked(said, Set.of(), apart(Set.of()));

        assertEquals(List.of(said), asked.found().decidesIn(), "every case divides rows, so the"
                + " case is what it was said as");
        assertTrue(asked.found().notWorkedOut().isEmpty(), "none was given up for a figure");
        assertEquals(3 * 12 + 2, asked.calls(), "what holds, each alternative of each choice once,"
                + " and the union of the cases");
    }

    @Test
    void theSameChoicesAskedWithTheRestAreMoreCasesThanAreWorkedOut() {
        Asked asked = asked(said(choices(12)), Set.of(), CasesOfALineAsked.Bearings.NEVER);

        assertTrue(asked.found().notWorkedOut()
                        .contains(CompositionBudget.CASES_A_LINE_IS_ASKED_IN),
                "twelve choices of three are more ways than the steps allow");
    }

    @Test
    void anAlternativeNoRowTakesLeavesTheCasesOfTheRestWithoutIt() {
        DecidingCase said = said(choices(4));
        Set<Proposition> blocked = Set.of(truth("p1.c"));

        Asked apart = asked(said, blocked, apart(Set.of()));
        Asked every = asked(said, blocked, CasesOfALineAsked.Bearings.NEVER);

        assertEquals(leavesOf(every.found()), leavesOf(apart.found()),
                "the cases that divide rows are the same however they are asked");
        assertEquals(3 * 2 * 3 * 3, leavesOf(apart.found()).size());
    }

    @Test
    void aChoiceNoAlternativeOfWhichAnyRowTakesLeavesNoCase() {
        Set<Proposition> blocked = Set.of(truth("p2.a"), truth("p2.b"), truth("p2.c"));

        Asked asked = asked(said(choices(5)), blocked, apart(Set.of()));

        assertTrue(asked.found().decidesIn().isEmpty());
    }

    @Test
    void aChoiceAboutAPositionTheLineIsAboutIsAskedWithTheRest() {
        DecidingCase said = said(choices(4));
        Set<TermPath> line = Set.of(TermPath.of("p1"));

        Asked apart = asked(said, Set.of(), apart(line));

        assertEquals(List.of(said), apart.found().decidesIn());
        assertEquals(1 + 1 + 3 + 3 + 9 + 9, apart.calls(), "what is chosen about the line bears"
                + " on every question after it, so each alternative of it asks the choices that"
                + " follow again, and the choice before it does not");
    }

    @Test
    void aChoiceAboutAPositionTheLineIsAboutLeavesTheCasesAskingEachCaseGives() {
        DecidingCase said = said(choices(4));
        Set<Proposition> blocked = Set.of(truth("p1.c"));
        Set<TermPath> line = Set.of(TermPath.of("p1"));

        Asked apart = asked(said, blocked, apart(line));
        Asked every = asked(said, blocked, CasesOfALineAsked.Bearings.NEVER);

        assertEquals(leavesOf(every.found()), leavesOf(apart.found()));
    }

    @Test
    void twoChoicesAboutOnePositionAreOneGroupAndWalkedTogether() {
        List<DecidingCase.Cases> both = new ArrayList<>(choices(3));
        both.add(choiceOf("p0"));
        DecidingCase said = said(both);

        Asked apart = asked(said, Set.of(), apart(Set.of()));

        assertEquals(List.of(said), apart.found().decidesIn());
        assertEquals(1 + 1 + 3 + 9 + 9 + 9, apart.calls(), "what is chosen about the position"
                + " bears on the choices after it as far as the second about it, and those"
                + " beside are asked once for each alternative chosen about it");
    }

    @Test
    void twoChoicesAboutOnePositionLeaveTheCasesAskingEachCaseGives() {
        List<DecidingCase.Cases> both = new ArrayList<>(choices(3));
        both.add(choiceOf("p0"));
        DecidingCase said = said(both);
        Set<Proposition> blocked = Set.of(truth("p0.c"));

        Asked apart = asked(said, blocked, apart(Set.of()));
        Asked every = asked(said, blocked, CasesOfALineAsked.Bearings.NEVER);

        assertEquals(leavesOf(every.found()), leavesOf(apart.found()));
    }

    /**
     * The cases of a statement of groups of parts, as they are kept when they are many: a part
     * chosen, held and then failing with another part chosen beside it, and under each the cases
     * of the groups after it, which are one and the same cases however the group before it came
     * out.
     */
    private DecidingCase.Cases decisionOver(int groups) {
        DecidingCase.Cases after = new DecidingCase.Cases.Together(List.of());
        for (int group = groups; group >= 1; group--) {
            TermPath part = TermPath.of("g" + group + ".a");
            Proposition holding = new Proposition.Truth(new DecisionSubject.AnInput(part), true);
            Proposition failing = new Proposition.Truth(new DecisionSubject.AnInput(part), false);
            Proposition other = truth("g" + group + ".b");
            Set<TermPath> at = Set.of(TermPath.of("g" + group));
            positions.put(holding, at);
            positions.put(failing, at);
            positions.put(other, at);
            after = new DecidingCase.Cases.EachOf(List.of(
                    new DecidingCase.Cases.Together(List.of(
                            new DecidingCase.Cases.One(holding), after)),
                    new DecidingCase.Cases.Together(List.of(
                            new DecidingCase.Cases.One(failing),
                            new DecidingCase.Cases.One(other), after))));
        }
        return after;
    }

    @Test
    void aDecisionOverGroupsOfPartsIsAskedInTheNumberOfPartsAddedUp() {
        DecidingCase said = said(List.of(decisionOver(12)));

        Asked asked = asked(said, Set.of(), apart(Set.of()));
        Asked every = asked(said, Set.of(), CasesOfALineAsked.Bearings.NEVER);

        assertEquals(List.of(said), asked.found().decidesIn());
        assertTrue(asked.found().notWorkedOut().isEmpty());
        assertEquals(3 * 12 + 2, asked.calls(), "three parts of each group, what holds, and the"
                + " union, whichever way the group before came out");
        assertFalse(every.found().notWorkedOut().isEmpty(), "asking each of the cases gives up on"
                + " twelve groups of two ways");
    }

    @Test
    void aDecisionOverGroupsOfPartsLeavesTheCasesAskingEachCaseGives() {
        DecidingCase said = said(List.of(decisionOver(5)));
        Set<Proposition> blocked = Set.of(truth("g3.b"));

        Asked apart = asked(said, blocked, apart(Set.of()));
        Asked every = asked(said, blocked, CasesOfALineAsked.Bearings.NEVER);

        assertEquals(leavesOf(every.found()), leavesOf(apart.found()));
        assertFalse(leavesOf(apart.found()).isEmpty());
    }

    @Test
    void aConditionNoPositionIsKnownOfIsNeverAskedApart() {
        List<DecidingCase.Cases> some = new ArrayList<>(choices(3));
        some.add(new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.One(truth("q.a")),
                new DecidingCase.Cases.One(truth("q.b")))));
        DecidingCase said = said(some);
        Set<Proposition> blocked = Set.of(truth("p1.c"));

        Asked apart = asked(said, blocked, apart(Set.of()));
        Asked every = asked(said, blocked, CasesOfALineAsked.Bearings.NEVER);

        assertEquals(leavesOf(every.found()), leavesOf(apart.found()));
        assertEquals(every.calls(), apart.calls(), "asked exactly as every case is asked");
    }

    @Test
    void casesNobodyTookApartAreNeverAskedApart() {
        List<DecidingCase.Cases> some = new ArrayList<>(choices(3));
        some.add(new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO));
        DecidingCase said = said(some);

        Asked apart = asked(said, Set.of(), apart(Set.of()));
        Asked every = asked(said, Set.of(), CasesOfALineAsked.Bearings.NEVER);

        assertEquals(every.found().notWorkedOut(), apart.found().notWorkedOut());
        assertEquals(leavesOf(every.found()), leavesOf(apart.found()));
        assertFalse(apart.found().notWorkedOut().isEmpty());
        assertEquals(every.calls(), apart.calls());
    }

    @Test
    void aGroupBesideAHeldPositionIsKeptWithTheRestAndTheOthersAreAskedOnTheirOwn() {
        DecidingCase said = said(choices(3));
        Set<Proposition> blocked = Set.of(truth("p0.a"));

        Asked apart = asked(said, blocked, apart(Set.of(TermPath.of("p2"))));
        Asked every = asked(said, blocked, CasesOfALineAsked.Bearings.NEVER);

        assertEquals(leavesOf(every.found()), leavesOf(apart.found()));
    }
}
