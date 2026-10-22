package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Asked of each case a condition was said for, with nothing given up on the strength of another.
 *
 * <p>A line fixed beforehand is crossed by no more rows in a narrower case than in a wider one,
 * which is what lets {@link CasesOfALineAsked#casesOf} stop at a case. What parts the values a
 * relation settles is read off the rows in a case, so a narrower case can part values a wider one
 * does not, and what is asked of it has to be asked of every case, to the end.
 */
class WhatIsAskedOfEachCaseIsKeptForTheCallerTest {

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    private static final Proposition A = truth("a");
    private static final Proposition B = truth("b");
    private static final Proposition C = truth("c");
    private static final Proposition D = truth("d");
    private static final Proposition SAID = truth("said");

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

    /** Asks, answering each condition by {@code answer} and keeping what was asked. */
    private record Asking<T>(Function<Proposition, T> answer, List<Proposition> asked) {

        Asking(Function<Proposition, T> answer) {
            this(answer, new ArrayList<>());
        }

        CasesOfALineAsked.Atoms<T> of(DecidingCase.Cases cases) {
            return CasesOfALineAsked.atomsOf(new DecidingCase(SAID, cases), condition -> {
                asked.add(condition);
                return answer.apply(condition);
            });
        }
    }

    /**
     * An answer found only in a narrow case is found: the wider cases it is part of are not asked
     * first, and not asked at all, since nothing about them is a reason to leave it unasked.
     */
    @Test
    void anAnswerFoundOnlyInANarrowCaseIsFound() {
        Set<Proposition> parts = Set.of(both(A, C), both(B, D));
        Asking<Boolean> asking = new Asking<>(parts::contains);

        CasesOfALineAsked.Atoms<Boolean> atoms = asking.of(FOUR);

        assertEquals(List.of(both(A, C), both(A, D), both(B, C), both(B, D)), asking.asked(),
                "every case chosen to the end, and nothing asked of a part of one");
        assertEquals(List.of(true, false, false, true),
                atoms.each().stream().map(CasesOfALineAsked.Atom::answer).toList());
        assertEquals(Set.of(), atoms.notWorkedOut());
    }

    /** Each case keeps the answer it came to, so that cases are said together only by the caller,
     *  and only where their answers are one. */
    @Test
    void eachCaseKeepsItsOwnAnswer() {
        CasesOfALineAsked.Atoms<String> atoms = new Asking<String>(condition ->
                condition.equals(both(A, C)) || condition.equals(both(A, D)) ? "ten" : "twenty")
                .of(FOUR);

        assertEquals(List.of("ten", "ten", "twenty", "twenty"),
                atoms.each().stream().map(CasesOfALineAsked.Atom::answer).toList());
        assertEquals(List.of(both(A, C), both(A, D), both(B, C), both(B, D)),
                atoms.each().stream().map(CasesOfALineAsked.Atom::condition).toList());
    }

    /** A case said for itself is asked as it was said. */
    @Test
    void aCaseSaidAloneIsAskedAsItIs() {
        Asking<String> asking = new Asking<>(_ -> "here");

        CasesOfALineAsked.Atoms<String> atoms = asking.of(one(SAID));

        assertEquals(List.of(SAID), asking.asked());
        assertEquals(List.of(new CasesOfALineAsked.Atom<>(SAID, "here")), atoms.each());
    }

    /** More ways of choosing a case than cases are taken apart are not asked, and say so. */
    @Test
    void moreWaysOfChoosingThanAreTakenApartAreNotAsked() {
        int count = CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum() + 1;
        List<DecidingCase.Cases> many = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            many.add(one(truth("t" + i)));
        }
        Asking<Boolean> asking = new Asking<>(_ -> true);

        CasesOfALineAsked.Atoms<Boolean> atoms = asking.of(new DecidingCase.Cases.EachOf(many));

        assertEquals(List.of(), atoms.each());
        assertEquals(List.of(), asking.asked());
        assertEquals(Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO),
                atoms.notWorkedOut());
    }

    /** The cases walked to are kept beside the figure the others were stopped at. */
    @Test
    void whatWasWalkedToIsKeptBesideWhatStoppedTheRest() {
        DecidingCase.Cases readTooLong = new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN);

        CasesOfALineAsked.Atoms<Boolean> atoms = new Asking<Boolean>(_ -> true).of(
                new DecidingCase.Cases.EachOf(List.of(readTooLong, one(A))));

        assertEquals(List.of(new CasesOfALineAsked.Atom<>(A, true)), atoms.each());
        assertEquals(Set.of(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN),
                atoms.notWorkedOut());
    }
}
