package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Which readings a declaration is named by, asked of the readings alone.
 *
 * <p>The counterfactuals are stated here rather than read out of a model, so that every answer, and
 * every rule that tells two of them apart, stays observable where the compiler's own models do not
 * reach it. A rule nothing observes is a rule the next reader is free to write a different way.
 *
 * <p>Every reading asked for is one this states, so a question put to a set of declarations that is
 * not the set the rule names fails here rather than answering.
 */
class WhatNamesADeclarationAtAnEndIsTheDifferenceItMadeTest {

    private static final TypeSymbol.AtModule A = named("A");

    private static final TypeSymbol.AtModule B = named("B");

    private static final TypeSymbol.AtModule C = named("C");

    private static final Endpoint TWENTY = Endpoint.inclusive(Count.of(20));

    private static final Endpoint THIRTY = Endpoint.inclusive(Count.of(30));

    private static final Endpoint FIFTY = Endpoint.inclusive(Count.of(50));

    /**
     * Where the end is where it is without any of them, none of them is named.
     *
     * <p>And no further reading is asked for. What each of them would do on its own is a question
     * about a difference, and there is none here to divide up.
     */
    @Test
    void whereTheyLeaveTheEndWhereItIsNobodyIsNamed() {
        EndNarrowing.Answer<TypeSymbol.AtModule> answer = EndNarrowing.read(TWENTY, List.of(A, B),
                reading(Map.of(Set.of(A, B), TWENTY)));

        assertInstanceOf(EndNarrowing.Answer.NoNarrowing.class, answer,
                "the clauses reached a value something else had already stopped it at");
        assertEquals(List.of(), answer.names());
    }

    /** The one the end moves without is named, and the one it does not is left out. */
    @Test
    void theOneTheEndMovesWithoutIsNamed() {
        EndNarrowing.Answer<TypeSymbol.AtModule> answer = EndNarrowing.read(TWENTY, List.of(A, B),
                reading(Map.of(
                        Set.of(A, B), FIFTY,
                        Set.of(A), FIFTY,
                        Set.of(B), TWENTY)));

        assertEquals(new EndNarrowing.Answer.Indispensable<>(List.of(A)), answer,
                "taking A away moves the end and taking B away leaves it");
    }

    /**
     * Where neither is missed on its own, the ones that reach the end alone are named.
     *
     * <p>Both of them here, which is what two declarations saying what the edge says comes to. One
     * of them is no more the answer than the other.
     */
    @Test
    void whereNeitherIsMissedTheOnesReachingTheEndAloneAreNamed() {
        EndNarrowing.Answer<TypeSymbol.AtModule> answer = EndNarrowing.read(TWENTY, List.of(A, B),
                reading(Map.of(
                        Set.of(A, B), FIFTY,
                        Set.of(A), TWENTY,
                        Set.of(B), TWENTY)));

        assertEquals(new EndNarrowing.Answer.AloneSufficient<>(List.of(A, B)), answer,
                "each of them leaves the end where it is with the other gone");
    }

    /**
     * Reaching the end and moving it are not the same question.
     *
     * <p>{@code C} left alone leaves the end at thirty, which is neither where the three of them put
     * it nor where none of them does. It moved something and it does not say what the edge says, and
     * an author sent to it would be sent to a clause that cannot put the end at twenty.
     */
    @Test
    void oneThatMovesTheEndWithoutReachingItIsNotNamed() {
        EndNarrowing.Answer<TypeSymbol.AtModule> answer = EndNarrowing.read(TWENTY, List.of(A, B, C),
                reading(Map.of(
                        Set.of(A, B, C), FIFTY,
                        Set.of(A), TWENTY,
                        Set.of(B), TWENTY,
                        Set.of(C), TWENTY,
                        Set.of(B, C), TWENTY,
                        Set.of(A, C), TWENTY,
                        Set.of(A, B), THIRTY)));

        assertEquals(new EndNarrowing.Answer.AloneSufficient<>(List.of(A, B)), answer,
                "C alone stops short of the end, and stopping short is not saying it");
    }

    /**
     * Where neither question tells them apart, the set is the answer.
     *
     * <p>Any two of these reach the end and no one of them does, so what is known is that the three
     * of them account for it. That is what this says, and it is not that each of them moved it.
     */
    @Test
    void whereNeitherQuestionTellsThemApartTheSetIsTheAnswer() {
        EndNarrowing.Answer<TypeSymbol.AtModule> answer = EndNarrowing.read(TWENTY, List.of(A, B, C),
                reading(Map.of(
                        Set.of(A, B, C), FIFTY,
                        Set.of(A), TWENTY,
                        Set.of(B), TWENTY,
                        Set.of(C), TWENTY,
                        Set.of(B, C), THIRTY,
                        Set.of(A, C), THIRTY,
                        Set.of(A, B), THIRTY)));

        assertEquals(new EndNarrowing.Answer.Undifferentiated<>(List.of(A, B, C)), answer,
                "any two of them reach it and no one of them does");
    }

    /**
     * Where nothing stops the coordinate without them, that absence is the difference.
     *
     * <p>A reading with no end on the side is a wider one and not a missing answer, and the
     * candidates are the whole of why the coordinate stops anywhere at all. Read as an end that
     * could not be worked out, it would say they left it where it was.
     */
    @Test
    void whereNothingStopsItWithoutThemThatAbsenceIsTheDifference() {
        EndNarrowing.Answer<TypeSymbol.AtModule> answer = EndNarrowing.read(TWENTY, List.of(A, B),
                removed -> removed.equals(Set.of(A, B)) ? null : TWENTY);

        assertEquals(new EndNarrowing.Answer.AloneSufficient<>(List.of(A, B)), answer,
                "with neither of them the coordinate stops nowhere, and it stops at twenty");
    }

    /** The ends these readings come to, and an error for a reading nothing here states. */
    private static EndNarrowing.Ends<TypeSymbol.AtModule> reading(
            Map<Set<TypeSymbol.AtModule>, Endpoint> ends) {
        return removed -> {
            Endpoint found = ends.get(removed);
            if (found == null) {
                throw new AssertionError("no reading stated for a walk without " + removed);
            }
            return found;
        };
    }

    private static TypeSymbol.AtModule named(String name) {
        return TypeSymbols.declared(new TypeKey("example.narrowing", name));
    }
}
