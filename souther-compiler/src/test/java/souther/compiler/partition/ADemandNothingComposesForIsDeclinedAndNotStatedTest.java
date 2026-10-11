package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a way asks of an answer that nothing composes against is carried as a thing it asked and
 * could not state.
 *
 * <p>Both halves of a way travel: what could be stated is what a value is composed against, and
 * what could not is why a row composed against the rest may not take the way. Stated all the same,
 * a demand nothing meets would sit among the ones a value was built for while nothing built one for
 * it — and a way whose demands were not all met would report itself as one whose demands were all
 * stated.
 *
 * <p>Which is the same shape as a narrowing the arithmetic declines. A reading that meets something
 * it has no words for says so; it does not put the thing on the list and leave the next reader to
 * notice that nothing acted on it.
 */
class ADemandNothingComposesForIsDeclinedAndNotStatedTest {

    private static final String TYPES = """
            module example.declined

            data Reading = { ok: Bool, at: Int }
            data Yes
            data No
            data Answer = Yes | No
            """;

    /**
     * A truth of the answer itself is stated: a {@code Bool} is two values, and the demand is the
     * value.
     */
    @Test
    void aTruthOfTheWholeAnswerIsStated() {
        AnswersDemanded demanded = demandsOf(TYPES + """

                behavior permits : (at: Int) -> Bool

                behavior decides : (at: Int) -> Answer
                    depends on permits
                let decides (at, permits) = if permits(at) then Yes else No
                """);

        assertTrue(demanded.declined().isEmpty(),
                () -> "every demand of the way was stated: " + demanded);
        assertTrue(demanded.stated().stream().anyMatch(AnswerDemand.ATruth.class::isInstance),
                () -> "and the truth is one of them: " + demanded);
    }

    /**
     * And so is a truth read off a place inside the answer: the value written at that place where
     * the answer is composed.
     */
    @Test
    void aTruthOfAPlaceInsideTheAnswerIsStated() {
        AnswersDemanded demanded = demandsOf(TYPES + """

                behavior look : (at: Int) -> Reading

                behavior decides : (at: Int) -> Answer
                    depends on look
                let decides (at, look) = if look(at).ok then Yes else No
                """);

        assertTrue(demanded.declined().isEmpty(),
                () -> "every demand of the way was stated: " + demanded);
        assertEquals(List.of(List.of(new TermPath.Step.Field("ok"))),
                demanded.stated().stream()
                        .filter(AnswerDemand.ATruth.class::isInstance)
                        .map(each -> ((AnswerDemand.ATruth) each).at()).toList(),
                () -> "and the truth is of the place it was read off: " + demanded);
    }

    /**
     * A comparison of the answer with a number of the input is stated as a statement about the
     * answer, and not as a comparison over it alone.
     *
     * <p>Which value the answer may take depends on what the input holds, so what is asked of it
     * is held with the number of the input in it and the composer puts that number at a value
     * before it composes the answer — a comparison among the answer's own places is a column of it
     * and is not this.
     */
    @Test
    void aComparisonOfTheAnswerWithTheInputIsAStatementAboutTheAnswer() {
        AnswersDemanded demanded = demandsOf(TYPES + """

                behavior look : (at: Int) -> Reading

                behavior decides : (at: Int) -> Answer
                    depends on look
                let decides (at, look) = if look(at).at > at then Yes else No
                """);

        assertTrue(demanded.declined().isEmpty(),
                () -> "nothing the way asks of the answer was left unstated: " + demanded);
        assertTrue(demanded.stated().stream().allMatch(AnswerDemand.AStatement.class::isInstance),
                () -> "what it asks is a statement, with the number of the input in it: "
                        + demanded);
        assertFalse(demanded.stated().isEmpty(), () -> "and it asks something: " + demanded);
    }

    /** A comparison over what two dependencies answered is one about the pair, and says so. */
    @Test
    void aComparisonOfTwoAnswersIsDeclined() {
        AnswersDemanded demanded = demandsOf(TYPES + """

                behavior look : (at: Int) -> Reading
                behavior peek : (at: Int) -> Reading

                behavior decides : (at: Int) -> Answer
                    depends on look, peek
                let decides (at, look, peek) = if look(at).at > peek(at).at then Yes else No
                """);

        assertEquals(List.of(new DemandGap.WhyNotStated.AFormOverMoreThanOneAnswer()),
                demanded.declined().stream().map(DemandGap.Unstated::why).toList(),
                () -> "the way asks something of the pair this cannot state, and says what"
                        + " stopped it: " + demanded);
        assertTrue(demanded.stated().isEmpty(),
                () -> "and nothing is composed to it: " + demanded);
    }

    /** The demands of the first way the body states, which is where the condition is met. */
    private static AnswersDemanded demandsOf(String source) {
        List<DecisionReading.Ruled> found = DecisionReadings.of(source, "decides").found();
        assertFalse(found.isEmpty(), "the body states a way");
        return found.getFirst().demands();
    }
}
