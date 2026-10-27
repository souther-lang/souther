package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How far apart two dates are, held against a number the input states, parts none of the three
 * places.
 *
 * <p>The number is held at one value it takes, and the rows with it there are rows of the model: a
 * date left either way among them is left either way. That is read only where the number stands
 * apart from both dates and nothing the way states bears on it — the controls below hold each of
 * the two, since a number tied to a date or narrowed on the way may not take the value it was
 * held at.
 */
class ADifferenceHeldAgainstAThresholdIsReadWithTheThresholdHeldStillTest {

    private static final String DECLARED = """
            module example.threshold

            data Cadence = Int
                invariant value >= 1

            data Book = { dates: List<Date>, staleAfter: Int }
                invariant staleAfter >= 1
                invariant staleAfter <= List.length(dates)

            behavior apart : (dates: List<Date>, today: Date, staleAfter: Cadence) -> List<Date>

            let apart (dates, today, staleAfter) =
                List.filter(d -> Date.daysBetween(d, today) >= staleAfter.value, dates)

            behavior tied : (book: Book, today: Date) -> List<Date>

            let tied (book, today) =
                List.filter(d -> Date.daysBetween(d, today) >= book.staleAfter, book.dates)

            behavior narrowed : (dates: List<Date>, today: Date, staleAfter: Cadence)
                    -> List<Date>

            let narrowed (dates, today, staleAfter) =
                if staleAfter.value >= 7
                    then List.filter(d -> Date.daysBetween(d, today) >= staleAfter.value, dates)
                    else []
            """;

    @Test
    void aThresholdApartFromBothDatesLeavesAllThreePlacesUndivided() {
        assertEquals(3, relatingTwoValues("apart"),
                "the dates, and the number held against how far apart they are");
    }

    @Test
    void aThresholdTiedToTheDatesByARuleIsNotHeldStill() {
        assertEquals(1, relatingTwoValues("tied"),
                "the number is kept within how many dates there are, so it is not apart from them:"
                        + " only the number is read, as it was");
    }

    @Test
    void aThresholdTheWayNarrowsIsNotHeldStill() {
        assertEquals(1, relatingTwoValues("narrowed"),
                "only the number is read, as it was: the way keeps it from the value held");
    }

    /** How many places a rule of {@code behavior} is said to leave undivided by relating two
     *  values. */
    private static long relatingTwoValues(String behavior) {
        Compilation compilation = Compilation.ofSource(DECLARED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get(behavior);
        assertNotNull(evidence, "the model under test compiles");
        return evidence.rulesWithoutALine().stream().map(RuleWithoutALine::why)
                .filter(why -> why instanceof BlockReason.ComparisonRelatingTwoValues).count();
    }
}
