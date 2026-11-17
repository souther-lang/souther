package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
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
 * <p>Dates are values spaced a day apart, so a date is left either way where some value of the
 * number puts the difference at both sides of it. A number tied to the dates by a rule, or narrowed
 * on the way, still takes such values, and the controls below hold each of the two.
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
    void aThresholdTiedToTheDatesByARuleLeavesAllThreePlacesUndivided() {
        assertEquals(3, relatingTwoValues("tied"),
                "the number is kept within how many dates there are, and each date is still at"
                        + " both sides of some value of it");
    }

    @Test
    void aThresholdTheWayNarrowsLeavesAllThreePlacesUndivided() {
        assertEquals(3, relatingTwoValues("narrowed"),
                "the way keeps the number to seven or more, and each date is still at both sides"
                        + " of some value of it");
    }

    /** How many places a rule of {@code behavior} is said to leave undivided by relating two
     *  values. */
    private static long relatingTwoValues(String behavior) {
        Compilation compilation = ACompiledModel.measured(DECLARED, Adequacy.Asked.fullReport());
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get(behavior);
        assertNotNull(evidence, "the model under test compiles");
        return evidence.rulesWithoutALine().stream().map(RuleWithoutALine::why)
                .filter(why -> why instanceof BlockReason.ComparisonRelatingTwoValues).count();
    }
}
