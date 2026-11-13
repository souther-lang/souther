package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a {@link StatementReading} comes to for a statement is worked out once, and handed to every
 * statement above it, so what a reading costs is the statements and not the ways down to them.
 *
 * <p>Counted in the statements the work is done for: a chain that long cannot be made to take
 * longer than a clock tells from the statements, since the text a statement is spelled as is
 * bounded.
 */
class AStatementReadThroughAReadingIsReadOnceHoweverManyStatementsHoldItTest {

    private static final int LENGTH = 20;

    /** Each statement is a conjunction of the one before it and a disjunction of that and a truth
     *  of its own; the truths are this test's own. */
    private static Proposition chainOf(int length) {
        String mine = UUID.randomUUID().toString();
        Proposition held = CompoundSamples.truth(mine + "0");
        for (int at = 1; at <= length; at++) {
            held = Proposition.all(List.of(held,
                    Proposition.any(List.of(held, CompoundSamples.truth(mine + at)))));
        }
        return held;
    }

    @Test
    void aChainOfStatementsHoldingTheOneBeforeTwiceIsReadOnceForEachStatement() {
        List<Proposition> read = new ArrayList<>();
        StatementReading<Boolean> reading = StatementReading.over((stated, again) -> {
            read.add(stated);
            return stated.anyPart(again);
        });

        assertFalse(reading.read(chainOf(LENGTH)));

        // Each level is a conjunction, a disjunction and a truth, and the first is a truth.
        assertEquals(3 * LENGTH + 1, read.size());
        assertEquals(read.size(), read.stream().distinct().count(), "each once");
    }

    @Test
    void aStatementReadAgainIsNotReadAgain() {
        Proposition chain = chainOf(LENGTH);
        int[] read = {0};
        StatementReading<Boolean> reading = StatementReading.over((stated, again) -> {
            read[0]++;
            return stated.everyPart(again);
        });
        reading.read(chain);
        int once = read[0];

        reading.read(chain);

        assertEquals(once, read[0]);
    }

    @Test
    void whatEachPartComesToIsPutTogetherInTheOrderThePartsAreKept() {
        Proposition first = CompoundSamples.truth("first");
        Proposition second = CompoundSamples.truth("second");
        Proposition both = Proposition.all(List.of(first, second));
        StatementReading<String> spelled = StatementReading.over((stated, again) ->
                stated.partsHeld().isEmpty() ? stated.spelling().toString()
                        : stated.foldParts("", (so, more) -> so + "|" + more, again));

        String told = spelled.read(both);

        List<String> kept = both.partsHeld().stream().map(part -> part.spelling().toString())
                .toList();
        assertEquals("|" + kept.get(0) + "|" + kept.get(1), told);
    }

    @Test
    void aReadingThatComesToNothingIsRefusedAndNotWorkedOutAgainForEveryWayDownToIt() {
        StatementReading<String> none = StatementReading.over((stated, again) -> null);

        assertThrows(NullPointerException.class, () -> none.read(CompoundSamples.truth("t")));
    }

    @Test
    void aReadingStopsAtTheFirstPartThatAnswersAsAnyPartAsksIt() {
        Proposition first = CompoundSamples.truth("first");
        Proposition second = CompoundSamples.truth("second");
        Proposition both = Proposition.all(List.of(first, second));
        List<Proposition> read = new ArrayList<>();
        StatementReading<Boolean> reading = StatementReading.over((stated, again) -> {
            read.add(stated);
            return !stated.partsHeld().isEmpty() ? stated.anyPart(again) : true;
        });

        assertTrue(reading.read(both));

        assertEquals(2, read.size(), "the whole and the first part it asks");
    }
}
