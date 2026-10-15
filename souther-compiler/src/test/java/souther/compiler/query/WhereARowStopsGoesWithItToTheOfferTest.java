package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.FillResult;
import souther.compiler.partition.Generator;
import souther.compiler.partition.RepairShortfall;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What looking past a guard came to goes with the row through every step between the search and
 * the offer: the runs of one plan joined and renumbered, and two roads to one row joined into one
 * offered row.
 *
 * <p>Each of those steps copies the row under a new number or into a new value, and a step that
 * copied the line and left the rest behind would hand a reader a row stopping at a guard with
 * nothing said about it.
 */
class WhereARowStopsGoesWithItToTheOfferTest {

    private static final String MODEL = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, amount: Int) -> Done | Refused
                constructs Done

            let settle (kind, amount) = {
                guard amount > 0 else Refused
                match kind with
                    | Plain -> Done { n = amount }
                    | Express -> Done { n = amount + 500 }
            }
            """;

    /** The row about the class the guard refuses, which stops there. */
    private static final String STOPS = "amount=x <= 0";

    private static FillResult filled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), "example.settle");
        assertNotNull(all, "the model under test compiles");
        return all.get("settle").composed();
    }

    private static FillResult.Offer offerFor(FillResult filled, String label) {
        for (FillResult.Offer offer : filled.offers()) {
            if (offer.row().labels().contains(label)) {
                return offer;
            }
        }
        throw new AssertionError("no row is for " + label + ": " + filled.rows());
    }

    /** Joined with another run of the plan, the row is numbered afresh and still stops where it
     *  did, for the reason it did. */
    @Test
    void runsJoinedKeepWhereEachRowStops() {
        FillResult one = filled();
        RepairShortfall alone = offerFor(one, STOPS).stop();
        assertNotNull(alone, "the row stops at the guard in one run");

        FillResult joined = FillResult.acrossRuns(List.of(one, one));

        assertEquals(alone, offerFor(joined, STOPS).stop());
    }

    /** A road that brings a row with nothing to say adds nothing, and one that brings a stop adds
     *  it, however the two arrive. */
    @Test
    void twoRoadsToOneRowKeepTheStopEitherBrought() {
        FillResult.Offer stopping = offerFor(filled(), STOPS);
        Generator.GeneratedRow row = stopping.row();
        RowKey key = RowKey.of("settle", row);

        assertEquals(List.of(stopping.stop()),
                OfferedRow.of(key, row).and(row, null).and(row, stopping.stop()).stops());
        assertEquals(List.of(stopping.stop()),
                OfferedRow.of(key, row).and(row, stopping.stop()).and(row, null).stops());
    }

    /** The same stop arriving twice is said once. */
    @Test
    void oneStopArrivingTwiceIsOneStop() {
        FillResult.Offer stopping = offerFor(filled(), STOPS);
        Generator.GeneratedRow row = stopping.row();
        RowKey key = RowKey.of("settle", row);

        assertEquals(List.of(stopping.stop()), OfferedRow.of(key, row)
                .and(row, stopping.stop()).and(row, stopping.stop()).stops());
    }
}
