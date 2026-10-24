package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.FillResult;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The rows a block holds are counted once for each stimulus, whichever search composed them.
 *
 * <p>The room a search that follows the fill is told it has is the block's: a row a line and a case
 * arrive at alike is one row of it, and a count of what each search composed would count it twice
 * and stop the block short of rows it has room for, or, counting only the rows beside it, take
 * room the others already took.
 */
class ABlocksRowsAreCountedOncePerStimulusTest {

    @Test
    void aRowTwoSourcesComposedCountsOnce() {
        Generator.GeneratedRow one = row(1);
        Generator.GeneratedRow another = row(2);

        assertEquals(2, Composition.stimuliBetween("f", List.of(),
                List.of(List.of(one), List.of(one, another))).size(),
                "the row a line and a case both composed is one row of the block");
    }

    @Test
    void theFillsRowsAndTheOthersAreOneCount() {
        Generator.GeneratedRow one = row(1);
        Generator.GeneratedRow another = row(2);

        assertEquals(2, Composition.stimuliBetween("f",
                List.of(new FillResult.Offer(one, null)), List.of(List.of(another, one))).size(),
                "a row the fill composed and a line also did is one row");
        assertEquals(3, Composition.stimuliBetween("f",
                List.of(new FillResult.Offer(one, null)),
                List.of(List.of(another), List.of(row(3)))).size(),
                "and rows apart are rows apart");
    }

    @Test
    void nothingComposedIsNoRoomTaken() {
        assertEquals(0, Composition.stimuliBetween("f", List.of(), List.of(List.of())).size(),
                "no row is no room taken");
    }

    private static Generator.GeneratedRow row(long n) {
        return new Generator.GeneratedRow(List.of(new Generator.Purpose.Unstated()),
                List.of(FixtureTemplate.integer(n)), List.of());
    }
}
