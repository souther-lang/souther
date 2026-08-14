package souther.compiler.check;

import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Three answers, not two: a place that can be quoted, a place this compile has no source for, and a
 * region that is not one place at all.
 *
 * <p>The middle one is ordinary. A declaration read back out of a published module was written in a
 * text this compile does not hold, and a report about it says what it can without pointing. The last
 * is not ordinary, and answering it the same way would file a value no walk of one file could
 * produce under the answer given to a published declaration — after which the only sign of it would
 * be a diagnostic that quietly stopped pointing at things.
 */
class WhetherAPlaceCanBeQuotedIsAskedBeforeItIsPointedAtTest {

    private static Region in(String sourceId) {
        return new Region(new SourcePos(3, 5, sourceId), new SourcePos(3, 20, sourceId));
    }

    @Test
    void aRegionReadOffASourceCanBeQuoted() {
        Optional<CitableRegion> citable = CitableRegion.of(in("model.sou"));

        assertTrue(citable.isPresent());
        assertEquals("model.sou", citable.get().region().start().sourceId(),
                "the region names the source, which is what makes it one to point at");
        assertEquals(in("model.sou"), citable.get().region(),
                "the region is carried as it was, not measured again");
    }

    /** What a published module's declarations come back as: written somewhere, quotable nowhere. */
    @Test
    void aRegionReadFromNoSourceCannotBeQuoted() {
        assertEquals(Optional.empty(), CitableRegion.of(in(null)));
    }

    @Test
    void nothingIsQuotableWhereThereIsNoRegion() {
        assertEquals(Optional.empty(), CitableRegion.of(null));
        assertEquals(Optional.empty(), CitableRegion.of(new Region(null, null)));
    }

    @Test
    void aRegionRunningBetweenTwoSourcesIsNotAnUnquotablePlace() {
        CitableRegion.NotOnePlace refused = assertThrows(CitableRegion.NotOnePlace.class,
                () -> CitableRegion.of(new Region(new SourcePos(3, 5, "model.sou"),
                        new SourcePos(3, 20, "other.sou"))));

        assertTrue(refused.getMessage().contains("model.sou"), refused.getMessage());
        assertTrue(refused.getMessage().contains("other.sou"), refused.getMessage());
    }

    /** The same either way round: one end knowing its source and the other not is the same broken
     *  region as two ends naming two. */
    @Test
    void aRegionWithOneEndInASourceIsRefusedToo() {
        assertThrows(CitableRegion.NotOnePlace.class,
                () -> CitableRegion.of(new Region(new SourcePos(3, 5, "model.sou"),
                        new SourcePos(3, 20))));
        assertThrows(CitableRegion.NotOnePlace.class,
                () -> CitableRegion.of(new Region(new SourcePos(3, 5),
                        new SourcePos(3, 20, "model.sou"))));
    }

    /**
     * And it is not swallowed. The check that would build one fails open — an analysis that fell
     * over leaves the run-time check standing — so an exception thrown down there is not an
     * assertion but a behavior that quietly reports nothing, which is what a behavior whose
     * invariants all discharge reports.
     */
    @Test
    void aRegionThatIsNotOnePlaceIsNotSomethingTheCheckMayGiveUpOn() {
        CitableRegion.NotOnePlace broken = new CitableRegion.NotOnePlace("a.sou", "b.sou");

        assertThrows(CitableRegion.NotOnePlace.class,
                () -> InvariantChecker.gaveUp("a test", broken));
    }
}
