package souther.compiler.check;

import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.diag.WrittenAt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a region is, asked once, before anything points at it.
 *
 * <p>Four answers and not two. A place a reader can be sent to. A place this compile has no file for
 * — a declaration read back out of a published module was written in a text nobody holds — which is
 * an answer and not the absence of one: a report about it says where the code came from. A region
 * that is not one place at all, which is the compiler's model contradicting itself and is refused.
 * And a region nobody placed, which used to mean "read it in whichever file this ends up filed
 * under" and is now a caller that has not finished answering.
 *
 * <p>The middle two used to be one. Both were a null source, so every reader had to guess which it
 * had, and each of them guessed differently: a renderer read it as the diagnostic's own file, and
 * the three sites that knew better dropped the label instead.
 */
class WhetherAPlaceCanBeQuotedIsAskedBeforeItIsPointedAtTest {

    private static Region in(String sourceId) {
        return new Region(new SourcePos(3, 5, sourceId), new SourcePos(3, 20, sourceId));
    }

    /** A region read from a text put back together out of what a module published. */
    private static Region outOfSight() {
        WrittenAt out = WrittenAt.outOfSight(new SourceProvenance.APublishedModule("lib.rule"));
        return new Region(new SourcePos(3, 5).standingInFor(out),
                new SourcePos(3, 20).standingInFor(out));
    }

    @Test
    void aRegionReadOffASourceIsSomewhereAReaderIsSent() {
        DiagnosticPlace place = DiagnosticPlace.of(in("model.sou"));

        DiagnosticPlace.InSource sent = assertInstanceOf(DiagnosticPlace.InSource.class, place);
        assertEquals("model.sou", sent.source(),
                "the region names the source, which is what makes it one to point at");
        assertEquals(in("model.sou"), sent.region(),
                "the region is carried as it was, not measured again");
    }

    /** What a published module's declarations come back as: written somewhere, quotable nowhere,
     *  and saying which somewhere rather than saying nothing. */
    @Test
    void aRegionOutOfSightSaysWhereTheCodeCameFrom() {
        DiagnosticPlace place = DiagnosticPlace.of(outOfSight());

        assertEquals(new SourceProvenance.APublishedModule("lib.rule"),
                assertInstanceOf(DiagnosticPlace.Unavailable.class, place).provenance());
        assertTrue(place.pointsAt().isEmpty(), "and there is nowhere to send a reader");
    }

    /**
     * A region nobody placed is refused rather than answered.
     *
     * <p>It reads exactly like the one above — a null source — and it is a different thing. Reading
     * the two as one is what put a label about a clause of {@code lib.rule} on a line of the file
     * the caller was compiling.
     */
    @Test
    void aRegionNamingNoSourceAndClaimingToBeThePlaceIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> DiagnosticPlace.of(in(null)));
    }

    @Test
    void aRegionRunningBetweenTwoSourcesIsNotAPlaceAtAll() {
        DiagnosticPlace.NotOnePlace refused = assertThrows(DiagnosticPlace.NotOnePlace.class,
                () -> DiagnosticPlace.of(new Region(new SourcePos(3, 5, "model.sou"),
                        new SourcePos(3, 20, "other.sou"))));

        assertTrue(refused.getMessage().contains("model.sou"), refused.getMessage());
        assertTrue(refused.getMessage().contains("other.sou"), refused.getMessage());
    }

    /** The same either way round: one end knowing its source and the other not is the same broken
     *  region as two ends naming two. */
    @Test
    void aRegionWithOneEndInASourceIsRefusedToo() {
        assertThrows(DiagnosticPlace.NotOnePlace.class,
                () -> DiagnosticPlace.of(new Region(new SourcePos(3, 5, "model.sou"),
                        new SourcePos(3, 20))));
        assertThrows(DiagnosticPlace.NotOnePlace.class,
                () -> DiagnosticPlace.of(new Region(new SourcePos(3, 5),
                        new SourcePos(3, 20, "model.sou"))));
    }

    /**
     * And it is not swallowed. The check that would build one fails open — an analysis that fell
     * over leaves the run-time check standing — so an exception thrown down there is not an
     * assertion but a behavior that quietly reports nothing, which is what a behavior whose
     * invariants all discharge reports.
     *
     * <p>Asked of what the failure is and not of which ones the boundary has met. The refusal is
     * raised where regions become places and the others are raised where clauses are read, which is
     * two layers and one question ({@code TheCompilerDisagreesWithItself}).
     */
    @Test
    void aRegionThatIsNotOnePlaceIsNotSomethingTheCheckMayGiveUpOn() {
        DiagnosticPlace.NotOnePlace broken = assertThrows(DiagnosticPlace.NotOnePlace.class,
                () -> DiagnosticPlace.of(new Region(new SourcePos(1, 1, "a.sou"),
                        new SourcePos(1, 9, "b.sou"))));

        assertThrows(DiagnosticPlace.NotOnePlace.class,
                () -> InvariantChecker.gaveUp("a test", broken));
    }
}
