package souther.compiler.types;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reading was read on is a set of applications: put together, readings keep every
 * application of each whatever order they are put together in, and an application no source's call
 * made is nothing a reading is said to be read on. Counted by call, the readings a call's
 * applications made and the applications that made some are two numbers, neither standing for the
 * other.
 */
class TheApplicationsReadingsWereReadOnArePutTogetherAndCountedByCallTest {

    private static ACallOfAnOperation call(int construct) {
        return new ACallOfAnOperation(new ValueName.Stdlib.Operation("List", "fold"),
                new ConstructOccurrence(SourceConstructOrigin.written(
                        new WrittenOwner.Body("m", "f"), construct, SourceConstruct.CALL),
                        OccurrenceLineage.ORIGINAL));
    }

    private static final ACallOfAnOperation OUTER = call(1);
    private static final ACallOfAnOperation INNER = call(2);

    private static AnApplicationOfAClosure of(ACallOfAnOperation call, int ordinal) {
        return AnApplicationOfAClosure.OF_NO_CALL_WRITTEN.inside(
                new AnApplicationOfAClosure.Made(call, ordinal));
    }

    private static AnApplicationOfAClosure inner(int outer, int inner) {
        return of(OUTER, outer).inside(new AnApplicationOfAClosure.Made(INNER, inner));
    }

    private static ApplicationsReadOn on(AnApplicationOfAClosure... each) {
        return ApplicationsReadOn.of(List.of(each));
    }

    @Test
    void readingsPutTogetherKeepEveryApplicationInWhateverOrder() {
        List<ApplicationsReadOn> some = List.of(on(of(OUTER, 0)), on(of(OUTER, 1), of(OUTER, 0)),
                on(inner(0, 0)), ApplicationsReadOn.NONE, on(inner(1, 0), of(OUTER, 2)));
        for (ApplicationsReadOn a : some) {
            assertEquals(a, a.and(a), "putting a reading with itself adds nothing");
            assertEquals(a, a.and(ApplicationsReadOn.NONE));
            assertEquals(a, ApplicationsReadOn.NONE.and(a));
            for (ApplicationsReadOn b : some) {
                assertEquals(a.and(b), b.and(a), "in either order");
                assertTrue(a.and(b).each().containsAll(a.each())
                        && a.and(b).each().containsAll(b.each()), "every application of each");
                for (ApplicationsReadOn c : some) {
                    assertEquals(a.and(b).and(c), a.and(b.and(c)));
                }
            }
        }
    }

    @Test
    void anApplicationNoSourcesCallMadeIsNotSaid() {
        assertEquals(ApplicationsReadOn.NONE,
                on(AnApplicationOfAClosure.OF_NO_CALL_WRITTEN));
        assertEquals(Set.of(of(OUTER, 0)),
                on(AnApplicationOfAClosure.OF_NO_CALL_WRITTEN, of(OUTER, 0)).each());
        assertEquals(List.of(), ApplicationsReadOn.byCall(List.of(ApplicationsReadOn.NONE)));
    }

    /** Two applications reading one line at one place are one reading of two applications; one
     *  application reading two lines is two readings of one. */
    @Test
    void aCallsApplicationsAndItsReadingsAreCountedApart() {
        assertEquals(List.of(new ApplicationsReadOn.OfACall(OUTER, 2, 1)),
                ApplicationsReadOn.byCall(List.of(on(of(OUTER, 0), of(OUTER, 1)))));
        assertEquals(List.of(new ApplicationsReadOn.OfACall(OUTER, 1, 2)),
                ApplicationsReadOn.byCall(List.of(on(of(OUTER, 0)), on(of(OUTER, 0)))));
    }

    /**
     * The first application of the inner call inside the outer one's first and inside its second
     * are two applications, and a reading read inside an application of the outer call is a
     * reading of the outer call too.
     */
    @Test
    void anApplicationOfANestedCallIsToldApartByTheApplicationsAroundIt() {
        assertEquals(List.of(new ApplicationsReadOn.OfACall(OUTER, 2, 2),
                        new ApplicationsReadOn.OfACall(INNER, 2, 2)),
                ApplicationsReadOn.byCall(List.of(on(inner(0, 0)), on(inner(1, 0)))));
        assertEquals(List.of(new ApplicationsReadOn.OfACall(OUTER, 1, 1),
                        new ApplicationsReadOn.OfACall(INNER, 2, 1)),
                ApplicationsReadOn.byCall(List.of(on(inner(0, 0), inner(0, 1)))));
    }
}
