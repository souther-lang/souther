package souther.compiler.types;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;
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

    private static AnApplicationOfAClosure.Made made(ACallOfAnOperation call, int ordinal) {
        return AnApplicationOfAClosure.Made.of(call, ordinal).orElseThrow();
    }

    private static AnApplicationOfAClosure of(ACallOfAnOperation call, int ordinal) {
        return new AnApplicationOfAClosure(List.of(made(call, ordinal)));
    }

    private static AnApplicationOfAClosure inner(int outer, int inner) {
        return new AnApplicationOfAClosure(List.of(made(OUTER, outer), made(INNER, inner)));
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

    private static ApplicationsReadOn.OfACall counted(ACallOfAnOperation call, int applications,
                                                      int readings) {
        return new ApplicationsReadOn.OfACall(call, made(call, 0).construct(), applications,
                readings);
    }

    /** Two applications reading one line at one place are one reading of two applications; one
     *  application reading two lines is two readings of one. */
    @Test
    void aCallsApplicationsAndItsReadingsAreCountedApart() {
        assertEquals(List.of(counted(OUTER, 2, 1)),
                ApplicationsReadOn.byCall(List.of(on(of(OUTER, 0), of(OUTER, 1)))));
        assertEquals(List.of(counted(OUTER, 1, 2)),
                ApplicationsReadOn.byCall(List.of(on(of(OUTER, 0)), on(of(OUTER, 0)))));
    }

    /**
     * The first application of the inner call inside the outer one's first and inside its second
     * are two applications, and a reading read inside an application of the outer call is a
     * reading of the outer call too.
     */
    @Test
    void anApplicationOfANestedCallIsToldApartByTheApplicationsAroundIt() {
        assertEquals(List.of(counted(OUTER, 2, 2), counted(INNER, 2, 2)),
                ApplicationsReadOn.byCall(List.of(on(inner(0, 0)), on(inner(1, 0)))));
        assertEquals(List.of(counted(OUTER, 1, 1), counted(INNER, 2, 1)),
                ApplicationsReadOn.byCall(List.of(on(inner(0, 0), inner(0, 1)))));
    }

    /**
     * A call written inside one of the language's own operations is no call of the model: an
     * application is not told by it, and is told by the calls of the model around it all the
     * same.
     */
    @Test
    void aCallInsideALanguagesOwnOperationTellsNoApplication() {
        ConstructOccurrence insideTheLibrary = new ConstructOccurrence(
                SourceConstructOrigin.written(new WrittenOwner.Body("m", "f"), 3,
                        SourceConstruct.CALL),
                new OccurrenceLineage.Expansion(OccurrenceLineage.ORIGINAL,
                        new ValueName.Stdlib.Operation("List", "sum"),
                        new ExpansionSite.Written(SourceConstructOrigin.written(
                                new WrittenOwner.Body("m", "f"), 4, SourceConstruct.CALL))));
        ACallOfAnOperation library = new ACallOfAnOperation(
                new ValueName.Stdlib.Operation("List", "fold"), insideTheLibrary);
        assertEquals(Optional.empty(), AnApplicationOfAClosure.Made.of(library, 0));
        assertEquals(OUTER, made(OUTER, 0).call());
    }
}
