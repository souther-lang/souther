package souther.compiler;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A fork on a value the body computed asks the input one question, and matching the input again
 * inside an arm asks it another.
 *
 * <p>Taking the {@code ClosedKind} arm of a fork on {@code cursorKind(cursor)} comes to the input
 * being a {@code ClosedCursor}. That is what the arm means for the input and no answer to the fork,
 * whose answers are {@code ClosedKind} and {@code OpenKind}; a table that read it as one has
 * a column over the kinds answered with a case of the cursor.
 */
class AForkOnAComputedValueIsAskedOfTheInputTheArmsDivideTest {

    private static final String SUMS = """
            module repro.rematched_sum_fork

            data Cursor = OpenCursor | ClosedCursor
            data Parts = InvalidParts | WholeParts
            data CursorKind = OpenKind | ClosedKind
            data PartsKind = InvalidKind | WholeKind
            data Route = Reject | Accept

            let cursorKind (cursor: Cursor): CursorKind =
                match cursor with
                    | OpenCursor -> OpenKind
                    | ClosedCursor -> ClosedKind

            let partsKind (parts: Parts): PartsKind =
                match parts with
                    | InvalidParts -> InvalidKind
                    | WholeParts -> WholeKind

            let classify (cursor: CursorKind, parts: PartsKind): Route =
                match cursor with
                    | ClosedKind -> Reject
                    | OpenKind
                        -> match parts with
                            | InvalidKind -> Reject
                            | WholeKind -> Accept

            behavior consume : (cursor: Cursor, parts: Parts) -> Route
            """;

    /** The cursor and the parts are matched again once the route has been decided. */
    @Test
    void theInputsAreMatchedAgainInsideTheRouteTheKindsDecided() {
        AdequacyReport report = reportOf(SUMS + """
                let consume (cursor, parts) =
                    match classify(cursorKind(cursor), partsKind(parts)) with
                        | Reject -> Reject
                        | Accept
                            -> match cursor with
                                | OpenCursor
                                    -> match parts with
                                        | WholeParts -> Accept
                                        | InvalidParts -> unreachable "Accept contains WholeParts"
                                | ClosedCursor -> unreachable "Accept contains OpenCursor"
                """);

        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED, report.adequacy());
        assertFalse(report.adequacyGaps().isEmpty());
    }

    /** Matching the cursor ahead of the route asks the same of the same fork. */
    @Test
    void theCursorIsMatchedBeforeTheRouteIsDecided() {
        AdequacyReport report = reportOf(SUMS + """
                let consume (cursor, parts) =
                    match cursor with
                        | ClosedCursor -> Reject
                        | OpenCursor
                            -> match classify(cursorKind(cursor), partsKind(parts)) with
                                | Reject -> Reject
                                | Accept -> Accept
                """);

        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED, report.adequacy());
    }

    /** The same fork written directly on the inputs is the control. */
    @Test
    void theInputsMatchedDirectlyAreStillReported() {
        AdequacyReport report = reportOf("""
                module repro.direct

                data Cursor = OpenCursor | ClosedCursor
                data Parts = InvalidParts | WholeParts
                data Route = Reject | Accept

                behavior consume : (cursor: Cursor, parts: Parts) -> Route
                let consume (cursor, parts) =
                    match cursor with
                        | ClosedCursor -> Reject
                        | OpenCursor
                            -> match parts with
                                | InvalidParts -> Reject
                                | WholeParts -> Accept
                """);

        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED, report.adequacy());
        assertFalse(report.adequacyGaps().isEmpty());
    }

    private static AdequacyReport reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }
}
