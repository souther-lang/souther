package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.BorderObligationId;
import souther.compiler.partition.PointRole;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row for a line is looked for where each reading of that line is.
 *
 * <p>A non-recursive helper is spliced into every body that calls it, so one comparison is read once
 * per call — and each of those readings is reached under its caller's own conditions. Which
 * conditions a row has to satisfy to get there is therefore the reading's own answer, and it is the
 * region a search composes a row in.
 *
 * <p>So the readings are searched apart and brought together after. Brought together first, the
 * region a row is composed in belongs to whichever reading the fold kept, which is the one a walk
 * met first — so the row an author is offered is written for a call site nobody chose.
 *
 * <p>What the fold is still right about is the report: the readings owe one row between them, and a
 * point one of them found a row at is found.
 */
class ARowIsLookedForWhereEachReadingOfTheLineIsTest {

    /**
     * One guard called twice is two readings, one line and one row to write.
     *
     * <p>The two are what a search runs over and the one is what a report says. Both readings owe
     * the same row, which is what makes bringing them together right; what they do not share is
     * where a row for it may be composed.
     */
    @Test
    void aGuardCalledTwiceIsReadTwiceAndReportedOnce() {
        Compilation compilation = compiled();
        LineReadings read = compilation.db()
                .ask(new Adequacy.Readings("example.banding", "twice")).value();
        List<BorderAssessment> lines = compilation.db()
                .ask(new Adequacy.Boundaries("example.banding", "twice")).value();
        assertNotNull(read, "the model under test compiles");
        assertNotNull(lines, "the model under test compiles");

        List<BorderAssessment> readings = read.each();
        assertEquals(2, at(readings, "a = 100").size(),
                () -> "the helper is called from both arms, so its line is read twice: "
                        + labels(readings));
        assertEquals(1, at(lines, "a = 100").size(),
                () -> "and a report says it once: " + labels(lines));

        List<BorderObligationId> owed = at(readings, "a = 100").stream()
                .map(each -> each.border().obligation()).distinct().toList();
        assertEquals(1, owed.size(),
                () -> "both readings owe the one row the author wrote: " + owed);
    }

    /**
     * A row is still offered at a line that was read twice.
     *
     * <p>What searching the readings apart may not cost. Two searches come back where one used to
     * and the fold keeps one item per point, so a fold that kept the wrong one would leave the point
     * with nothing to offer while a row for it had been composed. The row carries a {@code side},
     * because getting to either call takes one.
     */
    @Test
    void aRowIsStillOfferedAtALineReadTwice() {
        Compilation compilation = compiled();
        List<BorderAssessment> searched = compilation.db()
                .ask(new Adequacy.BoundarySearch("example.banding", "twice")).value();
        assertNotNull(searched, "the model under test compiles");

        ItemAssessment.Owed on = assertInstanceOf(ItemAssessment.Owed.class,
                at(searched, "a = 100").get(0).at(PointRole.ON));
        ItemAssessment.Attempt.Built built = assertInstanceOf(
                ItemAssessment.Attempt.Built.class, on.attempt(),
                () -> "a row stands at the line under one of the two calls: " + on.attempt());
        List<String> row = built.row().inputs().stream()
                .map(each -> each.text()).toList();

        assertTrue(row.contains("Amount(100)"), () -> "the row is written at the line: " + row);
        assertTrue(row.contains("Left") || row.contains("Right"),
                () -> "and under the arm one of the two calls is reached by: " + row);
    }

    private static List<BorderAssessment> at(List<BorderAssessment> lines, String label) {
        return lines.stream().filter(each -> each.border().label().equals(label)).toList();
    }

    private static List<String> labels(List<BorderAssessment> lines) {
        return lines.stream().map(each -> each.border().label()).toList();
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(TWICE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** A helper called from both arms of a fork, so its comparison is read once per call. */
    private static final String TWICE = """
            module example.banding

            data Amount = Int
                invariant value >= 0

            data Small
            data Large
            data Size = Small | Large

            data Left
            data Right
            data Side = Left | Right

            let band (a: Amount): Size =
                if a.value <= 100 then Small else Large

            behavior twice : (side: Side, a: Amount) -> Size
            let twice (side, a) =
                match side with
                    | Left -> band(a)
                    | Right -> band(a)

            example twice
                | "left small" : (Left, Amount(1)) -> Small
                | "left large" : (Left, Amount(500)) -> Large
            """;
}
