package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arm of a shared helper that the input type of the behavior calling it rules out is not owed a
 * row.
 *
 * <p>The helper matches the whole of {@code Stage}. What a behavior hands it is what the behavior's
 * own input type leaves, so for a behavior over {@code OpenStage} no value arrives at the arm for
 * {@code Done}, and for a behavior over {@code Stage} one does. The arm is the author's, one arm
 * with one answer for each place it stands in, and it is owed a row wherever some place can be
 * reached by a value.
 */
class AnArmTheCallersNarrowerInputRulesOutIsNotOwedARowTest {

    private static final String TYPES = """
            module probe.open
            data Draft = { n: Int }
            data Live = { n: Int }
            data Done = { n: Int }
            data Stage = Draft | Live | Done
            data OpenStage = Draft | Live

            let weightOf (s: Stage): Int =
                match s with
                    | Draft -> 1
                    | Live -> 2
                    | Done -> 3
            """;

    private static final String NARROW = TYPES + """

            behavior weigh : (s: OpenStage) -> Int
            let weigh (s) = weightOf(s)

            example weigh
                | "draft" : (Draft { n = 1 }) -> 1
                | "live" : (Live { n = 1 }) -> 2
            """;

    private static final String WIDE = TYPES + """

            behavior weigh : (s: Stage) -> Int
            let weigh (s) = weightOf(s)

            example weigh
                | "draft" : (Draft { n = 1 }) -> 1
                | "live" : (Live { n = 1 }) -> 2
            """;

    private static final String BOTH = TYPES + """

            behavior weigh : (s: OpenStage) -> Int
            let weigh (s) = weightOf(s)

            example weigh
                | "draft" : (Draft { n = 1 }) -> 1
                | "live" : (Live { n = 1 }) -> 2

            behavior weighAny : (s: Stage) -> Int
            let weighAny (s) = weightOf(s)

            example weighAny
                | "draft" : (Draft { n = 1 }) -> 1
                | "live" : (Live { n = 1 }) -> 2
            """;

    /** The input is one product, which a position states no division of. What its declaration
     *  leaves is not none of the cases of a sum it is matched as: that is an empty list found, and
     *  not a position with nothing to hold. */
    private static final String ONE_CASE = TYPES + """

            behavior weighDraft : (s: Draft) -> Int
            let weighDraft (s) = weightOf(s)

            example weighDraft
                | "draft" : (Draft { n = 1 }) -> 1
            """;

    private static String reportOn(String model) throws Exception {
        Path file = Files.createTempDirectory("souther-narrower").resolve("model.sou");
        Files.writeString(file, model);
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", file.toString()});
        } finally {
            System.setOut(was);
        }
        return out.toString(StandardCharsets.UTF_8);
    }

    @Test
    void anArmTheNarrowerInputOfItsCallerRulesOutIsNotCounted() throws Exception {
        String report = reportOn(NARROW);

        assertTrue(report.contains("branch      2/2"),
                () -> "no `OpenStage` is a `Done`, so the arm for it is not in the count:\n"
                        + report);
        assertFalse(report.contains("no row goes through"),
                () -> "and no row is asked for through it:\n" + report);
        assertTrue(report.contains("adequacy: satisfied"),
                () -> "so a strict build has nothing to refuse over:\n" + report);
    }

    /** The control. Without it the test above passes on a measure that stopped counting the arms
     *  of a helper at all, or one that dropped `Done` wherever it is matched. */
    @Test
    void theSameHelperHandedTheWholeSumStillOwesTheArm() throws Exception {
        String report = reportOn(WIDE);

        assertTrue(report.contains("branch      2/3"),
                () -> "a `Stage` is a `Done` some of the time:\n" + report);
        assertTrue(report.contains("no row goes through `case Done`"),
                () -> "and the arm for it is asked a row:\n" + report);
        assertFalse(report.contains("E1327"),
                () -> "it is no dead branch where a value reaches it:\n" + report);
    }

    /** The arm is one arm however many behaviors call the helper. Dropped for the narrower one it
     *  must stay owed for the wider, and said dead for neither. */
    @Test
    void anArmOneCallerReachesIsOwedAndIsNoDeadBranchForTheOther() throws Exception {
        String report = reportOn(BOTH);

        assertTrue(report.contains("branch      2/2") && report.contains("branch      2/3"),
                () -> "each behavior counts the arms its own input can reach:\n" + report);
        assertTrue(report.contains("no row goes through `case Done`"),
                () -> "the wider behavior is owed the row:\n" + report);
        assertFalse(report.contains("E1327"),
                () -> "an arm another call takes is not one to take out:\n" + report);
    }

    @Test
    void anInputThatStatesNoDivisionRulesNoCaseOut() throws Exception {
        String report = reportOn(ONE_CASE);

        assertFalse(report.contains("E1327"),
                () -> "a product states no cases, which says nothing of what it can be:\n"
                        + report);
        assertFalse(report.contains("no row goes through `case Draft`"),
                () -> "and the arm for the very value it holds is taken by the row:\n" + report);
    }
}
