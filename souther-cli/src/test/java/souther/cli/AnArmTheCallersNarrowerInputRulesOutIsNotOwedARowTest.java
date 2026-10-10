package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
 *
 * <p>What the type says a value can be is asked as such: a record is the one case it is, a newtype
 * over a sum is the cases of the sum, and a sum inside a sum is its leaves. Where the declaration
 * says nothing this can follow — an optional — nothing is ruled out.
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

    /** The input is one record. It divides into nothing, and it is the one case it is: the arm for
     *  its own case is the only one a value arrives at. */
    private static final String ONE_CASE = TYPES + """

            behavior weighDraft : (s: Draft) -> Int
            let weighDraft (s) = weightOf(s)

            example weighDraft
                | "draft" : (Draft { n = 1 }) -> 1
            """;

    /** A newtype over a sum is the cases of the sum under its name. */
    private static final String NEWTYPE = TYPES + """

            data OpenOnly = OpenStage

            behavior weigh : (s: OpenOnly) -> Int
            let weigh (s) = weightOf(s.value)

            example weigh
                | "draft" : (OpenOnly(Draft { n = 1 })) -> 1
                | "live" : (OpenOnly(Live { n = 1 })) -> 2
            """;

    /** An arm over the inner sum of a sum is entered by any of its leaves the input holds. */
    private static final String NESTED = """
            module probe.nested
            data Station
            data Hospital
            data Renkei
            data OnceKind = Station | Hospital
            data VisitKind = OnceKind | Renkei
            data NotStation = Hospital | Renkei

            let rank (k: VisitKind): Int =
                match k with
                    | Station -> 1
                    | Hospital -> 2
                    | Renkei -> 3

            let rankOnce (k: VisitKind): Int =
                match k with
                    | OnceKind -> 1
                    | Renkei -> 2

            behavior byLeaf : (k: NotStation) -> Int
            let byLeaf (k) = rank(k)

            example byLeaf
                | "hospital" : (Hospital) -> 2
                | "renkei" : (Renkei) -> 3

            behavior byInnerSum : (k: NotStation) -> Int
            let byInnerSum (k) = rankOnce(k)

            example byInnerSum
                | "hospital" : (Hospital) -> 1
                | "renkei" : (Renkei) -> 2
            """;

    /** What a helper answers is read off the arms of the helper that answer it, so the cases of
     *  the value matched are those of the helper's arms; the position matched on is none. */
    private static final String ANSWERED = """
            module probe.kind
            data Draft = { n: Int }
            data Live = { n: Int }
            data Done = { n: Int }
            data Lost = { n: Int }
            data Stage = Draft | Live | Done | Lost
            data OpenStage = Draft | Live
            data Pending
            data Settled
            data Kind = Pending | Settled

            let kindOf (s: Stage): Kind =
                match s with
                    | Draft -> Pending
                    | Live -> Pending
                    | Done -> Settled
                    | Lost -> Settled

            behavior weigh : (s: OpenStage) -> Int
            let weigh (s) =
                match kindOf(s) with
                    | Pending -> 1
                    | Settled -> 2

            example weigh
                | "draft" : (Draft { n = 1 }) -> 1
                | "live" : (Live { n = 1 }) -> 1
            """;

    /** An optional is a position the declaration does not say the cases of this way, so the arms
     *  over it are owed rows however narrow what it holds. */
    private static final String AN_OPTIONAL = TYPES + """

            data Box = { stage: OpenStage? }

            let present (s: Stage?): Int =
                match s with
                    | Some stage -> weightOf(stage)
                    | None -> 0

            behavior weigh : (b: Box) -> Int
            let weigh (b) = present(b.stage)

            example weigh
                | "none" : (Box { stage = None }) -> 0
            """;

    /** What a list holds is each of its elements. */
    private static final String AN_ELEMENT = TYPES + """

            behavior total : (stages: List<OpenStage>) -> Int
            let total (stages) = List.sum(List.map(stage -> weightOf(stage), stages))

            example total
                | "both" : ([ Draft { n = 1 }, Live { n = 1 } ]) -> 3
            """;

    private record Output(String report, String warnings, int exit) {}

    private static Output run(String model, boolean strict) throws Exception {
        Path file = Files.createTempDirectory("souther-narrower").resolve("model.sou");
        Files.writeString(file, model);
        PrintStream out = System.out;
        PrintStream err = System.err;
        ByteArrayOutputStream said = new ByteArrayOutputStream();
        ByteArrayOutputStream warned = new ByteArrayOutputStream();
        System.setOut(new PrintStream(said, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(warned, true, StandardCharsets.UTF_8));
        int exit;
        try {
            exit = Main.dispatch(strict
                    ? new String[] {"examples", "--strict", file.toString()}
                    : new String[] {"examples", file.toString()});
        } finally {
            System.setOut(out);
            System.setErr(err);
        }
        return new Output(said.toString(StandardCharsets.UTF_8),
                warned.toString(StandardCharsets.UTF_8), exit);
    }

    private static String reportOn(String model) throws Exception {
        return run(model, false).report();
    }

    @Test
    void anArmTheNarrowerInputOfItsCallerRulesOutIsNotCounted() throws Exception {
        Output output = run(NARROW, true);

        assertTrue(output.report().contains("branch      2/2"),
                () -> "no `OpenStage` is a `Done`, so the arm for it is not in the count:\n"
                        + output.report());
        assertFalse(output.report().contains("no row goes through"),
                () -> "and no row is asked for through it:\n" + output.report());
        assertTrue(output.report().contains("adequacy: satisfied"),
                () -> "so a strict build has nothing to refuse over:\n" + output.report());
        assertEquals(0, output.exit(), () -> "and a strict build succeeds:\n" + output.report());
    }

    /** The control. Without it the test above passes on a measure that stopped counting the arms
     *  of a helper at all, or one that dropped `Done` wherever it is matched. */
    @Test
    void theSameHelperHandedTheWholeSumStillOwesTheArm() throws Exception {
        Output output = run(WIDE, true);

        assertTrue(output.report().contains("branch      2/3"),
                () -> "a `Stage` is a `Done` some of the time:\n" + output.report());
        assertTrue(output.report().contains("no row goes through `case Done`"),
                () -> "and the arm for it is asked a row:\n" + output.report());
        assertFalse(output.warnings().contains("E1327"),
                () -> "it is no dead branch where a value reaches it:\n" + output.warnings());
        assertEquals(1, output.exit(), "and a strict build refuses over it");
    }

    /** The arm is one arm however many behaviors call the helper. Dropped for the narrower one it
     *  must stay owed for the wider, and said dead for neither. */
    @Test
    void anArmOneCallerReachesIsOwedAndIsNoDeadBranchForTheOther() throws Exception {
        Output output = run(BOTH, false);

        assertTrue(output.report().contains("branch      2/2")
                        && output.report().contains("branch      2/3"),
                () -> "each behavior counts the arms its own input can reach:\n"
                        + output.report());
        assertTrue(output.report().contains("no row goes through `case Done`"),
                () -> "the wider behavior is owed the row:\n" + output.report());
        assertFalse(output.warnings().contains("E1327"),
                () -> "an arm another call takes is not one to take out:\n" + output.warnings());
    }

    @Test
    void aRecordInputIsTheOneCaseItIsAndRulesTheOthersOut() throws Exception {
        Output output = run(ONE_CASE, true);

        assertTrue(output.report().contains("branch      1/1"),
                () -> "the one case a `Draft` can be is the only arm owed a row:\n"
                        + output.report());
        assertFalse(output.report().contains("no row goes through"),
                () -> "and the row for it covers it:\n" + output.report());
        assertTrue(output.report().contains("adequacy: satisfied"), () -> output.report());
        assertEquals(0, output.exit(), () -> output.report());
        // Said by what the type declares, which is the reason it holds whatever the rules are: the
        // first arm takes the one case there is, and nothing is left for the arms after it.
        assertTrue(output.warnings().contains("declared as Draft"),
                () -> "the author is told what the position is declared as:\n"
                        + output.warnings());
        assertTrue(output.warnings().contains("the arms before this one take Draft"),
                () -> "and that the arms before take all of it:\n" + output.warnings());
    }

    @Test
    void aNewtypeOverASumIsTheCasesOfTheSum() throws Exception {
        Output output = run(NEWTYPE, true);

        assertTrue(output.report().contains("branch      2/2"),
                () -> "an `OpenOnly` is a `Draft` or a `Live` and no `Done`:\n" + output.report());
        assertEquals(0, output.exit(), () -> output.report());
    }

    @Test
    void anArmOverAnInnerSumIsEnteredByAnyLeafOfItTheInputHolds() throws Exception {
        Output output = run(NESTED, true);

        assertEquals(2, count(output.report(), "branch      2/2"),
                () -> "the leaf `Station` is not a `NotStation`, and the arm over `OnceKind` is "
                        + "still entered by `Hospital`:\n" + output.report());
        assertEquals(0, output.exit(), () -> output.report());
    }

    /** The arms of what a helper answers are of the arms of the helper, wherever the value
     *  matched stands: it is no position of the input, and the statement says which cases of the
     *  input bring each. */
    @Test
    void anArmOverWhatAHelperAnswersIsRuledOutByEveryHelperArmThatAnswersIt() throws Exception {
        Output output = run(ANSWERED, true);

        assertTrue(output.warnings().contains("Every way a value could arrive here is ruled out"),
                () -> "the arm for `Settled` is entered by `Done` and `Lost`, and neither is an "
                        + "`OpenStage`:\n" + output.warnings());
        assertTrue(output.report().contains("adequacy: satisfied"),
                () -> "so it is owed no row:\n" + output.report());
        assertEquals(0, output.exit(), () -> output.report());
    }

    @Test
    void whatTheDeclarationSaysNothingOfIsNotRuledOut() throws Exception {
        Output output = run(AN_OPTIONAL, false);

        assertFalse(output.warnings().contains("E1327"),
                () -> "an optional is no position whose cases this reading follows:\n"
                        + output.warnings());
    }

    @Test
    void aListHoldsEachOfItsElementsToTheTypeOfTheElement() throws Exception {
        Output output = run(AN_ELEMENT, true);

        assertTrue(output.report().contains("branch      2/2"),
                () -> "no element of a list of `OpenStage` is a `Done`:\n" + output.report());
        assertEquals(0, output.exit(), () -> output.report());
    }

    private static int count(String text, String of) {
        return (text.length() - text.replace(of, "").length()) / of.length();
    }
}
