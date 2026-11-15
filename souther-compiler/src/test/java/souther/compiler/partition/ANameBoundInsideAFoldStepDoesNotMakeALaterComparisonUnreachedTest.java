package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fold's step may stop a run on what it reads. A name the step binds, by a {@code let} or by an
 * inlined library call, stands for what it was bound to, so binding one leaves the places the step
 * may stop on as they are written without it, and a comparison after the fold is judged by whether
 * it reads any of those places.
 *
 * <p>Each spelling that binds is measured against the spelling that writes the expression where
 * it is used, both ways round. Where the comparison after the fold reads none of what the step
 * stops on, no spelling leaves it not shown reached. Where it reads one of them, the spelling
 * without a name leaves it not shown reached, and so does every spelling with one: a reading that
 * let the names go would otherwise agree with the spelling without one only by letting go of every
 * stop.
 */
class ANameBoundInsideAFoldStepDoesNotMakeALaterComparisonUnreachedTest {

    private static final String SIGNATURE =
            "(m: Map<String, Int>, prices: Map<String, Int>, s: String, prev: List<String>) -> Bool";

    private static final String ROWS_APART = """
                | "no" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "b" ]) -> false
                | "yes" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "a" ]) -> true
            """;

    private static final String ROWS_SHARED = """
                | "no" : ([ ("a", 2) ], [ ("a", 3) ], "z", [ "b" ]) -> false
                | "yes" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "a" ]) -> true
            """;

    /** The spellings of the step, each with what is asked after the fold. */
    private static final Map<String, String> STEPS = steps();

    private static Map<String, String> steps() {
        Map<String, String> out = new LinkedHashMap<>();
        out.put("piped", "{ let p = Map.get(k, prices) |> Option.withDefault(0)\n"
                + "        acc + p + q }");
        out.put("called", "{ let p = Option.withDefault(0, Map.get(k, prices))\n"
                + "        acc + p + q }");
        out.put("helper", "acc + line(k, q, prices)");
        out.put("unnamed", "acc + (Map.get(k, prices) |> Option.withDefault(0)) + q");
        return out;
    }

    private static final String APART = "List.contains(s, prev)";

    /** Reads the keys of {@code m}, which the step stops on as much as on the values. */
    private static final String SHARED = "Map.containsKey(s, m)";

    private static String model() {
        StringBuilder source = new StringBuilder("""
                module example.fold

                let line (k: String, q: Int, prices: Map<String, Int>) = {
                    let p = Map.get(k, prices) |> Option.withDefault(0)
                    p + q
                }
                """);
        STEPS.forEach((spelling, step) -> {
            behavior(source, spelling, step, APART, ROWS_APART);
            behavior(source, "shared" + spelling, step, SHARED, ROWS_SHARED);
        });
        return source.toString();
    }

    private static void behavior(StringBuilder source, String name, String step, String asked,
                                 String rows) {
        source.append("""

                behavior %1$s : %2$s
                let %1$s (m, prices, s, prev) = {
                    let total = Map.fold((acc, k, q) -> %3$s, 0, m)
                    %4$s
                }
                example %1$s
                %5$s""".formatted(name, SIGNATURE, step, asked, rows));
    }

    private static final Compilation COMPILATION =
            ACompiledModel.measured(model(), Adequacy.Asked.fullReport());

    private static Map<String, PartitionEvidence> measured() {
        Map<String, PartitionEvidence> out =
                COMPILATION.db().ask(new Adequacy.Coverage("example.fold")).value();
        assertNotNull(out, "the model under test compiles");
        return out;
    }

    /** Every place left unread and why. */
    private static List<String> notRead(PartitionEvidence evidence) {
        return evidence.notRead().stream().map(left -> left.at() + " " + left.reason()).toList();
    }

    /** The places left unread for want of a showing that a run gets to the comparison. */
    private static List<String> notShownToGetTo(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(left -> left.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)
                .map(PartitionEvidence.NotRead::at)
                .toList();
    }

    @Test
    void everySpellingLeavesWhatTheSpellingWithoutANameLeavesWhereTheComparisonReadsNoStop() {
        Map<String, PartitionEvidence> measured = measured();
        List<String> without = notRead(measured.get("unnamed"));
        for (String spelling : STEPS.keySet()) {
            assertNotNull(measured.get(spelling), spelling);
            assertEquals(without, notRead(measured.get(spelling)), spelling);
        }
    }

    @Test
    void whereTheComparisonReadsWhatTheStepStopsOnEverySpellingKeepsItNotShownReached() {
        Map<String, PartitionEvidence> measured = measured();
        List<String> without = notShownToGetTo(measured.get("shared" + "unnamed"));
        assertFalse(without.isEmpty(),
                "the spelling without a name is the one that shows what a shared stop does");
        for (String spelling : STEPS.keySet()) {
            assertEquals(without, notShownToGetTo(measured.get("shared" + spelling)), spelling);
        }
    }

    @Test
    void theComparisonReadingNoStopIsNeverShownNotReached() {
        for (String spelling : STEPS.keySet()) {
            assertTrue(notShownToGetTo(measured().get(spelling)).isEmpty(), spelling);
        }
    }
}
