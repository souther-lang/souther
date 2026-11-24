package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run has worked out by one application of a closure, and what it is handed, is every
 * application before it, whether or not that one gets to the step being judged: an application
 * taking another arm is worked out all the same, and hands on what it answered.
 */
class AnApplicationThatDoesNotGetToAStepIsStillWorkedOutBeforeItTest {

    private static List<String> stops(String body) {
        Compilation compilation = ACompiledModel.measured("""
                module demo

                data In = { p: Int, q: Int }

                behavior b : (i: In) -> Int
                let b (i) = %s
                """.formatted(body), new Adequacy.Asked(Adequacy.Level.OFF, false));
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).filter(line -> line.startsWith("· may stop a run:")
                        || line.startsWith("· stop not resolved:")).toList();
    }

    /** The first application takes the other arm and answers {@code i.q}, which the second is
     *  handed: its sum stops at the greatest {@code i.q}, and is not read as one over the seed. */
    @Test
    void aFoldHandsOnWhatAnApplicationThatTookTheOtherArmAnswered() {
        List<String> said = stops(
                "List.fold((a, x) -> if x == 0 then i.q else a + 1, 0, [0, 1])");
        assertTrue(said.stream().anyMatch(line -> line.startsWith("· may stop a run:")
                && line.contains("i.q = 9223372036854775807")), said::toString);
    }

    /** The first application is made only where {@code i.p} is not nought: where it is, the
     *  second is handed the seed, and its sum, the one step that may stop, stops. What the first
     *  answers is not read as what the second is handed, so the sum is not shown to get past. */
    @Test
    void anApplicationMadeOnlyOnSomeRowsHandsOnNothingTakenAsMade() {
        List<String> said = stops("List.fold((a, x) -> if x == 0 then 0 else a + 1,"
                + " 9223372036854775807, List.filter(x -> x /= i.p, [0, 1]))");
        assertFalse(said.isEmpty(), said::toString);
    }

    /** The first application divides by {@code i.p} on its arm, before the second gets to its
     *  sum: no value is shown to stop at the sum that stops at the division first. */
    @Test
    void anApplicationBeforeTheStepOnAnotherArmIsGotPastFirst() {
        List<String> said = stops("List.length(List.map(x -> if x == 0 then"
                + " Rational.toInt(DOWN, 4 / i.p) else x + i.q, [0, 1]))");
        assertFalse(said.stream().anyMatch(line -> line.startsWith("· may stop a run:")
                && line.contains("stops in i.q + 1") && line.contains("i.p = 0")),
                said::toString);
    }
}
