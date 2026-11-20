package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A helper whose arm makes a value its condition keeps within the type's rules makes it on no run
 * that stops, wherever it is called, and so does a call handed what an earlier call made on that
 * arm: no comparison is said to work out what may stop a run where nothing says.
 *
 * <p>Three calls, since what the second is handed is still a form of the numbers of the input
 * its arm holds, and what the third is handed is a value of the type made two calls back, whose
 * number only the type's rules hold.
 */
class AHelperCalledOnWhatItMadeOnAnArmIsToldToStopNoRunThereTest {

    @Test
    void aCallHandedWhatAnEarlierOneMadeOnItsArmStopsNoRun() {
        Compilation compilation = ACompiledModel.measured("""
                module probe.chained

                data MB = Int
                    invariant value >= 0
                data Drawn = { taken: MB, left: MB }

                behavior draw : (used: MB, a: MB, b: MB, c: MB) -> Drawn
                    constructs Drawn, MB

                let draw (used, a, b, c) = {
                    let (_, rest) = take(used, a)
                    let (_, more) = take(rest, b)
                    let (taken, left) = take(more, c)
                    Drawn { taken = taken, left = left }
                }

                let take (used: MB, cap: MB): (MB, MB) =
                    if used.value <= cap.value then (used, MB(0))
                    else (cap, MB(used.value - cap.value))
                """, new Adequacy.Asked(Adequacy.Level.OFF, false));
        String report = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));

        assertFalse(report.contains(UnreadBesideItsStops.STOPS_NOT_ALL_TOLD), report);
    }
}
