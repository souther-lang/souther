package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A comparison read to the end and the same for every row is said to cut nothing where it is
 * written, however it was settled.
 *
 * <p>A form of the input's numbers that cancels, the bounds of the sign an ordering answers, a
 * form over what an operation answered that cancels by its law, a form over a value the body bound
 * that cancels: each reading comes to the same statement, and the report says the same of each. The
 * one answer it may not give is silence — a position such a rule is written about, said to be one
 * the model states nothing about.
 */
class AComparisonSettledForEveryRowCutsNothingWhereItIsWrittenTest {

    private static final String MODEL = """
            module probe.settled

            data P = { a: Int, b: Int, xs: List<Int> }

            behavior cancels : (p: P) -> Int
            let cancels (p) = if p.a - p.a == 0 then 1 else 0

            behavior bySign : (p: P) -> Int
            let bySign (p) = if Int.compare(p.a, p.b) <= 1 then 1 else 0

            behavior byALaw : (p: P) -> Int
            let byALaw (p) =
                if List.length(List.map(x -> x + 1, p.xs)) - List.length(p.xs) == 0 then 1 else 0

            behavior bound : (p: P) -> Int
            let bound (p) = {
                let n = p.a * p.b
                if n - n == 0 then 1 else 0
            }
            """;

    /** The report on {@link #MODEL}, made once: every case here asks it about one behavior. */
    private static AdequacyReport report;

    private static AdequacyReport report() {
        if (report == null) {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            report = AdequacyReport.of(compilation);
        }
        return report;
    }

    /** What was left unread about each position of {@code behavior}, as {@code position reason}. */
    private static List<String> notRead(String behavior) {
        for (AdequacyReport.BehaviorReport each : report().modules().get(0).behaviors()) {
            if (each.name().equals(behavior)) {
                return each.partition().notRead().stream()
                        .map(one -> one.at() + " " + one.reason()).toList();
            }
        }
        throw new AssertionError("no behavior called " + behavior);
    }

    @Test
    void aFormThatCancelsCutsNothingAtTheNumberItWasReadOver() {
        assertEquals(List.of("p.a RULE_CUTS_NOTHING"), notRead("cancels"));
    }

    @Test
    void anOrderingWhoseSignItsBoundsSettleCutsNothingAtWhatItCompares() {
        assertEquals(List.of("p.a RULE_CUTS_NOTHING", "p.b RULE_CUTS_NOTHING"), notRead("bySign"));
    }

    @Test
    void everySettlingIsSaidAndNoneIsSilence() {
        for (String behavior : List.of("cancels", "bySign", "byALaw", "bound")) {
            List<String> said = notRead(behavior);
            assertFalse(said.isEmpty(), () -> behavior + " is written about the input");
            said.forEach(each -> assertEquals("RULE_CUTS_NOTHING", each.split(" ")[1],
                    () -> behavior + " was read to the end and cuts nothing: " + said));
        }
    }
}
