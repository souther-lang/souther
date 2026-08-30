package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison no run through can be recorded is not a rule the model has no line for.
 *
 * <p>Its outcome decides nothing about any row, because no row gets past it — so there is nothing
 * for a report to say of it, and in particular nothing in the words a reading of the arithmetic
 * answers in. Those words are about what the arithmetic could do with the form, and the form is not
 * what refuses the comparison: where it stands is. Given a reason in those words all the same, a
 * comparison the arithmetic reads to the end is reported as one whose form went unread, and the
 * measurement is marked short of something no reader fell short of.
 *
 * <p>What refuses it is asked of the standing, so the claim is made at both levels: that this
 * comparison is one the policy refuses for that reason, and that the report says nothing of it.
 * Without the first, the second would hold of a model whose comparison was simply a line.
 */
class AComparisonNoRunReachesIsNotARuleWithoutALineTest {

    /**
     * A comparison whose every continuation aborts, with the rule written in {@code condition}.
     *
     * <p>{@code Off} is a case the model rules out, so the {@code unreachable}s are claims the rules
     * bear out (E1326 otherwise) — and the comparison deciding between the two of them is one no
     * run answers past, whichever way it comes out.
     */
    private static String model(String condition) {
        return """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Active = Flag invariant value /= Off
                data Answer = Int

                behavior pick : (f: Active, n: Int) -> Answer
                let pick (f, n) = match f.value with
                    | On  -> Answer(1)
                    | Off -> if %s then unreachable "a" else unreachable "b"

                example pick
                    | "on" : (Active(On), 3) -> Answer(1)
                """.formatted(condition);
    }

    /** A form the arithmetic reads to the end: one line, cutting one position at one value. */
    private static final String READ = "n >= 100000";

    /** A form the arithmetic stops on: the product of a position with itself. */
    private static final String STOPPED = "n * n >= 100000";

    private static String report(String condition) {
        Compilation compilation = Compilation.ofSource(model(condition), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }

    @Test
    void theComparisonIsOneNoRunRecords() {
        BoundaryPolicy.Standing standing =
                ReadComparisons.of(model(READ), "pick").only().standing();
        assertEquals(new BoundaryPolicy.Standing.Refused(standing.comparison(),
                NotABoundary.NOTHING_RECORDS_IT), standing);
    }

    @Test
    void aFormReadToTheEndIsNotReportedAsOneNobodyRead() {
        String human = report(READ);
        assertFalse(human.contains("not read: comparison"), human);
        assertFalse(human.contains("measurement: partial"), human);
    }

    /**
     * And a form the arithmetic would have stopped on says nothing either. The standing is decided
     * before the arithmetic is asked, so what the arithmetic would have made of the form is not a
     * fact anybody holds.
     */
    @Test
    void aFormTheArithmeticWouldStopOnIsNotReportedEither() {
        String human = report(STOPPED);
        assertFalse(human.contains("not read: comparison"), human);
        assertFalse(human.contains("measurement: partial"), human);
    }

    /** The half that makes the other half worth reading: the same rule where a run reaches it is
     *  a line, and the report carries it. */
    @Test
    void theSameRuleWhereARunReachesItIsALine() {
        Compilation compilation = Compilation.ofSource("""
                module example.probe

                data Answer = Int

                behavior pick : (n: Int) -> Answer
                let pick (n) = if n >= 100000 then Answer(1) else Answer(0)

                example pick
                    | "low" : (3) -> Answer(0)
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String human = AdequacyReport.of(compilation).human(SourceNameResolver.identity());
        assertTrue(human.contains("100000"), human);
    }
}
