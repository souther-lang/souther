package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two arms counted as one that nothing shows are one leave the measurement short of complete.
 *
 * <p>What tells two copies of a fork apart is what each decides, described far enough to tell one
 * specialisation of a rule from another. A fork handed a value from outside the body decides
 * something this can describe nothing of, so its copies describe alike without anything having been
 * compared — and they are counted together.
 *
 * <p>Together rather than apart, which is the safer of the two: split, each would be owed a row
 * establishing what the row beside it already does, and a specific piece of work that is already
 * done is worse to be told than nothing.
 *
 * <p>What it costs is a count holding two decisions where it says one. That is exactly a behavior
 * reported complete over something nothing ran, so the count does not call itself complete — in the
 * prose, in the document, and in the one field a build reads.
 *
 * <p>Which module wrote the fork does not come into it. A helper of this module's own applying what
 * it was handed is the same shape as one the library wrote, and a rule that asked where the fork was
 * written would have said nothing about the one below.
 */
class WhatIsCountedTogetherIsSaidTest {

    private static final String MODULE = "example.flags";

    private static final String MODEL = """
            module example.flags

            data Yes
            data No
            data Verdict = Yes | No

            let decide (b: Bool): Verdict = if b then Yes else No

            behavior both : (p: Bool, q: Bool) -> Verdict
            let both (p, q) = if decide(p) == Yes then decide(q) else No

            example both
                | "the first holds and the second does not" : (true, false) -> No
            """;

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    private static Adequacy.BranchEvidence arms() {
        Adequacy.BranchEvidence both = measured().db()
                .ask(new Adequacy.BranchCoverage(MODULE)).value().get("both");
        assertNotNull(both, "the model under test compiles");
        return both;
    }

    /** The helper's two calls come out under one pair of keys: neither decides anything sayable. */
    @Test
    void armsNothingCanTellApartAreCountedTogether() {
        Adequacy.BranchEvidence both = arms();

        assertEquals(6, both.all().size(), "each call is emitted and probed on its own");
        assertEquals(4, both.obligations(),
                () -> "the helper's two calls are counted under one pair: " + both.all().stream()
                        .map(each -> each.obligation().decides().said()).toList());
        assertEquals(1, both.countedTogether().size(),
                () -> "one fork whose copies cannot be told apart: " + both.countedTogether());
    }

    /**
     * And the numbers do not call themselves complete.
     *
     * <p>The whole of what the collapse costs. A count holding two decisions where it says one, with
     * a status of complete beside it, is a behavior reported complete over something nothing ran.
     */
    @Test
    void theMeasurementIsNotComplete() {
        assertNotEquals(MeasurementStatus.COMPLETE, arms().status(),
                "what the count holds is more than what it says");
    }

    /** And the report says which fork that is, once for the fork. */
    @Test
    void theReportSaysWhichForkThatIs() {
        String human = AdequacyReport.of(measured()).human(SourceNameResolver.identity());

        assertEquals(1, human.lines().filter(line -> line.contains("counted as one")).count(),
                () -> "said once for the fork and not once per arm: " + human);
    }

    /** And a document says it too, not only the prose. */
    @Test
    void theDocumentSaysItToo() {
        String json = AdequacyReport.of(measured()).json(SourceNameResolver.identity());

        assertTrue(json.contains("\"countedTogether\" : [ \"example.flags\" ]"), json);
    }

    /**
     * Nothing is said where the two decide describably different things.
     *
     * <p>Including where neither compares anything: a field an author named is something they wrote,
     * and two of them are two decisions.
     */
    @Test
    void nothingIsSaidWhereTheDecisionsAreToldApart() {
        Compilation compilation = Compilation.ofSource("""
                module example.flags

                data Person =
                    { active: Bool
                    , retired: Bool
                    }
                data Yes
                data No
                data Verdict = Yes | No

                let decide (b: Bool): Verdict = if b then Yes else No

                behavior both : (x: Person) -> Verdict
                let both (x) = if decide(x.active) == Yes then decide(x.retired) else No

                example both
                    | "active and not retired"
                        : (Person { active = true, retired = false }) -> No
                """, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Adequacy.BranchEvidence both = compilation.db()
                .ask(new Adequacy.BranchCoverage(MODULE)).value().get("both");
        assertNotNull(both, "the model under test compiles");

        assertEquals(List.of(), both.countedTogether(),
                () -> "the two decide different things: " + both.all().stream()
                        .map(each -> each.obligation().decides().said()).toList());
        assertEquals(6, both.obligations(), "so each call's arms are its own to cover");
    }
}
