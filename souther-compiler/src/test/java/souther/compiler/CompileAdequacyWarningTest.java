package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a build is told about what its {@code example}s do not cover.
 *
 * <p>Off by default and one dial, because the levels differ in what they cost. Reading what the rows
 * already established is free; finding out which arms they went through means generating a second set
 * of classes and running every row again, and a build that did not ask for that must not pay for it —
 * an editor recompiles on every keystroke.
 */
class CompileAdequacyWarningTest {

    private static final String MODEL = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas

            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior submit : (kind: Kind, cost: Amount) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (kind, cost) = {
                guard cost.value <= 100 else Waiting { cost = cost }
                Submitted { cost = cost }
            }

            example submit
                | (Domestic, Amount(50)) -> Submitted { cost = Amount(50) }
            """;

    private static List<String> codesAt(Adequacy.Level level) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(level);
        compilation.answerEverything();
        List<String> codes = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            Diagnostic d = found.report().diagnostic();
            if (!found.report().isError() && d.code() != null && d.code().startsWith("E19")) {
                codes.add(d.code());
            }
        }
        return codes;
    }

    /** The default. A build that did not ask is told nothing, and nothing is measured to tell it. */
    @Test
    void aBuildThatDidNotAskIsToldNothing() {
        assertEquals(List.of(), codesAt(Adequacy.Level.OFF));
    }

    /**
     * What the compile already ran is enough to say which cases nothing claims.
     *
     * <p>The one row expects `Submitted` and applies the behavior to a `Domestic`, so `Waiting` and
     * `Overseas` are both cases the model declares and nothing says anything about.
     */
    @Test
    void theSignatureGapsCostNothingToFind() {
        List<String> codes = codesAt(Adequacy.Level.WITNESS);

        assertTrue(codes.contains("E1913"), codes.toString());
        assertTrue(codes.contains("E1915"), codes.toString());
        assertFalse(codes.contains("E1916"), "a boundary takes running the rows again: " + codes);
        assertFalse(codes.contains("E1918"), "and so does an arm: " + codes);
    }

    /** Asking for everything adds what the second run answers, and nothing that was there is lost. */
    @Test
    void theArmsAndTheBoundariesArriveWithTheLevelThatPaysForThem() {
        List<String> codes = codesAt(Adequacy.Level.ALL);

        assertTrue(codes.contains("E1913"), codes.toString());
        assertTrue(codes.contains("E1915"), codes.toString());
        assertTrue(codes.contains("E1916"), codes.toString());
        assertTrue(codes.contains("E1918"), codes.toString());
    }

    /**
     * Nothing that only the report says becomes a warning.
     *
     * <p>A position the model draws no line through is a fact about the model rather than a mistake in
     * it — 398 of them across the corpus this was measured on, every one saying "no rule was written
     * here". A row waiting for a {@code let} is not a mistake either: waiting is the normal state of a
     * model being written. Both stay in `souther examples` and out of the build.
     */
    @Test
    void whatIsOnlyWorthReportingIsNotWarnedAbout() {
        List<String> codes = codesAt(Adequacy.Level.ALL);

        assertFalse(codes.contains("E1912"), "pending is not a warning: " + codes);
        assertFalse(codes.contains("E1917"), "not derivable is not a warning: " + codes);
    }

    /** Every warning is a warning. None of these stops a build. */
    @Test
    void noneOfThemIsAnError() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Level.ALL);
        compilation.answerEverything();

        for (Db.Found found : compilation.db().allReports()) {
            String code = found.report().diagnostic().code();
            if (code != null && code.startsWith("E19") && !code.equals("E1901")) {
                assertFalse(found.report().isError(), code + " stopped the build");
            }
        }
    }

    /** A model whose rows cover it says nothing, at any level. */
    @Test
    void aCoveredModelIsSilent() {
        String covered = MODEL + """
                    | (Overseas, Amount(0))   -> Submitted { cost = Amount(0) }
                    | (Domestic, Amount(100)) -> Submitted { cost = Amount(100) }
                    | (Domestic, Amount(101)) -> Waiting { cost = Amount(101) }
                """;
        Compilation compilation = Compilation.ofSource(covered, "Main");
        compilation.measure(Adequacy.Level.ALL);
        compilation.answerEverything();

        List<String> codes = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            Diagnostic d = found.report().diagnostic();
            if (d.code() != null && d.code().startsWith("E19")) {
                codes.add(d.code() + " " + d.values().values().iterator().next());
            }
        }
        assertEquals(List.of(), codes);
    }
}
