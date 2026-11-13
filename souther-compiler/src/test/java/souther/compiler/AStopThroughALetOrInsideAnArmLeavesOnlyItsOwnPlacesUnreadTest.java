package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A stop an operation ends a run with, told through a name it is bound to or inside a part of the
 * body some runs skip, leaves unread the places it reads and no others: a comparison of places
 * the stop does not read is read as it is beside a stop written at once and in every run.
 */
class AStopThroughALetOrInsideAnArmLeavesOnlyItsOwnPlacesUnreadTest {

    private static final String DECLARED = """
            module probe.arm

            data Ok
            data No
            data Skipped

            data Row = { x: Int, k: Int, m: Int, j: Int }
            """;

    private record Model(String name, String before) {}

    private static final String UNRELATED = "p.m + 1 >= p.j";

    private static final List<Model> MODELS = List.of(
            new Model("a quotient written out", "let y = Rational.toInt(DOWN, 1 / p.x)"),
            new Model("a quotient bound to a name",
                    "let q = 1 / p.x\n    let y = Rational.toInt(DOWN, q)"),
            new Model("a quotient bound to a name, kept as it is",
                    "let q = 1 / p.x\n    let y = q"),
            new Model("a quotient in an arm",
                    "let y = if p.k > 0 then Rational.toInt(DOWN, 1 / p.x) else 0"),
            new Model("a quotient in the other arm",
                    "let y = if p.k > 0 then 0 else Rational.toInt(DOWN, 1 / p.x)"),
            new Model("a quotient after a conjunction",
                    "let y = p.k > 0 && Rational.toInt(DOWN, 1 / p.x) > 0"),
            new Model("a quotient after a disjunction",
                    "let y = p.k > 0 || Rational.toInt(DOWN, 1 / p.x) > 0"),
            new Model("a sum in an arm", "let y = if p.k > 0 then p.x + 1 else 0"));

    private static String report(Model model, String comparison, Adequacy.Level level) {
        String source = DECLARED + """

                behavior m : (p: Row) -> Bool
                let m (p) = {
                    %s
                    let c = %s
                    c
                }
                """.formatted(model.before(), comparison);
        Compilation compilation = ACompiledModel.measured(source, Adequacy.Asked.reportOnly(level));
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /**
     * Each name reads the one before it twice, so a number worked out once for each way a name is
     * reached takes twice as long at every binding added; at this depth that is no time at all.
     */
    @Test
    void aChainOfNamesEachReadingTheOneBeforeTwiceIsWorkedOutOncePerName() {
        StringBuilder before = new StringBuilder("let a0 = 1 / p.x");
        int depth = 30;
        for (int i = 1; i <= depth; i++) {
            before.append("\n    let a").append(i).append(" = a").append(i - 1).append(" * a")
                    .append(i - 1);
        }
        before.append("\n    let y = Rational.toInt(DOWN, a").append(depth).append(")");
        Model chain = new Model("a chain of names", before.toString());
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60),
                () -> report(chain, UNRELATED, Adequacy.Level.ALL));
        assertFalse(report.contains("not read:"), report);
    }

    /**
     * Each name holds a remainder of the one before it and reads it again beside, so the
     * remainder of a dividend, the number the divisor is and why a stop is no form each read the
     * chain below, and a remainder is read once for every way down to it unless a remainder read is
     * taken again.
     */
    @Test
    void aChainOfNamesEachHoldingARemainderOfTheOneBeforeIsWorkedOutOncePerName() {
        Model shallow = remainders(3);
        Model deep = remainders(24);
        String report = assertTimeoutPreemptively(Duration.ofSeconds(30),
                () -> report(deep, UNRELATED, Adequacy.Level.ALL));
        assertEquals(report(shallow, UNRELATED, Adequacy.Level.ALL).contains("not read:"),
                report.contains("not read:"),
                "what a chain says is what it says of its first links");
    }

    /** {@code depth} names, each a remainder of the one before and that one beside, the last the
     *  divisor of a remainder. */
    private static Model remainders(int depth) {
        StringBuilder before = new StringBuilder("let a0 = p.x");
        for (int i = 1; i <= depth; i++) {
            before.append("\n    let a").append(i).append(" = Int.floorMod(a").append(i - 1)
                    .append(", 7) + a").append(i - 1);
        }
        before.append("\n    let y = Int.floorMod(7, a").append(depth).append(")");
        return new Model("a chain of remainders", before.toString());
    }

    @Test
    void aComparisonOfPlacesNoStopReadsIsReadWhateverTheStopIsBoundOrGuardedBy() {
        List<String> wrong = new ArrayList<>();
        for (Adequacy.Level level : List.of(Adequacy.Level.ALL, Adequacy.Level.WITNESS)) {
            for (Model each : MODELS) {
                String report = report(each, UNRELATED, level);
                if (report.contains("not read:")) {
                    wrong.add(level + " " + each.name() + ":\n" + report);
                }
            }
        }
        assertEquals(List.of(), wrong);
    }
}
