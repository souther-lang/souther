package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule relating two names a sum's cases share reaches the numbers those names stand at.
 *
 * <p>Beside {@link ABoundOnASharedNameReachesTheNumbersItStandsAtTest}, which measures an end. An
 * end is a per-name answer and reaches the case through the reading of the position; a relation is
 * not a per-name answer, and what carries it is the rules of the value above said again in the
 * words of the case.
 *
 * <p><b>Once per context and not once per narrowing crossed.</b> The last measurement here relates
 * two names under two sums that are narrowed independently. A renaming worked out edge by edge
 * leaves one of the two names spelled as the sum wrote it in either copy, and the two copies relate
 * nothing when they are met.
 */
class ARelationOverSharedNamesReachesTheNumbersTheyStandAtTest {

    private static final String ONE_SUM = """
            module g

            data Shared = { lo: Int, hi: Int }
            data A = { ...Shared, x: Int }
            data B = { ...Shared, y: Int }
            data Q = A | B

            data Holder = { q: Q }
                invariant ordered = q.lo <= q.hi

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** The same model with the rule taken out, so that what the rule does is what is measured. */
    private static final String UNRULED =
            ONE_SUM.replace("    invariant ordered = q.lo <= q.hi\n", "");

    private static final String TWO_SUMS = """
            module g

            data Shared = { lo: Int, hi: Int }
            data A = { ...Shared, x: Int }
            data B = { ...Shared, y: Int }
            data Q = A | B

            data Holder = { left: Q, right: Q }
                invariant across = left.lo <= right.hi

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    private static final String TWO_SUMS_UNRULED =
            TWO_SUMS.replace("    invariant across = left.lo <= right.hi\n", "");

    private static final String ONE_SUM_OF_TWO = """
            module g

            data Shared = { lo: Int, hi: Int }
            data A = { ...Shared, x: Int }
            data B = { ...Shared, y: Int }
            data Q = A | B

            data Holder = { p: Q, r: Q }
                invariant ordered = p.lo <= p.hi

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** The rule the record wrote about the sum, read at the numbers one case stands at. */
    @Test
    void aRelationReachesTheCaseTheNumbersStandUnder() {
        for (String at : List.of("A", "B")) {
            NumericDomain.Bounds runs = stoppedAt(ONE_SUM,
                    "h.q@" + at + ".lo", "h.q@" + at + ".hi", 7);

            assertNotNull(runs, "h.q@" + at + ".lo is a number this reading answers about");
            assertNotNull(runs.max(), () -> "h.q@" + at + ".lo stops where h.q@" + at
                    + ".hi was fixed, and runs " + runs);
            assertEquals("7", number(runs.max()),
                    "h.q@" + at + ".lo stops where the rule the record wrote put it");
        }
    }

    /** And nothing else stops it, so the end above is the rule's doing. */
    @Test
    void andWithoutTheRuleNothingStopsIt() {
        NumericDomain.Bounds runs = stoppedAt(UNRULED, "h.q@A.lo", "h.q@A.hi", 7);

        assertTrue(runs == null || runs.max() == null,
                () -> "h.q@A.lo is stopped by nothing once the rule is gone, and runs " + runs);
    }

    /**
     * The relation carried into one case is about that case's numbers.
     *
     * <p>Two values of one sum's declaration, related by a rule written about one of them. Fixing
     * the one leaves the other where its own type leaves it — a renaming that carried the rule to
     * every position spelled {@code lo} would stop this one too.
     */
    @Test
    void andItIsAboutTheValueTheRuleWasWrittenAbout() {
        NumericDomain.Bounds runs = stoppedAt(ONE_SUM_OF_TWO, "h.r@A.lo", "h.p@A.hi", 7);

        assertTrue(runs == null || runs.max() == null,
                () -> "h.r@A.lo is stopped by nothing, the rule being about h.p, and runs " + runs);
    }

    /**
     * One relation, two sums narrowed independently, and it reaches both.
     *
     * <p>What the whole context selects, in one renaming. Crossed one narrowing at a time, the copy
     * carried into {@code left@A} still calls the other name {@code right.hi} and the copy carried
     * into {@code right@B} still calls this one {@code left.lo}, so nothing relates the two numbers
     * a caller asked about.
     */
    @Test
    void aRelationCrossesTwoNarrowingsAtOnce() {
        NumericDomain.Bounds runs = stoppedAt(TWO_SUMS, "h.left@A.lo", "h.right@B.hi", 7);

        assertNotNull(runs, "h.left@A.lo is a number this reading answers about");
        assertNotNull(runs.max(),
                () -> "h.left@A.lo stops where h.right@B.hi was fixed, and runs " + runs);
        assertEquals("7", number(runs.max()),
                "h.left@A.lo stops where the rule across the two sums put it");
    }

    @Test
    void andWithoutThatRuleNothingStopsItEither() {
        NumericDomain.Bounds runs =
                stoppedAt(TWO_SUMS_UNRULED, "h.left@A.lo", "h.right@B.hi", 7);

        assertTrue(runs == null || runs.max() == null,
                () -> "h.left@A.lo is stopped by nothing once the rule is gone, and runs " + runs);
    }

    /** Where {@code asked} runs once {@code fixed} stands at {@code at}. */
    private static NumericDomain.Bounds stoppedAt(String source, String asked, String fixed,
                                                  int at) {
        InputDomain read = reading(source, "read");
        Quantities quantities = read.quantities(symbolsOf(source));
        return quantities
                .given(new NumericTerm.ValueOf(pathOf(read, fixed)),
                        Count.of(BigDecimal.valueOf(at)))
                .runsBetween(new NumericTerm.ValueOf(pathOf(read, asked)));
    }

    private static String number(souther.compiler.numeric.Endpoint end) {
        return Count.number(end.at()).at().stripTrailingZeros().toPlainString();
    }

    private static TermPath pathOf(InputDomain read, String spelled) {
        return read.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + read.positions().stream()
                                .map(Position::path).toList()));
    }

    private static Symbols symbolsOf(String source) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        return Scopes.derived(compilation.db(), compilation.modules().get(0)).value();
    }

    private static InputDomain reading(String source, String behavior) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        return InputDomain.of(spec, sigs.get(behavior), symbols, ReadAs.THE_COMPILATION_DOES);
    }
}
