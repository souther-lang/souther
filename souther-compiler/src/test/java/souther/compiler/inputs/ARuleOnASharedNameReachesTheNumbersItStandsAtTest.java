package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule a record writes about a name its cases share reaches the numbers that name stands at.
 *
 * <p>{@code Holder} says {@code q.limit <= 10} and {@code q} is a sum whose cases spread the
 * declaration that writes {@code limit}. The name is written at {@code q}; the numbers are at
 * {@code q@A.limit} and {@code q@B.limit}. A reader asking where one of those runs is asking about
 * the number the rule is about, and the rule has to be part of the answer.
 */
class ARuleOnASharedNameReachesTheNumbersItStandsAtTest {

    private static final String SHARED = """
            module g

            data Paging = { limit: Int }
            data A = { ...Paging, x: Int }
            data B = { ...Paging, y: Int }
            data Q = A | B

            data Holder = { q: Q }
                invariant small = q.limit <= 10

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** The same model with the rule taken out, so that what the rule does is what is measured. */
    private static final String UNRULED = SHARED.replace("    invariant small = q.limit <= 10\n",
            "");

    @Test
    void theRuleTheRecordWroteBoundsEachCase() {
        for (String at : List.of("h.q@A.limit", "h.q@B.limit")) {
            NumericDomain.Bounds runs = runsAt(SHARED, at);

            assertNotNull(runs, at + " is a number this reading answers about");
            assertNotNull(runs.max(),
                    () -> at + " is bounded above by the rule the record wrote, and runs " + runs);
            assertEquals("10", souther.compiler.numeric.Count.number(runs.max().at()).at()
                            .stripTrailingZeros().toPlainString(),
                    at + " stops where the rule the record wrote put it");
        }
    }

    /**
     * And nothing else bounds it, so the bound above is the rule's doing.
     *
     * <p>Without this the first would pass on a reading that bounds every {@code Int} for reasons
     * of its own, and would say nothing about whether a rule written at a name reaches the numbers
     * that name stands at.
     */
    @Test
    void andWithoutTheRuleNothingBoundsIt() {
        for (String at : List.of("h.q@A.limit", "h.q@B.limit")) {
            NumericDomain.Bounds runs = runsAt(UNRULED, at);

            assertTrue(runs == null || runs.max() == null,
                    () -> at + " is bounded by nothing once the rule is gone, and runs " + runs);
        }
    }

    private static NumericDomain.Bounds runsAt(String source, String spelled) {
        InputDomain read = reading(source, "read");
        return read.quantities(symbolsOf(source))
                .runsBetween(new NumericTerm.ValueOf(pathOf(read, spelled)));
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
