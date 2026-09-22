package souther.program.api;

import souther.compiler.abort.AbortKind;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@link CheckedProgram#abortsAt} answers for a {@code Core} site, read against the same
 * fixtures a source author would write — never against a node built by hand, which would be asking
 * this compiler's own opinion of a shape it invented rather than of a program it checked.
 */
class ACoreSiteAnswersWhichLanguageAbortsItCanRaiseTest {

    private static final String MODULE = """
            module demo exposing ( Positive, unguarded, guarded, sums, divides, unreached )

            data Positive = Int
                invariant positive = value > 0

            behavior unguarded : (n: Int) -> Positive

            let unguarded (n) = Positive(n)

            behavior guarded : (n: Int) -> Positive

            let guarded (n) = {
                guard Positive(n) as p else Positive(1)

                p
            }

            behavior sums : (a: Int, b: Int) -> Int

            let sums (a, b) = a + b

            behavior divides : (a: Int, b: Int) -> Int

            let divides (a, b) = Rational.toInt(DOWN, a / b)

            behavior unreached : (n: Int) -> Int

            let unreached (n) = unreachable "never called with anything"
            """;

    private static CheckedProgram program() {
        return CheckedProgram.of(List.of(MODULE));
    }

    private static Core bodyOf(CheckedProgram program, String behavior) {
        CheckedModule demo = program.module("demo");
        for (var b : demo.behaviors()) {
            if (b.name().name().equals(behavior)) {
                return ((CheckedImplementation.Body) b.implementation()).body();
            }
        }
        throw new AssertionError("no behavior `" + behavior + "` in the fixture");
    }

    /** Every node under {@code root}, {@code root} itself included — a plain walk, independent of
     *  {@code AbortSites}, so this test reads the body rather than the classifier's own opinion of
     *  it. */
    private static List<Core> everyNodeOf(Core root) {
        List<Core> found = new ArrayList<>();
        collect(root, found);
        return found;
    }

    private static void collect(Core node, List<Core> into) {
        into.add(node);
        Core.forEachChild(node, child -> collect(child, into));
    }

    @Test
    void aPlainConstructionAbortsOnAnUnheldInvariant() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "unguarded");

        Core.Construct construct = onlyOneOf(Core.Construct.class, body);

        assertEquals(Set.of(AbortKind.INVARIANT_NOT_HELD), program.abortsAt(construct).kinds());
    }

    /**
     * And the same construction, attempted, never does — the invariant decides a branch instead of
     * aborting, so the site {@code guard ... as ... else ...} tests has nothing to answer for.
     */
    @Test
    void anAttemptedConstructionNeverAbortsOnTheInvariantItTests() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "guarded");

        Core.IfConstructed attempt = onlyOneOf(Core.IfConstructed.class, body);

        assertTrue(program.abortsAt(attempt).isEmpty(),
                "the IfConstructed itself branches; it does not abort");
        assertTrue(program.abortsAt(attempt.construct()).isEmpty(),
                "the construction it tests is guarded, so its own invariant is not an abort here");
    }

    @Test
    void anIntSumAbortsWhereTheAnswerHasNoPlace() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "sums");

        Core.Binary sum = onlyOneOf(Core.Binary.class, body);

        assertEquals(Set.of(AbortKind.ANSWER_HAS_NO_PLACE), program.abortsAt(sum).kinds());
    }

    @Test
    void theExactQuotientAbortsOnAZeroDivisorAndOnAnAnswerWithNoPlace() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "divides");

        Core.Binary quotient = onlyOneOf(Core.Binary.class, body);

        assertEquals(Set.of(AbortKind.DIVISION_BY_ZERO, AbortKind.ANSWER_HAS_NO_PLACE),
                program.abortsAt(quotient).kinds());
    }

    @Test
    void unreachableAbortsForTheOneReasonItIs() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "unreached");

        Core.Unreachable reached = onlyOneOf(Core.Unreachable.class, body);

        assertEquals(Set.of(AbortKind.UNREACHABLE_REACHED), program.abortsAt(reached).kinds());
    }

    /** And an ordinary read never does — a program is not every site answering the same thing. */
    @Test
    void aReadOfAParameterNeverAborts() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "sums");

        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Read read) {
                assertTrue(program.abortsAt(read).isEmpty(), () -> read + " never aborts on its own");
            }
        }
    }

    /** A node this program never handed over is refused rather than answered as total. */
    @Test
    void aSiteNoProgramHandedOverIsRefused() {
        CheckedProgram program = program();
        Core.Int stray = new Core.Int(1, Type.INT, new SourcePos(1, 1));

        assertThrows(IllegalArgumentException.class, () -> program.abortsAt(stray));
    }

    private static <T extends Core> T onlyOneOf(Class<T> kind, Core body) {
        T found = null;
        for (Core node : everyNodeOf(body)) {
            if (kind.isInstance(node)) {
                if (found != null) {
                    throw new AssertionError("more than one " + kind.getSimpleName() + " in " + body);
                }
                found = kind.cast(node);
            }
        }
        if (found == null) {
            throw new AssertionError("no " + kind.getSimpleName() + " in " + body);
        }
        return found;
    }
}
