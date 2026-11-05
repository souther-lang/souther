package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.OccurrenceLineage;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An evaluation a proof about the way to a place may rest on says which copy of its body it stands
 * in, and a helper called twice holds it in two copies.
 *
 * <p>Asked of the tree the elaborator makes, where the copy is known: a node that cannot say is
 * one a proof would put at the helper's one written place.
 */
class EveryEvaluationAProofMayRestOnSaysTheCopyItIsInTest {

    private static final String SOURCE = """
            module example.copies

            data Grade = Int
                invariant value >= 0

            let graded (x: Int): Grade = Grade(x)
            let negated (x: Int): Int = -x
            let stop (x: Int): Int = if x > 100 then unreachable "no" else x

            behavior negatedTwice : (a: Int, b: Int) -> Int
            let negatedTwice (a, b) = negated(a) + negated(b)

            behavior stoppedTwice : (a: Int, b: Int) -> Int
            let stoppedTwice (a, b) = stop(a) + stop(b)

            behavior gradedTwice : (a: Int, b: Int) -> Grade
                constructs Grade
            let gradedTwice (a, b) = if a > b then graded(a) else graded(b)
            """;

    @Test
    void aNegationInAHelperCalledTwiceIsInTwoCopies() {
        List<Core.Neg> found = in("negatedTwice", Core.Neg.class);
        assertCopies(found.stream().map(Core.Neg::lineage).toList());
    }

    @Test
    void anUnreachableInAHelperCalledTwiceIsInTwoCopies() {
        List<Core.Unreachable> found = in("stoppedTwice", Core.Unreachable.class);
        assertCopies(found.stream().map(Core.Unreachable::lineage).toList());
    }

    @Test
    void aConstructionInAHelperCalledTwiceIsInTwoCopies() {
        List<Core.Construct> found = in("gradedTwice", Core.Construct.class);
        assertCopies(found.stream().map(Core.Construct::lineage).toList());
    }

    private static void assertCopies(List<OccurrenceLineage> lineages) {
        assertEquals(2, lineages.size(), lineages.toString());
        assertEquals(2, lineages.stream().distinct().count(), lineages.toString());
        assertTrue(lineages.stream().noneMatch(OccurrenceLineage.ORIGINAL::equals),
                "both are in a copy: " + lineages);
    }

    private static <T extends Core> List<T> in(String behavior, Class<T> kind) {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        List<T> out = new ArrayList<>();
        walk(body, e -> {
            if (kind.isInstance(e)) {
                out.add(kind.cast(e));
            }
        });
        assertFalse(out.isEmpty(), out.stream().map(Object::toString)
                .collect(Collectors.joining()));
        return out;
    }

    private static void walk(Core e, Consumer<Core> f) {
        f.accept(e);
        Core.forEachChild(e, child -> walk(child, f));
    }
}
