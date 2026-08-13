package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk over a body adds no edge for a name nothing declares, and refuses one nothing has read.
 *
 * <p>The two are one thing to a walk that asks whether the name is answered — {@code !(v instanceof
 * Denoting)} is true of both — and they are not one thing. A name nothing declares is a mistake in
 * the source, reported where it is written, and a walk carrying on past it is what lets the
 * definitions beside it still be checked. A name nothing has read is a pass that did not answer its
 * own nodes, and a walk carrying on past that reads the module as though the author had written an
 * unknown name: the pass that left it goes unmentioned, and every walk below agrees with it.
 *
 * <p>So {@link Ast.Var#answered()} is where the two part company, and a walk asks it rather than
 * deciding for itself. Which is the whole of issue #703 in one method: the question was being
 * answered again at each consumer.
 */
class AWalkTellsAnUnansweredNameFromAnUnreadOneTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final BindingId BOUND =
            new BindingId(new BindingOwner.OfValue("demo", "go"), 0);

    /** A name resolution answered with the binding {@code BOUND}. */
    private static Ast.Var bound() {
        return Ast.Var.denoting("n", new ValueName.Local("n", BOUND), new ReachName.Bare("n"), POS);
    }

    // --- the three states, at the one place that tells them apart ---

    @Test
    void answeredPartsTheThreeWhereEveryWalkUsedToPartThemItself() {
        assertEquals(Ast.Var.Denoting.class, bound().answered().getClass());
        assertEquals(null, Ast.Var.written("n", POS).unanswered().answered(),
                "nothing declares it, so a walk has no edge to add and carries on");
        assertTrue(assertThrows(IllegalStateException.class,
                        () -> Ast.Var.written("n", POS).answered())
                .getMessage().contains("before it was resolved"),
                "nothing has read it, which is this compiler's mistake and not the author's");
    }

    // --- and at a walk, which is where it matters ---

    /** {@code ValueCycles} builds the graph of which values read which. */
    @Test
    void aNameNothingDeclaresIsNoEdge() {
        Set<String> read = new LinkedHashSet<>();
        ValueCycles.valuesRead(Ast.Var.written("nosuch", POS).unanswered(),
                new LinkedHashMap<>(), read);

        assertEquals(Set.of(), read);
    }

    @Test
    void aNameNothingHasReadIsRefusedRatherThanCountedAmongThem() {
        assertThrows(IllegalStateException.class,
                () -> ValueCycles.valuesRead(Ast.Var.written("nosuch", POS),
                        new LinkedHashMap<>(), new LinkedHashSet<>()));
    }

    /** {@code HelperParams} asks which binding a name is a use of. Same pair. */
    @Test
    void theSamePairHoldsWhereAWalkAsksWhichBindingAUseIsOf() {
        Ast.Binder binder = new Ast.Binder.Bound(bound().written(), BOUND, POS);

        assertTrue(HelperParams.mentions(bound(), binder));
        assertEquals(false, HelperParams.mentions(
                Ast.Var.written("n", POS).unanswered(), binder));
        assertThrows(IllegalStateException.class,
                () -> HelperParams.mentions(Ast.Var.written("n", POS), binder));
    }
}
