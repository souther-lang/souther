package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk over a body adds no edge for a name nothing declares, and cannot be handed one nothing has
 * read.
 *
 * <p>The two were one thing to a walk that asks whether the name is answered — {@code !(v instanceof
 * Denoting)} was true of both — and they are not one thing. A name nothing declares is a mistake in
 * the source, reported where it is written, and a walk carrying on past it is what lets the
 * definitions beside it still be checked. A name nothing has read is a pass that did not answer its
 * own nodes, and a walk carrying on past that reads the module as though the author had written an
 * unknown name.
 *
 * <p>They used to be told apart by asking {@link Hir.Var#answered()}, which refused the second. They
 * are told apart by the representation now: a name nothing has read is {@link Ast.Var}, which a walk
 * below {@code Resolve} takes no argument of. So the refusal is not a check these walks make — it is
 * a call that does not compile, and what is left to ask them is the first half.
 */
class AWalkTellsAnUnansweredNameFromAnUnreadOneTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final BindingId BOUND =
            new BindingId(new BindingOwner.OfValue("demo", "go"), 0);

    /** A name resolution answered with the binding {@code BOUND}. */
    private static Hir.Var bound() {
        return new Hir.Var.Denoting(WrittenName.of("n", POS), new ValueName.Local("n", BOUND),
                new ReachName.Bare("n"), WrittenName.of("n", POS).region());
    }

    /** A name resolution read and found nothing for. */
    private static Hir.Var unanswered(String spelling) {
        WrittenName name = WrittenName.of(spelling, POS);
        return new Hir.Var.Unanswered(name, name.region());
    }

    // --- the two answers, at the one place that tells them apart ---

    @Test
    void answeredPartsTheTwoWhereEveryWalkUsedToPartThemItself() {
        assertEquals(Hir.Var.Denoting.class, bound().answered().getClass());
        assertEquals(null, unanswered("n").answered(),
                "nothing declares it, so a walk has no edge to add and carries on");
    }

    /**
     * And there is no third for it to part off. What a walk here is handed has been read, whatever
     * it turned out to name — the state that said nobody had looked is the other representation's,
     * and {@link Hir.Var} permits only these two.
     */
    @Test
    void thereIsNoStateHereForANameNothingHasRead() {
        assertEquals(Set.of(Hir.Var.Denoting.class, Hir.Var.Unanswered.class),
                Set.of(Hir.Var.class.getPermittedSubclasses()));
    }

    // --- and at a walk, which is where it matters ---

    /** {@code ValueCycles} builds the graph of which values read which. */
    @Test
    void aNameNothingDeclaresIsNoEdge() {
        Set<String> read = new LinkedHashSet<>();
        ValueCycles.valuesRead(unanswered("nosuch"), new LinkedHashMap<>(), read);

        assertEquals(Set.of(), read);
    }

    /** {@code HelperParams} asks which binding a name is a use of. Same pair. */
    @Test
    void theSamePairHoldsWhereAWalkAsksWhichBindingAUseIsOf() {
        Hir.Binder binder = new Hir.Binder(bound().written(), BOUND, POS);

        assertTrue(HelperParams.mentions(bound(), binder));
        assertEquals(false, HelperParams.mentions(unanswered("n"), binder));
    }
}
