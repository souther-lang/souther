package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.ReadAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a chain of bindings costs to name, where each one is entered inside the conditional the one
 * before it is read from.
 *
 * <p>A value referenced from another is expanded at the site that reads it rather than left a name,
 * so a chain of bindings that each read the one before it nests: the second's initializer holds the
 * first's binding, the third's holds the second's, and so on down. Naming an initializer computes
 * what its own initializer denotes and what the term grammar calls it, each a fresh walk of it
 * ({@link Terms#inside}) — so where an initializer holds a binding of its own, walking it starts the
 * two again, and a chain nested this deep would be walked a number of times growing with its depth
 * rather than a number growing with its length.
 *
 * <p>Built directly against {@link Terms} rather than through a compiled program, so what is
 * measured is this reading and nothing that parsing, typing or lowering do around it — and held as a
 * count of the walks a reading starts rather than as a time, over several doublings, so the property
 * asked is the shape of the growth and not one point on it.
 */
class AChainOfBindingsStartsWalksWithItsLengthAndNotWithItsPowersTest {

    private static final SourcePos POS = new SourcePos(0, 0);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    /** One level of the chain: the binding it introduces and the expression that introduces it. */
    private record Level(Core.Binder binder, Core expr) {}

    /** Level {@code i}, read inside the conditional {@code previous} is read from where {@code i} is
     *  not the first — the shape a chain takes once each reference to the one before it has been
     *  expanded at the site that reads it. */
    private static Level levelOf(Hir.Binders binders, int i, Level previous) {
        Core.Binder binder = CoreBinders.of(binders.binder("a" + i, POS));
        Core value = previous == null
                ? new Core.Int(0, Type.INT, POS)
                : new Core.Binary(BinOp.ADD,
                        new Core.If(new Core.Bool(true, Type.BOOL, POS), previous.expr(),
                                new Core.Int(0, Type.INT, POS),
                                Core.ForkPlace.asWritten(ConstructOccurrence.unwritten()),
                                Type.INT, POS),
                        new Core.Int(1, Type.INT, POS), ConstructOccurrence.unwritten(),
                        Type.INT, POS);
        Core read = new Core.Read(binder.name(), binder.binding(), Type.INT, POS);
        return new Level(binder, new Core.LetIn(binder, value, read, Type.INT, POS));
    }

    /** A chain nested {@code depth} deep, each level's initializer holding the one before it. */
    private static Core chainOf(int depth) {
        Hir.Binders binders = new Hir.Binders(OWNER);
        Level level = levelOf(binders, 0, null);
        for (int i = 1; i <= depth; i++) {
            level = levelOf(binders, i, level);
        }
        return level.expr();
    }

    /** How many canonical-key walks naming a chain nested {@code depth} deep starts. */
    private static long walksOver(int depth) {
        Terms terms = new Terms(Terms.Of.THE_DISCHARGE_TREE, RuleReadingContext.unshared(
                RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get())),
                ReadAs.THE_COMPILATION_DOES));
        long[] counting = {0};
        Terms.COUNTING_WALKS = counting;
        try {
            terms.bodyKey(chainOf(depth), Denotations.none());
        } finally {
            Terms.COUNTING_WALKS = null;
        }
        return counting[0];
    }

    /**
     * Doubling the depth of the chain, and the reading starts about twice the walks at every step —
     * not a number growing with the depth.
     */
    @Test
    void doublingTheDepthAboutDoublesTheWalks() {
        Map<Integer, Long> walks = new LinkedHashMap<>();
        for (int depth : new int[] {20, 40, 80, 160}) {
            walks.put(depth, walksOver(depth));
        }
        assertTrue(walks.get(40) <= walks.get(20) * 3, "depth 40: " + walks);
        assertTrue(walks.get(80) <= walks.get(40) * 3, "depth 80: " + walks);
        assertTrue(walks.get(160) <= walks.get(80) * 3, "depth 160: " + walks);
    }
}
