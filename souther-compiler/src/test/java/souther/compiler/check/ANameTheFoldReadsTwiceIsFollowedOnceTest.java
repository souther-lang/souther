package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.util.AbstractMap;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A name the constant fold reads twice is followed once, however the environment answers it.
 *
 * <p>A binding reaches this walk two ways. The tree may still hold it, and then the value and the
 * environment it was written in come with it; or the shape of the clause consumed it, and then what
 * it was given is what the reading was told. Those are two places one answer is kept, not two
 * questions — a binding has one value either way — so a fold that follows the second afresh at each
 * occurrence walks what a chain of names multiplies out to, over an environment that grows by one
 * entry per link.
 *
 * <p>Counted by the environment rather than by the walk, as the affine reading is
 * ({@link ANameReadTwiceIsFollowedOnceTest}): what the walk asks the environment is the one thing a
 * caller decides, so an environment that keeps a tally of what it was asked measures the walk
 * without the walk being told it is measured.
 */
class ANameTheFoldReadsTwiceIsFollowedOnceTest {

    private static final SourcePos POS = new SourcePos(0, 0);

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    /** Long enough that following a name afresh at each occurrence is a walk of a different order,
     *  and short enough that the answer is an ordinary number. */
    private static final int LINKS = 20;

    /** An environment that answers as the one it was made from, counting what it is asked for. */
    private static final class Counting extends AbstractMap<BindingId, Denotations.Means> {

        private final Map<BindingId, Denotations.Means> of;

        private final Map<BindingId, Integer> asked = new HashMap<>();

        Counting(Map<BindingId, Denotations.Means> of) {
            this.of = of;
        }

        @Override
        public Denotations.Means get(Object key) {
            asked.merge((BindingId) key, 1, Integer::sum);
            return of.get(key);
        }

        @Override
        public Set<Entry<BindingId, Denotations.Means>> entrySet() {
            return of.entrySet();
        }
    }

    @Test
    void everyLinkOfAChainTheEnvironmentAnswersForIsFollowedOnce() {
        PathEngine engine = new PathEngine(
                RuleReadingContext.unshared(
                        RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get())),
                        souther.compiler.query.ReadAs.THE_COMPILATION_DOES),
                Terms.Of.THE_DISCHARGE_TREE);
        Hir.Binders binders = new Hir.Binders(OWNER);

        // Nothing of the chain stands in the tree: every name is one the reading was told about,
        // which is the half a fold used to follow afresh.
        Core.Binder first = CoreBinders.of(binders.binder("x0", POS));
        Denotations at = bound(engine, first, new Core.Int(1, Type.INT, POS), Denotations.none());
        Core.Binder last = first;
        for (int i = 1; i <= LINKS; i++) {
            Core.Binder next = CoreBinders.of(binders.binder("x" + i, POS));
            at = bound(engine, next, doubled(last), at);
            last = next;
        }

        Counting counting = new Counting(at.bound());
        Optional<Object> folded = CoreConstantEval
                .against(Symbols.none(DefaultStdlib.get()), new Denotations(counting))
                .eval(read(last));

        assertEquals(Optional.of(1L << LINKS), folded,
                "the chain this counts over did not fold, so the count says nothing");
        Map<BindingId, Integer> beyond = new HashMap<>();
        counting.asked.forEach((binding, times) -> {
            if (times > 1) {
                beyond.put(binding, times);
            }
        });
        assertEquals(Map.of(), beyond,
                "a name was followed more than once, so what a chain of names costs to fold is"
                        + " what its occurrences multiply out to rather than what it holds");
    }

    /** {@code x[i-1] + x[i-1]}: one name, read twice. */
    private static Core doubled(Core.Binder before) {
        return new Core.Binary(BinOp.ADD, read(before), read(before),
                Core.BinaryReading.AS_THEY_STAND, ConstructOccurrence.unwritten(), Type.INT, POS);
    }

    private static Denotations bound(PathEngine engine, Core.Binder binder, Core value,
                                     Denotations at) {
        return engine.bindLet(new Core.LetIn(binder, Type.INT, value, read(binder), Type.INT, POS),
                Known.top(), at).at();
    }

    private static Core read(Core.Binder binder) {
        return new Core.Read(binder.name(), binder.binding(), Type.INT, POS);
    }
}
