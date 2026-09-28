package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A name the affine walk reads twice is followed once.
 *
 * <p>What a name comes to is the value it was given read in the environment it was given in, and
 * both are settled where the binding was made (ADR-0111). So the second occurrence of a name is
 * the first occurrence asked again, and a walk that answers it again does the work again — over a
 * chain of bindings that each read the one before them twice, that is a reading that doubles with
 * every link while the body grows by one.
 *
 * <p>Counted here rather than timed, and counted by the environment rather than by the walk. What
 * a reading is asked is the one thing a caller of this walk decides, so a reading that keeps a
 * tally of what it was asked measures the walk without the walk being told it is measured.
 */
class ANameReadTwiceIsFollowedOnceTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final BindingOwner OWNER = new BindingOwner.OfValue("m", "v");

    /**
     * How many times a name may be followed: once per question the walk has about it.
     *
     * <p>What form the value composes to and what values stand behind the name are two questions,
     * asked by two walks over the same tree, and each asks the environment for itself. Neither is
     * the other asked again, so a name answered twice is answered once apiece — what this holds is
     * that nothing beyond that is asked, which is where a reading that doubles with the chain
     * would show.
     */
    private static final int QUESTIONS = 2;

    /** An environment over a chain of bindings, counting what it is asked to follow. */
    private record Chain(Map<BindingId, Core> given, Map<BindingId, Integer> asked)
            implements AffineForms.Reading<String, Chain> {

        @Override
        public Symbols symbols() {
            return Symbols.none(DefaultStdlib.get());
        }

        @Override
        public PublishedDeclarations published() {
            return PublishedDeclarations.NONE;
        }

        @Override
        public DeclarationKinds kinds() {
            return DeclarationKinds.NONE;
        }

        @Override
        public NewtypeInners inners() {
            return NewtypeInners.NONE;
        }

        /** Nothing is an atom here: what this measures is how often the walk asks to follow a
         *  name, and a leaf rule would answer some of those before it did. */
        @Override
        public LinearForm<String> leafOf(Core e, Chain at) {
            return null;
        }

        @Override
        public Chain inside(Core.LetIn li, Chain at) {
            return at;
        }

        @Override
        public AffineForms.ReadThrough<Chain> readThrough(Core.Read read, Chain at) {
            Core value = given.get(read.binding());
            if (value == null) {
                return null;
            }
            asked.merge(read.binding(), 1, Integer::sum);
            return new AffineForms.ReadThrough<>(value, at);
        }

        @Override
        public List<AffineForms.ReadThrough<Chain>> alternativesOf(Core.Read read, Chain at) {
            return null;
        }

        @Override
        public boolean readsThrough(Core.FieldAccess fa, Chain at) {
            return false;
        }
    }

    private static Core.Read read(BindingId binding) {
        return new Core.Read("a" + binding.ordinal(), binding, Type.INT, POS);
    }

    /** {@code a0 = 1}, then each {@code a[i] = a[i-1] + a[i-1]}, and the last one read. */
    private static Core chainOf(int links, Map<BindingId, Core> given) {
        BindingId first = new BindingId(OWNER, 0);
        given.put(first, new Core.Int(1, Type.INT, POS));
        for (int i = 1; i <= links; i++) {
            Core.Read before = read(new BindingId(OWNER, i - 1));
            given.put(new BindingId(OWNER, i), new Core.Binary(BinOp.ADD, before, before,
                    Core.BinaryReading.AS_THEY_STAND, ConstructOccurrence.unwritten(), Type.INT,
                    POS));
        }
        return read(new BindingId(OWNER, links));
    }

    @Test
    void everyLinkOfAChainEachNamedTwiceIsFollowedOnce() {
        int links = 16;
        Map<BindingId, Core> given = new HashMap<>();
        Core root = chainOf(links, given);
        Map<BindingId, Integer> asked = new HashMap<>();
        Chain reading = new Chain(given, asked);

        AffineForms.outcome(root, reading, reading);

        Map<BindingId, Integer> beyond = new HashMap<>();
        asked.forEach((binding, times) -> {
            if (times > QUESTIONS) {
                beyond.put(binding, times);
            }
        });
        assertEquals(Map.of(), beyond,
                "a name was followed more often than there are questions to ask of it, so what a"
                        + " chain costs to read is what its references multiply out to rather than"
                        + " what it holds");
    }
}
