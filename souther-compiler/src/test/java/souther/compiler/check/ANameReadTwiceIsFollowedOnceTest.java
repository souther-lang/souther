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
        public DeclarationAccess declarations() {
            return DeclarationAccess.NONE;
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
        public ValueStanding.ReadThrough<Chain> readThrough(Core.Read read, Chain at) {
            Core value = given.get(read.binding());
            if (value == null) {
                return null;
            }
            asked.merge(read.binding(), 1, Integer::sum);
            return new ValueStanding.ReadThrough<>(value, at);
        }

        @Override
        public List<ValueStanding.ReadThrough<Chain>> alternativesOf(Core.Read read, Chain at) {
            return null;
        }

        @Override
        public boolean readsThrough(Core.FieldAccess fa, Chain at) {
            return false;
        }
    }

    /**
     * An environment whose atoms make a product of two of them one, counting each product it is
     * asked to make and each it is told was made. {@code x} is the one atom: a name nothing was
     * given.
     */
    private record Multiplying(Map<BindingId, Core> given, Map<BindingId, Integer> asked,
                               Map<Core.Binary, Integer> made, Map<Core, Integer> toldAsAProduct,
                               Map<Core, Integer> toldAsAnyOther)
            implements AffineForms.Reading<String, Multiplying> {

        @Override
        public Symbols symbols() {
            return Symbols.none(DefaultStdlib.get());
        }

        @Override
        public DeclarationAccess declarations() {
            return DeclarationAccess.NONE;
        }

        @Override
        public LinearForm<String> leafOf(Core e, Multiplying at) {
            return Core.withoutStanding(e) instanceof Core.Read read
                    && !given.containsKey(read.binding()) ? LinearForm.atom("x") : null;
        }

        @Override
        public Multiplying inside(Core.LetIn li, Multiplying at) {
            return at;
        }

        @Override
        public ValueStanding.ReadThrough<Multiplying> readThrough(Core.Read read,
                                                                  Multiplying at) {
            Core value = given.get(read.binding());
            if (value == null) {
                return null;
            }
            asked.merge(read.binding(), 1, Integer::sum);
            return new ValueStanding.ReadThrough<>(value, at);
        }

        @Override
        public List<ValueStanding.ReadThrough<Multiplying>> alternativesOf(Core.Read read,
                                                                           Multiplying at) {
            return null;
        }

        @Override
        public boolean readsThrough(Core.FieldAccess fa, Multiplying at) {
            return false;
        }

        @Override
        public LinearForm<String> productOf(Core.Binary operation, LinearForm<String> left,
                                            LinearForm<String> right) {
            made.merge(operation, 1, Integer::sum);
            return LinearForm.atom("product");
        }

        @Override
        public void composedAsAProduct(Core operation, LinearForm<String> form,
                                       List<LinearForm<String>> operands) {
            toldAsAProduct.merge(operation, 1, Integer::sum);
        }

        @Override
        public void composed(Core operation, LinearForm<String> form,
                             List<LinearForm<String>> operands) {
            toldAsAnyOther.merge(operation, 1, Integer::sum);
        }
    }

    /** {@code a0} is the atom {@code x}, then each {@code a[i] = a[i-1] * a[i-1]}, and the last
     *  one read; the products are returned in the order they are written. */
    private static Core productChainOf(int links, Map<BindingId, Core> given,
                                       List<Core.Binary> products) {
        BindingId atom = new BindingId(OWNER, 0);
        for (int i = 1; i <= links; i++) {
            Core.Read before = read(i == 1 ? atom : new BindingId(OWNER, i - 1));
            Core.Binary product = new Core.Binary(BinOp.MUL, before, before,
                    Core.BinaryReading.AS_THEY_STAND, ConstructOccurrence.unwritten(), Type.INT,
                    POS);
            products.add(product);
            given.put(new BindingId(OWNER, i), product);
        }
        return read(new BindingId(OWNER, links));
    }

    /**
     * A product the reading's atoms make is made from the forms the walk composed of the factors,
     * and told once for each time it is made, in its own way and in no other. A walk that read the
     * factors again to make it, or told it beside the others, would show here as a product made
     * more often than there are questions to ask of it, or told twice.
     */
    @Test
    void everyProductOfAChainIsMadeFromTheWalksFactorsAndToldAsAProduct() {
        int links = 16;
        Map<BindingId, Core> given = new HashMap<>();
        List<Core.Binary> products = new java.util.ArrayList<>();
        Core root = productChainOf(links, given, products);
        Multiplying reading = new Multiplying(given, new HashMap<>(), new HashMap<>(),
                new HashMap<>(), new HashMap<>());

        AffineForms.outcome(root, reading, reading);

        assertEquals(Map.of(), reading.toldAsAnyOther(),
                "a product the reading made is told as one, and as no other operation");
        assertEquals(reading.made(), reading.toldAsAProduct(),
                "each product made is told, once for each time it was made");
        Map<Core.Binary, Integer> beyond = new HashMap<>();
        reading.made().forEach((product, times) -> {
            if (times > QUESTIONS) {
                beyond.put(product, times);
            }
        });
        assertEquals(Map.of(), beyond, "a product was made more often than there are questions to"
                + " ask of it, so what a chain costs is what its references multiply out to");
        assertEquals(links, reading.made().size(), "every product of the chain was made");
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
