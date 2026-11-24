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

    /**
     * An environment that is, where {@code afresh}, a new object each time a value is read in it,
     * and a name that stands for the one thing in all of them
     * ({@link AffineForms.Reading#standingOf}). Which is what an environment is that enters the
     * binding of a call's parameter at each visit of the call.
     */
    private record Afresh(Map<BindingId, Core> given, Map<BindingId, Integer> asked,
                          boolean afresh) implements AffineForms.Reading<String, Afresh.Where> {

        /** One environment, told from another by being another object. */
        private static final class Where {}

        private Where read(Where at) {
            return afresh ? new Where() : at;
        }

        @Override
        public Symbols symbols() {
            return Symbols.none(DefaultStdlib.get());
        }

        @Override
        public DeclarationAccess declarations() {
            return DeclarationAccess.NONE;
        }

        /** A name nothing was given is the one atom, so that no part of the chain is a constant
         *  the fold settles before the names are read. */
        @Override
        public LinearForm<String> leafOf(Core e, Where at) {
            return Core.withoutStanding(e) instanceof Core.Read read
                    && !given.containsKey(read.binding()) ? LinearForm.atom("x") : null;
        }

        @Override
        public Where inside(Core.LetIn li, Where at) {
            return read(at);
        }

        @Override
        public ValueStanding.ReadThrough<Where> readThrough(Core.Read read, Where at) {
            Core value = given.get(read.binding());
            if (value == null) {
                return null;
            }
            asked.merge(read.binding(), 1, Integer::sum);
            return new ValueStanding.ReadThrough<>(value, read(at));
        }

        @Override
        public Object standingOf(Core.Read read, Where at) {
            return given.get(read.binding());
        }

        @Override
        public List<ValueStanding.ReadThrough<Where>> alternativesOf(Core.Read read, Where at) {
            return null;
        }

        @Override
        public boolean readsThrough(Core.FieldAccess fa, Where at) {
            return false;
        }
    }

    /** How often each name of a chain headed by an atom is asked about, where each value is read
     *  in {@code afresh} an environment or in the one it was reached in. */
    private static Map<BindingId, Integer> askedOverAChain(int links, boolean afresh) {
        Map<BindingId, Core> given = new HashMap<>();
        Core root = chainOf(links, given);
        // The head is the atom and not the number one, which the fold would settle unread.
        given.remove(new BindingId(OWNER, 0));
        Map<BindingId, Integer> asked = new HashMap<>();
        Afresh reading = new Afresh(given, asked, afresh);

        AffineForms.outcome(root, new Afresh.Where(), reading);
        return asked;
    }

    /**
     * A name is the same question wherever the reading says it stands for the same thing, so an
     * environment that is a new object at every step costs a name no more than one that is not.
     * Keyed on the environment, a chain of names each reached by two ways would read the bottom
     * of it once for every way down.
     */
    @Test
    void aNameIsFollowedAsOftenInAnEnvironmentMadeAfreshAsInOneThatIsNot() {
        // Enough links that the count doubles at each one where the key is the environment.
        int links = 4;

        assertEquals(askedOverAChain(links, false), askedOverAChain(links, true),
                "a name was followed again because it was reached in an environment made afresh,"
                        + " which tells the reading nothing about the name");
    }

    /**
     * An environment that is a name for the meaning it gives {@code TARGET}: what is read is the
     * value that meaning is, and what the name stands for is that value as an object. An
     * environment of another name that gives the same value is another environment that gives
     * the same meaning.
     */
    private record Meaning(Map<String, Core> given, Map<Integer, Integer> readAs)
            implements AffineForms.Reading<String, String> {

        static final BindingId TARGET = new BindingId(OWNER, 1);

        @Override
        public Symbols symbols() {
            return Symbols.none(DefaultStdlib.get());
        }

        @Override
        public DeclarationAccess declarations() {
            return DeclarationAccess.NONE;
        }

        /** A name nothing was given is the atom of its own, so that what two meanings read as is
         *  told apart by the form. */
        @Override
        public LinearForm<String> leafOf(Core e, String at) {
            if (!(Core.withoutStanding(e) instanceof Core.Read read)
                    || read.binding().equals(TARGET)) {
                return null;
            }
            readAs.merge(read.binding().ordinal(), 1, Integer::sum);
            return LinearForm.atom("a" + read.binding().ordinal());
        }

        @Override
        public String inside(Core.LetIn li, String at) {
            return at;
        }

        @Override
        public ValueStanding.ReadThrough<String> readThrough(Core.Read read, String at) {
            if (!read.binding().equals(TARGET)) {
                return null;
            }
            return new ValueStanding.ReadThrough<>(given.get(at), at);
        }

        @Override
        public Object standingOf(Core.Read read, String at) {
            return given.get(at);
        }

        @Override
        public List<ValueStanding.ReadThrough<String>> alternativesOf(Core.Read read, String at) {
            return null;
        }

        @Override
        public boolean readsThrough(Core.FieldAccess fa, String at) {
            return false;
        }
    }

    /**
     * What a name came to is shared between the environments that give it one meaning and between
     * no others: the same value in two environments is read once, and two values the one name
     * stands for in two environments are each read as what they are.
     */
    @Test
    void aNameCameToIsSharedOnlyBetweenEnvironmentsThatGiveItOneMeaning() {
        Core one = read(new BindingId(OWNER, 10));
        Core other = read(new BindingId(OWNER, 11));
        Map<String, Core> given = Map.of("first", one, "same", one, "different", other);
        Map<Integer, Integer> readAs = new HashMap<>();
        Meaning reading = new Meaning(given, readAs);
        BindingWalk.Answers<AffineForms.Outcome<String, String>> answers = new BindingWalk.Answers<>();
        FoldedValue.Kept folds = new FoldedValue.Kept();
        Core name = read(Meaning.TARGET);

        LinearForm<String> first = AffineForms.of(name, "first", reading, answers, folds);
        LinearForm<String> same = AffineForms.of(name, "same", reading, answers, folds);
        LinearForm<String> different = AffineForms.of(name, "different", reading, answers, folds);

        assertEquals(LinearForm.atom("a10"), first);
        assertEquals(first, same);
        assertEquals(LinearForm.atom("a11"), different,
                "a name that stands for another value in another environment is read as that value");
        // Each value is read as what it is once, however many environments give it: the first
        // two environments give one value, and the third another.
        assertEquals(Map.of(10, 1, 11, 1), readAs);
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
