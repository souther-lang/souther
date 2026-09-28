package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.query.ReadAs;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What extending an environment makes does not depend on how many bindings it already holds.
 *
 * <p>This is the reason {@link BindingMap} exists, and it is a claim about cost that no answer an
 * environment gives can show: a copy of the whole map and a shared trie answer every lookup alike.
 * So it is asked of the structure — how many nodes the extended environment has that the one it
 * extended did not — at several sizes, and a copy would fail it at every one of them.
 */
class ExtendingAnEnvironmentMakesOnlyWhatTheExtensionAddsTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "b");

    /** A path through the trie is at most as deep as the hash is wide, plus the leaf and the
     * position the binding took in the order. */
    private static final int MOST_AN_EXTENSION_MAY_MAKE = 10;

    private static final int[] SIZES = {100, 400, 1600, 6400};

    private static BindingId id(int ordinal) {
        return new BindingId(OWNER, ordinal);
    }

    @Test
    void anEnvironmentExtendedOnceMakesTheSameWhateverItHolds() {
        for (int size : SIZES) {
            BindingMap<Integer> held = BindingMap.empty();
            for (int i = 0; i < size; i++) {
                held = held.with(id(i), i);
            }
            BindingMap<Integer> extended = held.with(id(size), size);

            int made = extended.nodesNotSharedWith(held);
            assertTrue(made >= 1, "extending by a new binding makes something, at " + size);
            assertTrue(made <= MOST_AN_EXTENSION_MAY_MAKE,
                    "extending an environment of " + size + " made " + made + " nodes");
        }
    }

    @Test
    void aBindingReplacedMakesNoNewPlaceInTheOrder() {
        BindingMap<Integer> held = BindingMap.<Integer>empty().with(id(0), 0).with(id(1), 1);
        int made = held.with(id(1), 9).nodesNotSharedWith(held);
        assertTrue(made >= 1 && made <= MOST_AN_EXTENSION_MAY_MAKE, "made " + made);
    }

    @Test
    void theMeasureTellsACopyOfTheWholeMapFromAnExtension() {
        for (int size : SIZES) {
            Map<BindingId, Integer> plain = new HashMap<>();
            BindingMap<Integer> held = BindingMap.empty();
            for (int i = 0; i < size; i++) {
                plain.put(id(i), i);
                held = held.with(id(i), i);
            }
            plain.put(id(size), size);
            BindingMap<Integer> copied = BindingMap.from(plain);

            assertTrue(copied.nodesNotSharedWith(held) >= size,
                    "a map rebuilt from scratch shares nothing with the one it was copied from, at "
                            + size);
        }
    }

    @Test
    void aScopeExtendedMakesTheSameWhateverItHolds() {
        for (int size : SIZES) {
            Scope held = Scope.NONE;
            for (int i = 0; i < size; i++) {
                held = held.with(id(i), "n" + i, Type.INT);
            }
            Scope extended = held.with(id(size), "last", Type.INT);

            int made = nodesOf(extended.bindings()).nodesNotSharedWith(nodesOf(held.bindings()));
            assertTrue(made >= 1 && made <= MOST_AN_EXTENSION_MAY_MAKE,
                    "extending a scope of " + size + " made " + made + " nodes");
            assertEquals(size, held.bindings().size());
        }
    }

    @Test
    void aDenotationsExtendedMakesTheSameWhateverItHolds() {
        Terms terms = new Terms(Terms.Of.THE_DISCHARGE_TREE, RuleReadingContext.unshared(
                RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get())),
                ReadAs.THE_COMPILATION_DOES));
        FactSubject subject = terms.placeSubject(id(0));
        Term term = terms.placeTerm(id(0));
        for (int size : new int[] {100, 400, 1600}) {
            Denotations held = Denotations.none();
            for (int i = 0; i < size; i++) {
                held = held.location(id(i), subject, term);
            }
            Denotations extended = held.location(id(size), subject, term);

            int made = nodesOf(extended.bound()).nodesNotSharedWith(nodesOf(held.bound()));
            assertTrue(made >= 1 && made <= MOST_AN_EXTENSION_MAY_MAKE,
                    "extending a denotation of " + size + " made " + made + " nodes");
        }
    }

    private static BindingMap<?> nodesOf(Map<BindingId, ?> bindings) {
        return (BindingMap<?>) bindings;
    }
}
