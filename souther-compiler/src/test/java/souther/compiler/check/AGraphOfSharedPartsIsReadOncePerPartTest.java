package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.BlockReason;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;
import java.util.SequencedMap;
import java.util.function.IntToLongFunction;
import java.util.concurrent.atomic.AtomicLong;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A value named twice by the value before it, over a chain of them, is a graph as long as the chain
 * and a tree that doubles at each link. Everything that answers a question of such a graph answers it
 * once per part: what a term is ordered by and whether two terms are equal, and what an origin names
 * and is made from.
 *
 * <p>What is counted is the work a question does at three chain lengths, each double the last. A
 * reader that answers once per part does twice the work for twice the chain, and one that recurses
 * into the parts instead does two to the power of the links added.
 */
class AGraphOfSharedPartsIsReadOncePerPartTest {

    private static final int[] LINKS = {5, 10, 20};

    /** {@code c(n) = c(n-1) + c(n-1)} from {@code seed}, built by {@code interner}. */
    private static Term doubled(Term.Interner interner, long seed, int links) {
        Term at = interner.written(seed);
        for (int link = 0; link < links; link++) {
            at = interner.operator(BinOp.ADD, at, at);
        }
        return at;
    }

    private static void assertDoublesAtMost(IntToLongFunction workAt) {
        SequencedMap<Integer, Long> work = new LinkedHashMap<>();
        for (int links : LINKS) {
            work.put(links, workAt.applyAsLong(links));
        }
        Growth.eachAtMost(work, 3, 1);
    }

    @Test
    void twoTermsBuiltApartAreEqualAndOrderedLevelWithoutWritingEitherOut() {
        assertDoublesAtMost(links -> {
            Term one = doubled(new Term.Interner(), 1, links);
            Term same = doubled(new Term.Interner(), 1, links);
            Term other = doubled(new Term.Interner(), 2, links);

            long[] counting = {0};
            Term.COUNTING_PAIRS = counting;
            try {
                assertEquals(one, same);
                assertEquals(0, Term.inOneOrder(one, same));
                assertNotEquals(one, other);
                assertEquals(Integer.signum(Term.inOneOrder(one, other)),
                        -Integer.signum(Term.inOneOrder(other, one)));
            } finally {
                Term.COUNTING_PAIRS = null;
            }
            return counting[0];
        });
    }

    /** A position that counts how often it is asked whether it is another, or hashed. */
    private static final class Counted {
        private final AtomicLong asked;

        Counted(AtomicLong asked) {
            this.asked = asked;
        }

        @Override
        public int hashCode() {
            asked.incrementAndGet();
            return 1;
        }

        @Override
        public boolean equals(Object other) {
            asked.incrementAndGet();
            return other instanceof Counted;
        }
    }

    /** {@code o(n) = o(n-1) + o(n-1)} over {@code leaf}. */
    private static <K> ValueOrigin<K> doubled(ValueOrigin<K> leaf, int links) {
        ValueOrigin<K> at = leaf;
        for (int link = 0; link < links; link++) {
            at = new ValueOrigin.Composed<>(List.of(at, at));
        }
        return at;
    }

    @Test
    void anOriginNamesItsPositionsOncePerPart() {
        assertDoublesAtMost(links -> {
            AtomicLong asked = new AtomicLong();
            ValueOrigin<Counted> named = doubled(
                    new ValueOrigin.IsAPosition<>(new Counted(asked)), links);

            assertEquals(1, named.positions().size());
            return asked.get();
        });
    }

    /** What an origin is made from, and why a comparison of it is not read, answered over a graph
     *  whose parts are shared. Not counted: nothing in these answers asks a position anything. */
    @Test
    void anOriginMadeFromAPositionAnswersWhatItIsMadeFrom() {
        ValueOrigin<String> named = doubled(new ValueOrigin.IsAPosition<>("x"), 3);
        ValueOrigin<String> made = doubled(new ValueOrigin.MadeFromAPosition<>("y"), 3);
        ValueOrigin<String> applied = doubled(new ValueOrigin.Applied<>(
                new ValueName.Helper("m", "f"), List.of(new ValueOrigin.IsAPosition<>("z"))), 3);

        assertEquals(Set.of("x"), named.positions());
        assertNull(named.madeFrom());
        assertEquals("y", made.madeFrom());
        assertEquals(new BlockReason.RuleAboutADerivedValue(),
                UnreadComparison.notAboutOwnValues(made));
        assertEquals(new BlockReason.UnreadComparisonForm(),
                UnreadComparison.notAboutOwnValues(applied));
    }
}
