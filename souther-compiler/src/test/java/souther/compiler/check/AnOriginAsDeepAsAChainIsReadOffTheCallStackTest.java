package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.ValueName;
import souther.test.OnItsOwnStack;

import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An origin is as deep as a chain of declarations — a record holding the one before it in a field is
 * one layer per record — so every question asked of one is answered without going as deep on the
 * call stack, and without copying what is under a layer once for each layer above it.
 */
class AnOriginAsDeepAsAChainIsReadOffTheCallStackTest {

    /** Small next to what the JVM gives a thread by default, so a walk as deep as the chain fails
     *  here on any platform this runs on. */
    private static final long STACK = 256L << 10;

    private static final int DEEP = 100_000;

    /** {@code depth} layers of {@code layer} over {@code leaf}. */
    private static ValueOrigin<String> under(int depth, ValueOrigin<String> leaf,
                                             Function<ValueOrigin<String>, ValueOrigin<String>> layer) {
        ValueOrigin<String> at = leaf;
        for (int i = 0; i < depth; i++) {
            at = layer.apply(at);
        }
        return at;
    }

    private static ValueOrigin<String> composed(ValueOrigin<String> over) {
        return new ValueOrigin.Composed<>(List.of(over));
    }

    private static ValueOrigin<String> chosen(ValueOrigin<String> over) {
        return new ValueOrigin.OneOf<>(List.of(), List.of(over));
    }

    @Test
    void everyQuestionOfAnOriginAsDeepAsAChainIsAnsweredOnASmallStack() {
        ValueOrigin<String> named = under(DEEP, new ValueOrigin.IsAPosition<>("x"),
                AnOriginAsDeepAsAChainIsReadOffTheCallStackTest::composed);
        ValueOrigin<String> made = under(DEEP, new ValueOrigin.MadeFromAPosition<>("y"),
                AnOriginAsDeepAsAChainIsReadOffTheCallStackTest::composed);
        ValueOrigin<String> chosenAmongMade = under(DEEP, made,
                AnOriginAsDeepAsAChainIsReadOffTheCallStackTest::chosen);
        ValueOrigin<String> chosenAmongNamed = under(DEEP, named,
                AnOriginAsDeepAsAChainIsReadOffTheCallStackTest::chosen);

        Throwable thrown = OnItsOwnStack.run("questions of a deep origin", STACK, () -> {
            assertEquals(Set.of("x"), named.positions());
            assertNull(named.madeFrom());
            assertFalse(named.madeByAnOperation());
            assertEquals("y", made.madeFrom());
            assertTrue(made.madeByAnOperation());
            assertEquals("y", chosenAmongMade.madeFrom());
            assertTrue(chosenAmongMade.madeByAnOperation());
            assertEquals(Set.of("x"), chosenAmongNamed.positions());
            assertFalse(chosenAmongNamed.madeByAnOperation());
        });
        if (thrown != null) {
            throw new AssertionError("a question of a deep origin threw", thrown);
        }
    }

    /** A position that counts how often a set asks where it goes. */
    private record Counted(int n, AtomicLong asked) {

        @Override
        public int hashCode() {
            asked.incrementAndGet();
            return Integer.hashCode(n);
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Counted other && other.n == n;
        }
    }

    /**
     * {@code o(n) = position(n) + o(n-1)}: each layer names one position of its own and everything
     * under it. A set per layer holding everything under it hands each position up once for every
     * layer above it, which is a number of insertions quadratic in the depth.
     */
    @Test
    void aPositionUnderEveryLayerIsCollectedOnceAndNotOncePerLayer() {
        int depth = 2_000;
        AtomicLong asked = new AtomicLong();
        ValueOrigin<Counted> at = new ValueOrigin.IsAPosition<>(new Counted(0, asked));
        for (int n = 1; n <= depth; n++) {
            at = new ValueOrigin.Composed<>(List.of(
                    new ValueOrigin.IsAPosition<>(new Counted(n, asked)), at));
        }
        ValueOrigin<Counted> deep = at;

        Set<Counted> positions = OnItsOwnStack.ask("the positions of a deep origin", STACK,
                deep::positions);

        assertEquals(depth + 1, positions.size());
        assertTrue(asked.get() <= 2L * (depth + 1),
                "a set asked " + asked.get() + " times where " + (depth + 1)
                        + " positions were collected");
    }

    /**
     * A part reached under a later part and again under an earlier one is read where the earlier one
     * reaches it, which is where it was first written.
     */
    @Test
    void aSharedPartReachedAgainUnderAnEarlierPartIsReadThere() {
        ValueOrigin<String> shared = composed(new ValueOrigin.IsAPosition<>("shared"));
        ValueOrigin<String> earlier = new ValueOrigin.Composed<>(List.of(
                shared, new ValueOrigin.IsAPosition<>("earlier")));
        ValueOrigin<String> whole = new ValueOrigin.Composed<>(List.of(earlier, shared));

        assertEquals(List.of("shared", "earlier"), List.copyOf(whole.positions()));
    }

    @Test
    void anOperationOverAPositionsOwnValuesIsOneButArithmeticOverThemIsNot() {
        ValueOrigin<String> applied = new ValueOrigin.Applied<>(new ValueName.Helper("m", "f"),
                List.of(new ValueOrigin.IsAPosition<>("z")));

        assertTrue(applied.madeByAnOperation());
        assertFalse(composed(new ValueOrigin.IsAPosition<>("z")).madeByAnOperation());
        assertFalse(new ValueOrigin.OneOf<>(List.of(),
                List.of(applied, new ValueOrigin.Written<>())).madeByAnOperation());
    }
}
