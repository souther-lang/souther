package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A reader that wants what a value is under all its names takes that answer from whoever holds it,
 * and does not take the names off one at a time to work it out again.
 *
 * <p>A compilation answers the terminal for a module's names in one pass, and that answer is only
 * worth having if the readers take it. Each of them is handed the capability by its caller, so a
 * capability that answers the terminal itself and counts what it is asked measures what the reader
 * does without the reader being told it is measured: asked for a name it wraps, the reader is
 * walking the chain.
 *
 * <p>Whether a name is worn at all is the one step a reader may still take, and it is one: the
 * outermost name and nothing under it.
 */
class AReaderOfTheTerminalTakesItAndDoesNotWalkTheNamesTest {

    /** Long enough that a reader walking it is told apart from one taking a step. */
    private static final int LINKS = 30;

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    /** {@code T1 = Int}, {@code Tn = T(n-1)}, answering the terminal itself and counting. */
    private static final class Counting implements NewtypeInners {

        private final Map<TypeKey, Type> wraps = new HashMap<>();

        private final boolean answersTheTerminal;

        int asked;

        int terminals;

        Counting(boolean answersTheTerminal) {
            this.answersTheTerminal = answersTheTerminal;
            wraps.put(key(1), Type.INT);
            for (int i = 2; i <= LINKS; i++) {
                wraps.put(key(i), name(i - 1));
            }
        }

        @Override
        public Type of(TypeKey declaration) {
            asked++;
            return wraps.get(declaration);
        }

        @Override
        public Type terminal(Type type) {
            terminals++;
            return answersTheTerminal ? Type.INT : NewtypeInners.super.terminal(type);
        }
    }

    private static final Type TOP = name(LINKS);

    @Test
    void theBaseIsTaken() {
        Counting inners = new Counting(true);

        assertEquals(Type.INT, TypeOps.base(TOP, inners));
        assertEquals(1, inners.terminals);
        assertEquals(0, inners.asked, "the base walked the names under the one it was asked of");
    }

    @Test
    void theNumericBaseIsTaken() {
        Counting inners = new Counting(true);

        assertEquals(Type.INT, TypeOps.numericBase(TOP, inners));
        assertEquals(1, inners.terminals);
        assertEquals(0, inners.asked,
                "the numeric base walked the names under the one it was asked of");
    }

    @Test
    void theShapeIsReadOffTheTerminal() {
        Counting inners = new Counting(true);

        assertEquals(new Shape.Scalar(Type.Prim.INT),
                TypeView.shapeOf(TOP, inners, SYMBOLS, ScopedDeclarations.kindsOf(SYMBOLS),
                        ScopedDeclarations.of(SYMBOLS)));
        assertEquals(1, inners.terminals);
        assertEquals(0, inners.asked, "the shape walked the names over it");
    }

    /** The order is the terminal's, and whether it is wrapped is the one step off the outside. */
    @Test
    void theOrderTakesTheTerminalAndOneStep() {
        Counting inners = new Counting(true);

        assertEquals(new Ordering.Wrapped(Ordering.LONGS), Ordering.of(TOP, inners,
                ScopedDeclarations.kindsOf(SYMBOLS), ScopedDeclarations.of(SYMBOLS),
                EnumerationListings.NONE));
        assertEquals(1, inners.terminals);
        assertEquals(1, inners.asked, "the order read more than the outermost name");
    }

    /**
     * The control: a capability that does not answer the terminal itself is walked, every name of
     * the chain once — so a reader counted at none above took the answer rather than missing the
     * names.
     */
    @Test
    void aCapabilityThatDoesNotHoldTheTerminalIsWalked() {
        Counting inners = new Counting(false);

        assertEquals(Type.INT, TypeOps.base(TOP, inners));
        assertEquals(LINKS, inners.asked);
    }

    private static TypeKey key(int i) {
        return new TypeKey("m", "T" + i);
    }

    private static Type name(int i) {
        return Type.ref(TypeSymbols.declared(key(i)));
    }
}
