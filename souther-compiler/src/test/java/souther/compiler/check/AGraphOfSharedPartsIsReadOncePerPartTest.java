package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.BlockReason;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.time.Duration;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A value named twice by the value before it, over a chain of them, is a graph as long as the chain
 * and a tree that doubles at each link. Everything that answers a question of such a graph answers it
 * once per part: what a term is ordered by and whether two terms are equal, and what an origin names
 * and is made from.
 *
 * <p>The chains here are longer than any tree of them could be walked, so a reader that recursed
 * into the parts instead does not finish.
 */
class AGraphOfSharedPartsIsReadOncePerPartTest {

    private static final int LINKS = 200;

    private static final Duration AS_LONG_AS_THE_GRAPH = Duration.ofSeconds(10);

    /** {@code c(n) = c(n-1) + c(n-1)} from {@code seed}, built by {@code interner}. */
    private static Term doubled(Term.Interner interner, long seed) {
        Term at = interner.written(seed);
        for (int link = 0; link < LINKS; link++) {
            at = interner.operator(BinOp.ADD, at, at);
        }
        return at;
    }

    @Test
    void twoTermsBuiltApartAreEqualAndOrderedLevelWithoutWritingEitherOut() {
        Term one = doubled(new Term.Interner(), 1);
        Term same = doubled(new Term.Interner(), 1);
        Term other = doubled(new Term.Interner(), 2);

        assertTimeoutPreemptively(AS_LONG_AS_THE_GRAPH, () -> {
            assertEquals(one, same);
            assertEquals(0, Term.inOneOrder(one, same));
            assertNotEquals(one, other);
            assertEquals(Integer.signum(Term.inOneOrder(one, other)),
                    -Integer.signum(Term.inOneOrder(other, one)));
        });
    }

    /** {@code o(n) = o(n-1) + o(n-1)} over {@code leaf}. */
    private static ValueOrigin<String> doubled(ValueOrigin<String> leaf) {
        ValueOrigin<String> at = leaf;
        for (int link = 0; link < LINKS; link++) {
            at = new ValueOrigin.Composed<>(List.of(at, at));
        }
        return at;
    }

    @Test
    void anOriginNamesItsPositionsAndWhatItIsMadeFromOncePerPart() {
        ValueOrigin<String> named = doubled(new ValueOrigin.IsAPosition<>("x"));
        ValueOrigin<String> made = doubled(new ValueOrigin.MadeFromAPosition<>("y"));
        ValueOrigin<String> applied = doubled(new ValueOrigin.Applied<>(
                new ValueName.Helper("m", "f"), List.of(new ValueOrigin.IsAPosition<>("z"))));

        assertTimeoutPreemptively(AS_LONG_AS_THE_GRAPH, () -> {
            assertEquals(Set.of("x"), named.positions());
            assertNull(named.madeFrom());
            assertEquals("y", made.madeFrom());
            assertEquals(new BlockReason.RuleAboutADerivedValue(),
                    UnreadComparison.notAboutOwnValues(made));
            assertEquals(new BlockReason.UnreadComparisonForm(),
                    UnreadComparison.notAboutOwnValues(applied));
        });
    }
}
