package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A form read off rules that admit no assignment is at no value, and never at every one.
 *
 * <p><b>The two are the widest and the narrowest thing this can say, and a range holds only one of
 * them.</b> A pair of ends nobody wrote down means the rules place no edge — every value there is —
 * and it is what {@link NumericDomain#boundsOf(LinearForm)} hands back for rules that contradict as
 * readily as for rules that say nothing. So narrowing until nothing is left widens the answer, and
 * every reader meeting it widens whatever it held: the contradiction leaves with it, and a search
 * spends what it is allowed on values these rules already refuse.
 *
 * <p>Held here because this is where the difference exists at all. Everything downstream can only
 * carry an answer this one made.
 */
class AFormOverRulesThatAdmitNothingIsAtNoValueTest {

    private static final String X = "x";
    private static final String Y = "y";

    /** {@code cx·x + cy·y + k}, which is how a rule over two positions is written. */
    private static LinearForm<String> form(long cx, long cy, long k) {
        return LinearForm.<String>constant(ExactRatio.of(k))
                .plus(LinearForm.<String>atom(X).times(ExactRatio.of(cx)))
                .plus(LinearForm.<String>atom(Y).times(ExactRatio.of(cy)));
    }

    private static Map<String, Granularity> whole() {
        Map<String, Granularity> out = new LinkedHashMap<>();
        out.put(X, Granularity.DISCRETE);
        out.put(Y, Granularity.DISCRETE);
        return out;
    }

    /**
     * Two rules closing the region between them, which is what a pair of guards does.
     *
     * <p>{@code y <= x} and {@code y >= x + 1}. Neither says anything about where either position
     * stops, so nothing here is bottom for being written down at an end that crossed: what
     * contradicts is the pair, over both positions at once.
     */
    private static NumericDomain<String> contradicting() {
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .assume(form(-1, 1, 0), Rel.LE, whole())
                .assume(form(1, -1, 1), Rel.LE, whole());
    }

    /** The same two positions with nothing said about them, which is what an open range means. */
    private static NumericDomain<String> silent() {
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
    }

    /** The rules leave the form nowhere, and that is what asking where it runs comes back with. */
    @Test
    void aFormOverRulesThatContradictIsAtNoValue() {
        NumericDomain<String> rules = contradicting();

        assertTrue(rules.isBottom(), "the pair admits no assignment, which is what this is about");
        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                rules.projectionOf(form(1, 1, 0)),
                "so a form over its positions is at no value rather than at every one");
        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                rules.projectionOf(LinearForm.atom(X)),
                "and so is one of them taken as itself, which is the shape every search asks in");
    }

    /**
     * And rules that merely say nothing leave the form every value, which is where an open range
     * belongs.
     *
     * <p>The control the sentence above rests on. Both answers come back with neither end written
     * down, so a check that only read the ends could not tell the two apart — which is the whole
     * defect, written as a test that would pass either way.
     */
    @Test
    void aFormOverRulesThatSayNothingIsAtEveryValue() {
        NumericDomain<String> rules = silent();

        assertEquals(new NumericDomain.FormProjection.Within(NumericDomain.Bounds.OPEN),
                rules.projectionOf(form(1, 1, 0)),
                "nothing is said, so nothing bounds it at either end");
        assertEquals(NumericDomain.Bounds.OPEN,
                assertInstanceOf(NumericDomain.FormProjection.Within.class,
                        rules.projectionOf(LinearForm.atom(X))).bounds(),
                "and the same of one position taken as itself");
    }

    /**
     * The two questions the ends cannot tell apart, asked of one reading each.
     *
     * <p>Beside the pair above rather than a third sentence about either: what is pinned is that the
     * ends agree while the answers do not, which is what says the difference is carried by
     * something other than the ends.
     */
    @Test
    void theEndsSayTheSameThingOfBoth() {
        assertEquals(silent().boundsOf(form(1, 1, 0)), contradicting().boundsOf(form(1, 1, 0)),
                "the ends of both are the pair nobody wrote down");
    }
}
