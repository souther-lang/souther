package souther.compiler.numeric;

import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Rules read of one value, asked about as rules of something that holds it.
 *
 * <p>A caller holding the readings of several values at once has to say what they leave together,
 * and each of those readings is about its own value's positions. What a rule says is a relation
 * between numbers and it says the same thing whatever the numbers are called, so carrying one
 * across is a renaming and saying two of them together is keeping both — neither is a second
 * derivation of anything, and that is what makes an answer assembled this way the same answer.
 */
class RulesReadOfOneValueAreCarriedAndSaidTogetherTest {

    private static LinearForm<String> atom(String a) {
        return LinearForm.<String>atom(a);
    }

    private static LinearForm<String> num(long n) {
        return LinearForm.<String>constant(BigDecimal.valueOf(n));
    }

    private static Map<String, Granularity> whole(String... atoms) {
        Map<String, Granularity> out = new LinkedHashMap<>();
        for (String each : atoms) {
            out.put(each, Granularity.DISCRETE);
        }
        return out;
    }

    /** The rules of one value, under the names the thing holding it calls those numbers by. */
    @Test
    void aRuleSaysTheSameThingUnderOtherNames() {
        NumericDomain<String> read = NumericDomain.<String>top()
                .assume(atom("x").plus(atom("y")).minus(num(5)), Rel.LE, whole("x", "y"))
                .assume(atom("x"), Rel.GE, whole("x"))
                .assume(atom("y"), Rel.GE, whole("y"));

        NumericDomain<String> carried = read.over(name -> "p." + name);

        assertEquals(Endpoint.inclusive(Count.of(5)),
                carried.boundsOf(atom("p.x").plus(atom("p.y"))).max());
        assertEquals(Endpoint.inclusive(Count.of(0)), carried.boundsOf(atom("p.x")).min());
    }

    /**
     * A relation through a number the caller cannot spell still holds the two it relates apart.
     *
     * <p>Which is why carrying one across may not drop it. The rule below says nothing about either
     * of the names on its own, and taking it away leaves their difference unbounded — the one
     * direction a reader downstream cannot see.
     */
    @Test
    void aRelationThroughAnUnspellableNumberIsCarriedToo() {
        NumericDomain<String> read = NumericDomain.<String>top()
                .assume(atom("x").minus(atom("hidden")), Rel.LE, whole("x", "hidden"))
                .assume(atom("hidden").minus(atom("y")), Rel.LE, whole("hidden", "y"));

        NumericDomain<String> carried =
                read.over(name -> name.equals("hidden") ? "<1>" : "p." + name);

        assertTrue(carried.entails(atom("p.x").minus(atom("p.y")), Rel.LE),
                "what the two of them are held apart by went through the number in between");
        // And nothing else says it. Half the relation is half of nothing: neither rule names both
        // of them, so a carrying that kept only the rules it could spell would leave this open.
        assertFalse(NumericDomain.<String>top()
                        .assume(atom("p.x").minus(atom("p.hidden")), Rel.LE, whole("p.x", "p.hidden"))
                        .entails(atom("p.x").minus(atom("p.y")), Rel.LE),
                "one half of the relation proves nothing about the pair");
    }

    /** Two names for one number is a different rule, not a wider reading of this one. */
    @Test
    void twoPositionsCalledOneNameIsRefused() {
        NumericDomain<String> read = NumericDomain.<String>top()
                .assume(atom("x").minus(atom("y")), Rel.LE, whole("x", "y"));

        assertThrows(IllegalArgumentException.class, () -> read.over(_ -> "one"));
    }

    /** Saying two readings together says everything either of them says. */
    @Test
    void whatIsSaidTogetherIsEverythingBothSay() {
        NumericDomain<String> one = NumericDomain.<String>top()
                .assume(atom("a").minus(num(3)), Rel.LE, whole("a"));
        NumericDomain<String> other = NumericDomain.<String>top()
                .assume(atom("b").minus(num(4)), Rel.LE, whole("b"));

        Bounds sum = one.meet(other).boundsOf(atom("a").plus(atom("b")));

        assertEquals(Endpoint.inclusive(Count.of(7)), sum.max());
        assertNull(sum.min());
    }

    /**
     * Whichever way round, and however often.
     *
     * <p>The property the whole arrangement leans on: what the rules leave is a function of which
     * rules were said and not of how a caller came by them. A reading that depended on the order
     * would make which parameter was read first part of what the model says.
     */
    @Test
    void sayingThemTheOtherWayRoundSaysTheSameThing() {
        NumericDomain<String> one = NumericDomain.<String>top()
                .assume(atom("a").plus(atom("b")).minus(num(5)), Rel.LE, whole("a", "b"));
        NumericDomain<String> other = NumericDomain.<String>top()
                .assume(atom("a").minus(num(1)), Rel.GE, whole("a"));

        LinearForm<String> asked = atom("a").plus(atom("b"));

        assertEquals(one.meet(other).boundsOf(asked), other.meet(one).boundsOf(asked));
        assertEquals(one.meet(other).boundsOf(asked),
                one.meet(other).meet(one).boundsOf(asked),
                "a rule said twice is the same rule");
    }

    /** Two readings that cannot both hold leave nothing, which is what a caller acts on. */
    @Test
    void twoReadingsThatContradictLeaveNothing() {
        NumericDomain<String> one = NumericDomain.<String>top()
                .assume(atom("a").minus(num(3)), Rel.LE, whole("a"));
        NumericDomain<String> other = NumericDomain.<String>top()
                .assume(atom("a").minus(num(9)), Rel.GE, whole("a"));

        assertTrue(one.meet(other).isBottom());
    }

    /** One number spaced two ways is the naming and the typing disagreeing, and neither is the
     *  safer of the two to pick. */
    @Test
    void oneNumberSpacedTwoWaysIsRefused() {
        NumericDomain<String> stepping = NumericDomain.<String>top()
                .assume(atom("a"), Rel.GE, whole("a"));
        NumericDomain<String> filling = NumericDomain.<String>top()
                .assume(atom("a"), Rel.GE, Map.of("a", Granularity.DENSE));

        assertThrows(IllegalStateException.class, () -> stepping.meet(filling));
    }
}
