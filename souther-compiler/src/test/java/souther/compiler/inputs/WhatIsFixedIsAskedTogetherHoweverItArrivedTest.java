package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Fixing a position refines what is asked, and what is asked is the whole of what was fixed.
 *
 * <p>Three searches condition this input's rules, each fixing positions in an order of its own. What
 * the rules leave may not depend on that order, or two of them asking the same thing get two answers
 * and neither is wrong about anything a reader could check. So the answers are held to an algebra:
 * fixing nothing changes nothing, fixing twice is fixing both, and the two orders agree.
 *
 * <p>Held of what is proved empty as well as of what is left. A proof reached by one route and not
 * by another would make which question was asked first into something a caller can see, and the
 * routes are a cache and an arithmetic — neither of which the model has anything to do with.
 *
 * <p>Not a check that the reading is made a particular way. Conditioning that kept every relation
 * would satisfy this however it was carried, and that is the point: what is fixed here is the
 * meaning, so an implementation may change under it.
 */
class WhatIsFixedIsAskedTogetherHoweverItArrivedTest {

    /** Two fields each running from none to five, held together at five by the record. */
    private static final String SOURCE = """
            module example.together

            data N = Int
                invariant atLeastNone = value >= 0
                invariant atMostFive  = value <= 5

            data P = { x: N, y: N }
                invariant together = x.value + y.value <= 5

            data Taken

            behavior take : (p: P) -> Taken
            """;

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("p").then("x"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("p").then("y"));

    /**
     * The relation crosses the boundary, which is the whole point of asking here.
     *
     * <p>Read a position at a time, {@code y} runs to five whatever {@code x} holds. The record says
     * otherwise, and with {@code x} at four there is one value left for {@code y}.
     */
    @Test
    void fixingOnePositionNarrowsTheOneItIsRelatedTo() {
        Quantities read = quantities();

        assertEquals(bounds(0, 5), read.runsBetween(Y));
        assertEquals(bounds(0, 1), read.given(X, count(4)).runsBetween(Y));
    }

    /** A form is bounded by the rule relating its positions, and not by the box of the two. */
    @Test
    void aFormIsBoundedByWhatRelatesItsPositions() {
        assertEquals(bounds(0, 5), quantities().runsBetween(sum()));
    }

    @Test
    void fixingNothingAsksTheSameThing() {
        Quantities read = quantities();

        assertEquals(read.runsBetween(sum()), read.given(Map.of()).runsBetween(sum()));
        assertEquals(read.runsBetween(Y), read.given(Map.of()).runsBetween(Y));
    }

    @Test
    void fixingTwiceIsFixingBoth() {
        Quantities read = quantities();
        Quantities apart = read.given(X, count(2)).given(Y, count(1));
        Quantities together = read.given(fixing(X, 2, Y, 1));

        assertEquals(together.runsBetween(sum()), apart.runsBetween(sum()));
        assertEquals(together.runsBetween(X), apart.runsBetween(X));
        assertEquals(together.emptiness(), apart.emptiness());
    }

    @Test
    void theOrderTheyWereFixedInDoesNotShow() {
        Quantities read = quantities();
        Quantities one = read.given(X, count(2)).given(Y, count(1));
        Quantities other = read.given(Y, count(1)).given(X, count(2));

        assertEquals(one.runsBetween(sum()), other.runsBetween(sum()));
        assertEquals(one.runsBetween(X), other.runsBetween(X));
        assertEquals(one.emptiness(), other.emptiness());
    }

    /** And the same of a pair the rules refuse, which is proved either way round. */
    @Test
    void theOrderDoesNotShowWhereNothingIsLeftEither() {
        Quantities read = quantities();
        Quantities one = read.given(X, count(4)).given(Y, count(4));
        Quantities other = read.given(Y, count(4)).given(X, count(4));

        assertTrue(one.emptiness().isPresent(), "x = 4 beside y = 4 comes to eight, and the record"
                + " holds the pair at five");
        assertEquals(one.emptiness(), other.emptiness());
    }

    /** One position holds one value, so fixing it twice fixes it at nothing. */
    @Test
    void twoValuesAtOnePositionLeaveNothing() {
        Quantities read = quantities().given(X, count(1)).given(X, count(2));

        assertEquals(new EmptyInput.TwoValuesAtOnePosition(X, count(1), count(2)),
                read.emptiness().orElseThrow());
    }

    /** A value outside where the position runs is proved impossible against where it runs. */
    @Test
    void aValueOutsideWhereThePositionRunsLeavesNothing() {
        assertTrue(quantities().given(X, count(9)).emptiness().isPresent());
    }

    /**
     * Nothing proved is not a value proved to exist.
     *
     * <p>The pair below is one the rules do leave, and the answer is empty. Read the other way, a
     * search would close no branch it should and open every branch it should not — so what this
     * holds is that the two readings are told apart at all.
     */
    @Test
    void aPairTheRulesLeaveIsNotProvedEmpty() {
        assertEquals(java.util.Optional.empty(),
                quantities().given(fixing(X, 2, Y, 1)).emptiness());
    }

    /**
     * A term at a path this input does not have is the caller's mistake.
     *
     * <p>Not an emptiness and not an unbounded answer: either would be a bug wearing the words of
     * something the model said.
     */
    @Test
    void atermOfAnotherInputIsRefused() {
        NumericTerm elsewhere = new NumericTerm.ValueOf(TermPath.of("q").then("x"));

        assertThrows(IllegalArgumentException.class,
                () -> quantities().runsBetween(elsewhere));
        assertThrows(IllegalArgumentException.class,
                () -> quantities().given(elsewhere, count(1)));
    }

    /** And a path this input does have is not refused, so the check above is about the path. */
    @Test
    void atermOfThisInputIsNotRefused() {
        assertNotEquals(null, quantities().runsBetween(X));
    }

    private static NumericDomain.LinearForm<NumericTerm> sum() {
        Map<NumericTerm, BigDecimal> coefs = new LinkedHashMap<>();
        coefs.put(X, BigDecimal.ONE);
        coefs.put(Y, BigDecimal.ONE);
        return new NumericDomain.LinearForm<>(BigDecimal.ZERO, coefs);
    }

    private static Map<NumericTerm, Count> fixing(NumericTerm one, int at,
                                                  NumericTerm other, int also) {
        Map<NumericTerm, Count> out = new LinkedHashMap<>();
        out.put(one, count(at));
        out.put(other, count(also));
        return out;
    }

    private static Count count(int at) {
        return new Count(BigDecimal.valueOf(at));
    }

    private static NumericDomain.Bounds bounds(int least, int most) {
        return new NumericDomain.Bounds(
                souther.compiler.numeric.Endpoint.inclusive(count(least)),
                souther.compiler.numeric.Endpoint.inclusive(count(most)));
    }

    /**
     * A count is never negative, and no clause anywhere writes that down.
     *
     * <p>The one fixing the declarations cannot be told about. Their reading settles positions and a
     * count taken of one is not a position it settles, so nothing there refuses this — what refuses
     * it is what the term guarantees of itself, which is part of what is asked here.
     */
    @Test
    void aCountFixedBelowNoneLeavesNothingThoughNoClauseSaysSo() {
        Read read = read(BAG, "take");
        NumericTerm size = new NumericTerm.SizeOf(
                souther.compiler.check.NumericMeasures.takenOf(
                        read.inputs().at(TermPath.of("b").then("xs")).type(), read.symbols()),
                TermPath.of("b").then("xs"));
        Quantities asked = read.inputs().quantities(read.symbols());

        assertTrue(asked.given(size, count(-1)).emptiness().isPresent());
        assertEquals(java.util.Optional.empty(), asked.given(size, count(1)).emptiness());
    }

    /** A collection nothing bounds, so only what a count guarantees of itself is left to refuse
     *  one. */
    private static final String BAG = """
            module example.bag

            data Bag = { xs: List<String> }

            data Taken

            behavior take : (b: Bag) -> Taken
            """;

    private record Read(InputDomain inputs, Symbols symbols) {}

    private static Quantities quantities() {
        Read read = read(SOURCE, "take");
        return read.inputs().quantities(read.symbols());
    }

    private static Read read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        return new Read(InputDomain.of(spec, sigs.get(behavior), symbols,
                ReadAs.THE_COMPILATION_DOES), symbols);
    }
}
