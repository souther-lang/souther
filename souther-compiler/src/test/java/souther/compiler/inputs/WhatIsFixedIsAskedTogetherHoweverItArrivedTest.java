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

    /**
     * Two counts the record relates, so that fixing one says something about the other.
     *
     * <p>A count is a number of a position and not a position, and the two are filed under different
     * names by the reading that makes them. A fixing that reached only the first left a rule over two
     * counts unconditioned while the same rule was read whole when it was asked about — so the answer
     * to "where does this run" knew the relation and the answer to "what is left once that is fixed"
     * did not.
     */
    private static final String COUNTED = """
            module example.counted

            data Possible =
                { accounts: List<Int>
                , contacts: List<Int>
                }
                invariant oneOfThem =
                    List.length(accounts) + List.length(contacts) >= 1

            data Taken

            behavior take : (p: Possible) -> Taken
            """;

    @Test
    void fixingOneCountNarrowsTheCountItIsRelatedTo() {
        Read read = read(COUNTED, "take");
        Quantities asked = read.inputs().quantities(read.symbols());
        NumericTerm accounts = size(read, "accounts");
        NumericTerm contacts = size(read, "contacts");

        assertEquals(new Count(BigDecimal.ZERO),
                asked.runsBetween(contacts).min().at(), "nothing bounds it on its own");
        assertEquals(new Count(BigDecimal.ONE),
                asked.given(accounts, count(0)).runsBetween(contacts).min().at());
    }

    @Test
    void twoCountsTheRuleRefusesTogetherLeaveNothing() {
        Read read = read(COUNTED, "take");
        Quantities asked = read.inputs().quantities(read.symbols());
        NumericTerm accounts = size(read, "accounts");
        NumericTerm contacts = size(read, "contacts");

        assertTrue(asked.given(accounts, count(0)).given(contacts, count(0))
                .emptiness().isPresent());
    }

    /** And the algebra holds of a count as much as of a value, which is where the two came apart. */
    @Test
    void theAlgebraHoldsOfACountToo() {
        Read read = read(COUNTED, "take");
        Quantities asked = read.inputs().quantities(read.symbols());
        NumericTerm accounts = size(read, "accounts");
        NumericTerm contacts = size(read, "contacts");
        Quantities one = asked.given(accounts, count(0)).given(contacts, count(2));
        Quantities other = asked.given(contacts, count(2)).given(accounts, count(0));
        Quantities together = asked.given(fixing(accounts, 0, contacts, 2));

        assertEquals(together.runsBetween(contacts), one.runsBetween(contacts));
        assertEquals(together.runsBetween(accounts), other.runsBetween(accounts));
        assertEquals(one.runsBetween(accounts), other.runsBetween(accounts));
        assertEquals(one.emptiness(), other.emptiness());
        assertEquals(together.emptiness(), one.emptiness());
    }

    /**
     * Settling a position does not read the declarations again, whenever it is asked about.
     *
     * <p>A settling is an equality on one number taken onto everything else the clauses came to,
     * and the reading states it that way itself at the end of its own work. So the clauses have
     * been read when the input was read, and a caller fixing a position — or fixing four of them
     * one at a time and asking after each — is arriving where the reading already is rather than
     * paying for it again.
     *
     * <p>Counted rather than timed. What is held is the shape of the thing: a search that fixes a
     * position per step down a box would read a declaration per step, and how fast one reading is
     * would decide whether that mattered.
     */
    @Test
    void settlingAPositionDoesNotReadTheDeclarationsAgain() {
        Read read = read(SOURCE, "take");
        Quantities asked = read.inputs().quantities(read.symbols());
        long before = souther.compiler.check.FieldDomains.readingsMade();

        Quantities twice = asked.given(X, count(1)).given(Y, count(1));
        twice.runsBetween(sum());
        twice.runsBetween(Y);
        twice.emptiness();

        assertEquals(before, souther.compiler.check.FieldDomains.readingsMade());
    }

    /**
     * And what it answers is what reading them again with the same thing settled would answer.
     *
     * <p>Which is why not reading them again is allowed. The two are one statement or they are two,
     * and stating a settling in two places is how they would come apart — so what the cheap way says
     * is held against what the reading itself says, at a position and over a form and about whether
     * anything is left.
     */
    @Test
    void whatASettlingLeavesIsWhatReadingItInWouldLeave() {
        Read read = read(SOURCE, "take");
        souther.compiler.types.TypeSymbol name = souther.compiler.types.TypeSymbols.declared(
                new souther.compiler.types.TypeKey(read.symbols().module(), "P"));
        Hir.Data data = (Hir.Data) read.symbols().declarations().declaration(name.key());
        souther.compiler.check.FieldDomains whole = souther.compiler.check.FieldDomains.of(
                name, data, read.symbols(), ReadAs.THE_COMPILATION_DOES);

        for (int at = 0; at <= 5; at++) {
            Map<String, Count> settled = Map.of("x", count(at));
            souther.compiler.check.FieldDomains readIn = souther.compiler.check.FieldDomains.of(
                    name, data, read.symbols(), ReadAs.THE_COMPILATION_DOES, settled);
            souther.compiler.check.FieldDomains.Settled taken = whole.given(Map.of(
                    new souther.compiler.check.FieldDomains.Coordinate("x", false), count(at)));

            assertEquals(readIn.holdsNothing().isPresent(), taken.holdsNothing().isPresent(),
                    "whether anything is left, with x at " + at);
            assertEquals(readIn.leftAt("y", false), taken.boundsOf(Map.of(
                            new souther.compiler.check.FieldDomains.Coordinate("y", false),
                            BigDecimal.ONE)),
                    "where y runs, with x at " + at);
        }
    }

    private static NumericTerm size(Read read, String field) {
        TermPath at = TermPath.of("p").then(field);
        return new NumericTerm.SizeOf(souther.compiler.check.NumericMeasures.takenOf(
                read.inputs().at(at).type(), read.symbols()), at);
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
