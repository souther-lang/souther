package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What is known of one term is not given up for what is unknown beside it.
 *
 * <p>Three things say where a term's values run, and they are not one thing. What the declarations
 * relate it to is one; what its own position was read to hold is another; what the term guarantees
 * of itself is a third, and a value a caller has fixed it at is a fourth. Asked as one question of
 * the reading that relates positions, the other three are answered only where that reading happens
 * to have a name for the coordinate — and where it does not, an answer that was in hand is dropped.
 *
 * <p>And it gives them up for whole reasons at a time. The clauses relating positions are read one
 * value at a time, so a coordinate that reading cannot name is one it can say nothing about — and an
 * answer that gave up on its account would give up on every coordinate beside it too: two positions
 * each known to be at least none would add up to something with no floor.
 *
 * <p>So all four go in beside each other and the answer is read out of the four together. Taking one
 * in only narrows, so what comes back is never wider than what the term alone says — which is the
 * direction the whole boundary is written in. What these hold to is the answer and not the way it is
 * arrived at: a fact in hand may not be dropped because the mechanism asked for it declined.
 */
class WhatIsKnownOfOneTermSurvivesWhatIsUnknownBesideItTest {

    /** A position ordered by its own values rather than counted, whose type places a floor. */
    private static final String TEXT = """
            module example.text

            data Code = String
                invariant atLeastA = value >= "A"

            data P = { c: Code, n: Int }

            data Taken

            behavior take : (p: P) -> Taken
            """;

    /** A collection no clause counts, beside a number a clause bounds. */
    private static final String UNCOUNTED = """
            module example.uncounted

            data P = { xs: List<Int>, n: Int }
                invariant none = n >= 0

            data Taken

            behavior take : (p: P) -> Taken
            """;

    /**
     * A floor on a position the arithmetic has no word for is still where its values stop.
     *
     * <p>Read only through the reading that relates positions, a text position has no coordinate to
     * be related by and comes back with nothing said about it — so a line drawn below the floor is
     * one nothing refuses, and the rows for it are asked for at values the position does not hold.
     */
    @Test
    void aFloorOnATextPositionIsWhereItsValuesStop() {
        Read read = read(TEXT);
        Position c = read.inputs().at(TermPath.of("p").then("c"));

        assertEquals(c.numericDomain(),
                read.quantities().runsBetween(c.term()),
                "the position's own answer and the quantity's are about the same values");
    }

    /** And a value fixed at a coordinate no clause names is where that term stands. */
    @Test
    void aTermFixedAtAValueRunsBetweenThatValue() {
        Read read = read(UNCOUNTED);
        NumericTerm size = size(read, "xs");

        assertEquals(at(2, 2), read.quantities().given(size, count(2)).runsBetween(size));
    }

    /** And a form keeps what is known of each of its terms where one of them is unknown. */
    @Test
    void aFormKeepsWhatIsKnownOfTheTermsBesideAnUnknownOne() {
        Read read = read(UNCOUNTED);
        NumericTerm size = size(read, "xs");
        NumericTerm n = read.inputs().at(TermPath.of("p").then("n")).term();
        Map<NumericTerm, BigDecimal> coefs = new LinkedHashMap<>();
        coefs.put(n, BigDecimal.ONE);
        coefs.put(size, BigDecimal.ONE);

        NumericDomain.Bounds runs = read.quantities()
                .runsBetween(new NumericDomain.LinearForm<>(BigDecimal.ZERO, coefs));

        assertEquals(Endpoint.inclusive(count(0)), runs.min(),
                "each of them is at least none, so their sum is");
    }

    /** Two positions the record relates, beside a collection no clause counts. */
    private static final String RELATED_BESIDE_AN_UNCOUNTED = """
            module example.beside

            data N = Int
                invariant atLeastNone = value >= 0
                invariant atMostFive  = value <= 5

            data P =
                { xs: List<Int>
                , x: N
                , y: N
                }
                invariant together = x.value + y.value >= 5

            data Taken

            behavior take : (p: P) -> Taken
            """;

    /**
     * And the rule relating two terms survives a third the reading cannot name.
     *
     * <p>A term the reading has no coordinate for is one no relation can be asked about, and that is
     * the whole of what it costs. Asked as two totals instead — everything each term is on its own,
     * against everything the relations leave the whole form — the unnameable term makes the
     * relational total say nothing and takes the relation between the two beside it with it. Meeting
     * does not distribute over addition, so the unit an answer is assembled at is which answer comes
     * out.
     *
     * <p>Held here and not at a report, because no report reaches it today. A coordinate the reading
     * of a value never named is in practice a count nothing takes, and a position whose values are
     * held inside something the walk does not reach into is set aside before any line is drawn on a
     * form over it. What is being held is the boundary's own answer, which is what the next reader
     * of it will get.
     */
    @Test
    void aRuleRelatingTwoTermsSurvivesAThirdThatCannotBeNamed() {
        Read read = read(RELATED_BESIDE_AN_UNCOUNTED);
        NumericTerm size = size(read, "xs");
        NumericTerm x = read.inputs().at(TermPath.of("p").then("x")).term();
        NumericTerm y = read.inputs().at(TermPath.of("p").then("y")).term();
        Map<NumericTerm, BigDecimal> coefs = new LinkedHashMap<>();
        coefs.put(size, BigDecimal.ONE);
        coefs.put(x, BigDecimal.ONE);
        coefs.put(y, BigDecimal.ONE);

        NumericDomain.Bounds runs = read.quantities()
                .runsBetween(new NumericDomain.LinearForm<>(BigDecimal.ZERO, coefs));

        assertEquals(Endpoint.inclusive(count(5)), runs.min(),
                "the two the record relates come to five, and nothing is negative beside them");
    }

    /** Three counts, two of them related and the third bounded on its own. */
    private static final String THREE_COUNTS = """
            module example.three

            data P =
                { a: List<Int>
                , b: List<Int>
                , c: List<Int>
                }
                invariant oneOfAB = List.length(a) + List.length(b) >= 1
                invariant capC    = List.length(c) <= 10

            data Taken

            behavior take : (p: P) -> Taken
            """;

    /**
     * And a term the rules name, whose floor only the term itself states, does not undo them.
     *
     * <p>A count is never negative and no clause writes that down, so the reading of the clauses has
     * a coordinate for it and no floor under it. Asked for a bound on the three together, that
     * reading may put the third as far below nothing as it likes and answers with no floor at all —
     * and met afterwards against what each of them is on its own, the rule holding the first two at
     * one is gone. Projecting is not distributive over meeting either: what the rules and the terms
     * leave together is narrower than each of them projected and then met.
     */
    @Test
    void aFloorOnlyTheTermStatesDoesNotUndoTheRuleBesideIt() {
        Read read = read(THREE_COUNTS);
        Map<NumericTerm, BigDecimal> coefs = new LinkedHashMap<>();
        coefs.put(size(read, "a"), BigDecimal.ONE);
        coefs.put(size(read, "b"), BigDecimal.ONE);
        coefs.put(size(read, "c"), BigDecimal.ONE);

        NumericDomain.Bounds runs = read.quantities()
                .runsBetween(new NumericDomain.LinearForm<>(BigDecimal.ZERO, coefs));

        assertEquals(Endpoint.inclusive(count(1)), runs.min(),
                "two of them come to one, and the third is never negative");
    }

    private static NumericTerm size(Read read, String field) {
        TermPath at = TermPath.of("p").then(field);
        return new NumericTerm.SizeOf(souther.compiler.check.NumericMeasures.takenOf(
                read.inputs().at(at).type(), read.symbols()), at);
    }

    private static Count count(int at) {
        return new Count(BigDecimal.valueOf(at));
    }

    private static NumericDomain.Bounds at(int least, int most) {
        return new NumericDomain.Bounds(Endpoint.inclusive(count(least)),
                Endpoint.inclusive(count(most)));
    }

    private record Read(InputDomain inputs, Symbols symbols) {
        Quantities quantities() {
            return inputs.quantities(symbols);
        }
    }

    private static Read read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("take")).findFirst().orElseThrow();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        return new Read(InputDomain.of(spec, sigs.get("take"), symbols,
                ReadAs.THE_COMPILATION_DOES), symbols);
    }
}
