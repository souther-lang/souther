package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.check.Carrier;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Which counts a carrier holds is the carrier's to say, and every producer of an end asks it.
 *
 * <p>A strict comparison over a carrier that steps is sharpened onto the count beside the one it
 * names: {@code value > 5} is an end at 6. Where the carrier has no count there, there is no end to
 * record — and the reader that sharpens it had its own idea of where counts stop, the range of a
 * {@code long}, which is a fact about one carrier out of five.
 *
 * <p>What that cost: {@code value > Won} sharpened to the place after the last case, which is inside
 * a {@code long} and outside the enumeration. The end became a cut, the cut an obligation, and the
 * obligation was asked for the value it stands for — a case at a place that has none. A `Date` past
 * the last day the calendar has does the same and did so before any of this.
 *
 * <p>The other half of the same rule is that holding a count is a question and not a correction. A
 * date-time's counts sit on a grid at the nanosecond, and what writes one rounds onto that grid — so
 * a reader that asked whether a carrier holds a count and was handed the nearest one it does hold
 * would offer a value between two moments as one of them.
 */
class ACountTheCarrierDoesNotHoldIsNotAnEndTest {

    private static final String STAGE = """
            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won

            data Ok
            data No
            data Verdict = Ok | No
            """;

    @Test
    void aBoundPastTheLastCaseOfAnEnumerationLeavesNoEnd() {
        assertEquals(List.of(), obligations("module example.past\n" + STAGE + """
                data PastEnd = Stage
                    invariant value > Won

                behavior f : (s: PastEnd) -> Verdict
                    constructs Ok
                let f (s) = Ok
                """));
    }

    @Test
    void aBoundBeforeTheFirstCaseOfAnEnumerationLeavesNoEnd() {
        assertEquals(List.of(), obligations("module example.before\n" + STAGE + """
                data BeforeStart = Stage
                    invariant value < Prospecting

                behavior f : (s: BeforeStart) -> Verdict
                    constructs Ok
                let f (s) = Ok
                """));
    }

    /** The same at the end of the calendar, which behaved this way before an enumeration was a
     * carrier: the reader that sharpened the bound stopped where an {@code Int} stops. */
    @Test
    void aBoundPastTheLastDayTheCalendarHasLeavesNoEnd() {
        assertEquals(List.of(), obligations("""
                module example.pastdate

                data Ok
                data No
                data Verdict = Ok | No

                data PastDate = Date
                    invariant value > Date("+999999999-12-31")

                behavior f : (s: PastDate) -> Verdict
                    constructs Ok
                let f (s) = Ok
                """));
    }

    /** And a bound the carrier does hold is still an end, so none of the above passes by drawing
     * nothing anywhere. */
    @Test
    void aBoundInsideTheCasesIsAnEnd() {
        assertEquals(List.of("AT Qualified"), obligations("module example.inside\n" + STAGE + """
                data FromQualified = Stage
                    invariant value >= Qualified

                behavior f : (s: FromQualified) -> Verdict
                    constructs Ok
                let f (s) = Ok
                """));
    }

    /**
     * Halfway between two adjacent moments is a number and not a moment.
     *
     * <p>Null rather than the moment it would be written as. Answered with the nearest one, a class
     * open between two adjacent moments was offered a value at one of its own ends.
     */
    @Test
    void aCountBetweenTwoMomentsIsNotOneOfThem() {
        assertNull(Carrier.MOMENT.onTheGrid(Count.of(new BigDecimal("0.0000000005"))));
        assertEquals(Count.of(new BigDecimal("0.000000001")),
                Carrier.MOMENT.onTheGrid(Count.of(new BigDecimal("0.000000001"))));
    }

    /** Every obligation the one position of {@code source}'s behavior owes, written. */
    private static List<String> obligations(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Ast.Module prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Ast.SpecBehavior spec = (Ast.SpecBehavior) prepared.behaviors().get(0);
        assertNotNull(sigs.get(spec.name()), "the model under test compiles");
        Partitions.Partitioning p =
                Partitions.of(spec, sigs.get(spec.name()), symbols, Exclusions.NONE);
        return p.axes().stream()
                .flatMap(axis -> Partitions.obligationsOf(axis, symbols,
                        p.domains().get(axis.term())).stream())
                .map(o -> o.side() + " " + o.written())
                .toList();
    }
}
