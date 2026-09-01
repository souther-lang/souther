package souther.compiler.check;

import souther.compiler.types.BinOp;
import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A rule that steps past the last value of an order, told apart from a rule nothing could read.
 *
 * <p>Two answers were one. {@code value > 5} over an {@code Int} sharpens onto 6, and sharpening
 * asks the order for the count beside the one named; where there is none — the last case of an
 * enumeration, the last day a calendar reaches — the reading answered "no end", which is what it
 * also answers to an equality and to a literal it could not read. The reader's own comment said as
 * much: no end where the order has no count there, which is not the same as the rule being
 * unsatisfiable, and this does not say which.
 *
 * <p>It has to say which. A rule stepping past the end of an order is a rule admitting nothing, and
 * a reading that files it beside the rules it could not read leaves the position looking unbounded
 * — which is the widest thing there is to say about a position that holds no value at all.
 */
class AnEndPastWhereAnOrderStopsIsNotAnEndNobodyReadTest {

    private static final SourcePos NOWHERE = new SourcePos(0, 0);

    private static Hir.Expr whole(long value) {
        return new Hir.IntLit(value, NOWHERE, null);
    }

    /** What {@code op} places, which is an order for every operator this reading takes. Read off
     *  the operator rather than written out, so the reading is asked what the language says the
     *  comparison places. */
    private static ComparisonClaim.Cut ordering(BinOp op) {
        return assertInstanceOf(ComparisonClaim.Cut.class, ComparisonPlacement.of(op),
                () -> op + " orders the values either side of what it names");
    }

    /** The ordinary reading, which sharpens a strict end onto the count beside it. */
    @Test
    void aStrictEndInsideTheOrderLandsOnTheCountBesideIt() {
        InvariantBound.Read read = InvariantBound.at(ordering(BinOp.GT), whole(5), Carrier.WHOLE);

        InvariantBound.Read.AnEnd end = assertInstanceOf(InvariantBound.Read.AnEnd.class, read);
        assertEquals(new InvariantBound(true, Endpoint.inclusive(Count.of(6))), end.bound());
    }

    /**
     * A strict end at the last value of the order, which admits nothing above it.
     *
     * <p>The answer #780 turns on. {@code c > Blue} names the last case its enumeration declares, so
     * the count beside it is one no case is at — and the reading has to say that the rule leaves
     * nothing rather than that it read nothing.
     */
    @Test
    void aStrictEndAtTheLastValueOfTheOrderLeavesNothing() {
        InvariantBound.Read read =
                InvariantBound.at(ordering(BinOp.GT), whole(Long.MAX_VALUE), Carrier.WHOLE);

        assertInstanceOf(InvariantBound.Read.PastWhereTheOrderStops.class, read);
    }

    /** An ordering against something the order has no value for states no end. */
    @Test
    void aLiteralTheOrderDoesNotReadStatesNoEnd() {
        assertInstanceOf(InvariantBound.Read.NoEnd.class,
                InvariantBound.at(ordering(BinOp.GT), new Hir.StringLit("x", NOWHERE, null),
                        Carrier.WHOLE));
    }
}
