package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * When two borders are one reading of one line.
 *
 * <p>Two readers ask this: the one finding the reading a debt was made from in a later assessment of
 * the same behavior, and the one keeping a reading's lines from holding one line twice. Neither is
 * asking whether every field matches, and the records' own equality answered as though they were —
 * so the day something not about which border this is went into a border, both of them would have
 * started saying two readings of one line are two.
 *
 * <p>What they are asking is the line, where it was met, what it asks of a row at each point, and
 * what such a row would be owed for.
 */
class OneBorderReadTwiceIsOneReadingTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    /**
     * A run stopping where the rules leave the quantity and one stopping there at a line as well are
     * two readings.
     *
     * <p>The values are the same values — the line is where the rules already stop it — so what a
     * row has to do is the same, and a reader comparing the demands alone would call them one. What
     * differs is what a row inside is owed to: with the line there, it answers for that rule as well
     * as for the end, and those are two things to be told about.
     */
    @Test
    void arunOwedToMoreThingsIsAnotherReading() {
        Border rulesOnly = bound(List.of());
        Border andALine = bound(List.of(Parting.by(
                Seam.of(space(), at(1000), Towards.BELOW), aComparison())));

        assertTrue(rulesOnly.demand(PointRole.IN).sameAs(andALine.demand(PointRole.IN)),
                "the run holds the same values either way");
        assertNotEquals(rulesOnly.answer(PointRole.IN).bases(),
                andALine.answer(PointRole.IN).bases(),
                "and a row inside it answers for more once the line is there");
        assertFalse(rulesOnly.sameReadingAs(andALine),
                "so the two are not one reading of one line");
        assertTrue(rulesOnly.sameReadingAs(bound(List.of())),
                "while a reading against itself is one reading");
    }

    /**
     * Two readings that differ only in who can move where a run stops are one reading.
     *
     * <p>Which declarations took the position in travels inside the border, because it is settled
     * where the region is worked out and nothing downstream can work it out again. So it is inside
     * the records' own equality, and the two readers that compare borders would have started saying
     * two readings of one line are two the day a position was narrowed differently at two places.
     * That is the day this method exists for.
     */
    @Test
    void whoCanMoveTheEndIsNoPartOfWhichReadingThisIs() {
        Border narrowed = bound(List.of(), new NarrowedEnds(List.of(), List.of(aDeclaration())));
        Border bare = bound(List.of(), NarrowedEnds.NONE);

        assertNotEquals(bare, narrowed,
                "the two do differ, and this is what they differ in");
        assertTrue(bare.sameReadingAs(narrowed),
                "and neither the line nor what a row at any of its points has to do is any"
                        + " different, so it is one reading of one line");
    }

    /**
     * Two spellings of the place a line is at are one place, so the two readings are one.
     *
     * <p>A level keeps the spelling its rule was written in, because that is what a report writes
     * back. Asked of the records, the border's own place would have told two readings of one line
     * apart over a trailing zero — which is the mistake this comparison exists to stop being made
     * about everything else it holds.
     */
    @Test
    void twoSpellingsOfThePlaceAreOnePlace() {
        Border plain = boundAt(Count.of(100));
        Border spelled = boundAt(new Count(new java.math.BigDecimal("100.00")));

        assertNotEquals(plain, spelled,
                "the two are written differently, and this is what they differ in");
        assertTrue(plain.sameReadingAs(spelled),
                "and a hundred is a hundred, so it is one line met in one place");
    }

    /** And one line met at two positions is two readings, whatever each of them owes. */
    @Test
    void oneLineMetAtTwoPositionsIsTwoReadings() {
        assertFalse(bound(List.of()).sameReadingAs(
                        Border.at(aLineAt("w.b", 100), aBound(),
                                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(100)),
                                        Endpoint.inclusive(Count.of(1000))))),
                "the same rule met at another position is another reading of it");
    }

    /** A bound at a hundred, leaving everything up to a thousand, told about {@code parted}. */
    private static Border bound(List<Parting> parted) {
        return bound(parted, NarrowedEnds.NONE);
    }

    /** The same, told which declarations took the ends of the position in. */
    private static Border bound(List<Parting> parted, NarrowedEnds narrowed) {
        return Border.at(aLineAt("w.a", 100), aBound(),
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(100)),
                        Endpoint.inclusive(Count.of(1000))),
                parted, narrowed);
    }

    /** The same bound, with its line written as {@code at}. */
    private static Border boundAt(Count at) {
        AxisId axis = new AxisId("weigh", "w.a");
        return Border.at(BoundaryTarget.at(
                        new BorderQuantity.OfACoordinate(axis,
                                new NumericTerm.ValueOf(TermPath.of(axis.term())),
                                TermOrders.itself(WHOLE)),
                        new Level.OnACarrier(WHOLE, at)),
                aBound(),
                new NumericDomain.Bounds(Endpoint.inclusive(at),
                        Endpoint.inclusive(Count.of(1000))));
    }

    /** A declaration that could have moved where the position stops. */
    private static souther.compiler.types.TypeSymbol.AtModule aDeclaration() {
        return TypeSymbols.declared(new TypeKey("example.weigh", "Held"));
    }

    private static LevelSpace space() {
        return LevelSpace.onACarrier(WHOLE);
    }

    private static Level at(int value) {
        return new Level.OnACarrier(WHOLE, Count.of(value));
    }

    private static BoundaryTarget aLineAt(String path, int value) {
        AxisId axis = new AxisId("weigh", path);
        return BoundaryTarget.at(
                new BorderQuantity.OfACoordinate(axis,
                        new NumericTerm.ValueOf(TermPath.of(axis.term())),
                        TermOrders.itself(WHOLE)),
                at(value));
    }

    /** The clause the bound is written in, which is only an identity here. */
    private static OriginRef aBound() {
        return new OriginRef.InvariantOrigin(new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("example.weigh", "Amount")), 0),
                Optional.of(new ClauseName("cap")))), 0, Towards.ABOVE, true);
    }

    /** A line of a body, for a place to be parted by something other than the bound. */
    private static AuthoredLine aComparison() {
        return new AuthoredLine(new RuleRef.Comparison("weigh",
                new souther.compiler.types.CoverageOrigin("example.weigh", 2, 0,
                        souther.compiler.types.CoverageConstruct.BINARY)),
                0, new LineFacts(true, true, false), List.of());
    }
}
