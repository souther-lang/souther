package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AReadingOfAPosition;
import souther.compiler.meaning.AuthoredPointMapping;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.coverage.Numberings;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;
import souther.compiler.check.Carrier;
import souther.compiler.check.Clause;
import souther.compiler.check.DeclaredLine;
import souther.compiler.check.InvariantStatementId;
import souther.compiler.check.PartId;
import souther.compiler.check.ClauseName;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.NarrowedBounds;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
     * A comparison's run stopping where the rules leave the quantity and one stopping there at a
     * line as well are one reading.
     *
     * <p>The values are the same values — the line is where the rules already stop it — so what a
     * row has to do is the same. What differs is what else a row inside answers for, and for a
     * comparison a body wrote, where the run beside its line stops is the reading's and no part of
     * the author's point: the two issue the same points, and are one reading of the line.
     */
    @Test
    void aComparisonsRunOwedToMoreThingsIsTheSameReading() {
        Border rulesOnly = compared(List.of());
        Border andALine = compared(List.of(Parting.by(
                HeldSeams.of(space(), at(1000), Towards.BELOW), aComparison())));

        assertTrue(rulesOnly.demand(PointRole.IN).sameAs(andALine.demand(PointRole.IN)),
                "the run holds the same values either way");
        assertNotEquals(rulesOnly.answer(PointRole.IN).bases(),
                andALine.answer(PointRole.IN).bases(),
                "and a row inside it answers for more once the line is there");
        assertTrue(rulesOnly.sameReadingAs(andALine),
                "which is no part of the comparison's point, so the two are one reading");
        assertTheReadingIsItsPoints(rulesOnly, andALine);
    }

    /**
     * A bound's run is what the rules leave, whatever lines a body draws inside it.
     *
     * <p>Nothing outside a bound can be constructed, so what a row beside its line is asked for is a
     * question about what the rules leave the position, and a comparison inside that divides it
     * without moving it. Told about a line at five hundred, the bound's reading is the reading it
     * is without it.
     */
    @Test
    void aBoundIsTheSameReadingWhateverLinesABodyDrawsInsideIt() {
        Border bare = bound(List.of());
        Border besideALine = bound(List.of(Parting.by(
                HeldSeams.of(space(), at(500), Towards.BELOW), aComparison())));

        assertEquals(bare.answer(PointRole.IN), besideALine.answer(PointRole.IN));
        assertTrue(bare.sameReadingAs(besideALine));
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
        Border narrowed = bound(List.of(), AReadingOfAPosition.withAnUpperEndAt(
                Endpoint.inclusive(Count.of(1000)), aDeclaration()));
        Border bare = bound(List.of(), NarrowedBounds.NOTHING);

        assertNotEquals(bare, narrowed,
                "the two do differ, and this is what they differ in");
        assertTrue(bare.sameReadingAs(narrowed),
                "and neither the line nor what a row at any of its points has to do is any"
                        + " different, so it is one reading of one line");
    }

    /**
     * Two spellings of the place a line is at are one place, so the two readings are one.
     *
     * <p>A level keeps the representation its rule was written with. Asked of the records, the border's own place would have told two readings of one line
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

    /**
     * The order two things that stop a run were arrived at is no part of which reading this is.
     *
     * <p>A run stopping at a line and at the end the rules leave is owed to both of them, and which
     * of the two an arrangement walked to first is how it was walked. Compared in the order they
     * came, one reading of one line would stop being that the day the walk changed — which is the
     * kind of accident this comparison is here to keep out of the answer.
     */
    @Test
    void theOrderWhatStopsARunWasFoundInIsNoPartOfTheReading() {
        Border one = compared(List.of(Parting.by(
                HeldSeams.of(space(), at(1000), Towards.BELOW), aComparison())));
        Border other = reversed(one);

        assertNotEquals(one.answer(PointRole.IN).bases(), other.answer(PointRole.IN).bases(),
                "the two list what stops the run in opposite orders");
        assertTrue(one.sameReadingAs(other),
                "and are owed to the same things, so they are one reading of one line");
    }

    /**
     * A point no row is owed at, settled in another place, is another reading.
     *
     * <p>The position holds a hundred and nothing else, so the run above the bound is empty and no
     * row is owed in it — settled by where the values stop. The same answer settled by the end of
     * the order instead owes no row for the same reason and is another point no row is owed at, as
     * a run owed to two different things is two points a row is owed at. Compared by the demands
     * alone, the two were one reading, and the second of them was dropped where one reading's lines
     * are kept from holding one line twice.
     */
    @Test
    void aPointNoRowIsOwedAtSettledElsewhereIsAnotherReading() {
        Border settled = onlyAHundred(NarrowedBounds.NOTHING);
        Border elsewhere = settledBy(settled, new DomainPoint.InTheRegion(Towards.ABOVE),
                List.of(new RegionClaim(new FarEnd.AtTheOrderEnd(Towards.ABOVE),
                        PointContributions.none())));

        assertTrue(settled.answer(new DomainPoint.InTheRegion(Towards.ABOVE))
                        instanceof PointAnswer.NotOwed,
                () -> "nothing stands above a hundred: " + settled.answers());
        assertFalse(settled.sameReadingAs(elsewhere),
                "the two owe no row there for one reason, and were settled in two places");
        assertTheReadingIsItsPoints(settled, elsewhere);
    }

    /**
     * And who settled it there is no part of which reading this is, for a point no row is owed at
     * as for one a row is.
     */
    @Test
    void whoSettledAPointNoRowIsOwedAtIsNoPartOfTheReading() {
        Border bare = onlyAHundred(NarrowedBounds.NOTHING);
        Border narrowed = onlyAHundred(AReadingOfAPosition.withAnUpperEndAt(
                Endpoint.inclusive(Count.of(100)), aDeclaration()));

        assertNotEquals(bare, narrowed,
                "a declaration took the end in at one of them, and this is what they differ in");
        assertTrue(bare.sameReadingAs(narrowed),
                "and the run above stops in the one place at both, so it is one reading");
        assertTheReadingIsItsPoints(bare, narrowed);
    }

    /**
     * That two readings are one exactly where the points they issue are the same: the points a row
     * is owed at and the points no row is owed at, as the accounts read them.
     */
    private static void assertTheReadingIsItsPoints(Border one, Border other) {
        boolean samePoints = Set.copyOf(one.owes().stream().map(OwedPoint::point).toList())
                .equals(Set.copyOf(other.owes().stream().map(OwedPoint::point).toList()))
                && Set.copyOf(one.leavesOut().stream().map(LeftOutPoint::point).toList())
                .equals(Set.copyOf(other.leavesOut().stream().map(LeftOutPoint::point).toList()));
        assertEquals(samePoints, one.sameReadingAs(other),
                () -> "one reading is one set of points: " + one.leavesOut() + " / "
                        + other.leavesOut());
    }

    /** A bound at a hundred on a position that holds a hundred and nothing else. */
    private static Border onlyAHundred(NarrowedBounds narrowed) {
        return Border.at(aLineAt("w.a", 100), aBound(),
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(100)),
                        Endpoint.inclusive(Count.of(100))),
                List.of(), narrowed);
    }

    /** The same border with the point at {@code point} settled by {@code claims} instead. */
    private static Border settledBy(Border border, DomainPoint point, List<RegionClaim> claims) {
        Map<DomainPoint, PointAnswer> answers = new LinkedHashMap<>(border.answers());
        if (!(answers.get(point) instanceof PointAnswer.NotOwed was)) {
            throw new IllegalArgumentException("no row is owed at " + point + " to settle again: "
                    + answers);
        }
        answers.put(point, new PointAnswer.NotOwed(was.reason(), claims));
        return new Border(border.cut(), border.origin(), answers, border.leftNothing());
    }

    /** The same border with what stops each of its runs listed the other way round. */
    private static Border reversed(Border border) {
        java.util.Map<DomainPoint, PointAnswer> answers =
                new java.util.LinkedHashMap<>();
        for (DomainPoint role : border.answers().keySet()) {
            PointAnswer answer = border.answer(role);
            answers.put(role, answer instanceof PointAnswer.InRegion in && in.claims().size() > 1
                    ? new PointAnswer.InRegion(in.criterion(), reversed(in.claims()))
                    : answer);
        }
        return new Border(border.cut(), border.origin(), answers, border.leftNothing());
    }

    private static List<RegionClaim> reversed(List<RegionClaim> claims) {
        List<RegionClaim> out = new java.util.ArrayList<>(claims);
        java.util.Collections.reverse(out);
        return out;
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

    /**
     * A place another rule parts the quantity at that was not worked out leaves the run not worked
     * out, and not wider.
     *
     * <p>The runs of an arrangement lie between its places, so with one missing none of them is
     * known to be the run it looks like. Left out, the run would read to the next place that is
     * known and a row written in it would be owed to a line it may not be inside.
     */
    @Test
    void aPlaceThatWasNotWorkedOutLeavesTheRunNotWorkedOut() {
        UnheldNumber why = UnheldNumber.MORE_ROOM_COULD_ANSWER;

        Border border = Border.at(aLineAt("w.a", 100), aComparisonOrigin(),
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(100)),
                        Endpoint.inclusive(Count.of(1000))),
                ExactAnswer.unheld(why), NarrowedBounds.NOTHING);

        assertEquals(new PointAnswer.NotWorkedOut(why), border.answer(PointRole.IN),
                "the run beside the line is one of the runs that lie between the places");
        assertTrue(border.answer(PointRole.ON) instanceof PointAnswer.AtLine,
                "and the point at the line, which the order alone answers, is asked as it always is");
    }

    /** A bound at a hundred, leaving everything up to a thousand, told about {@code parted}. */
    private static Border bound(List<Parting> parted) {
        return bound(parted, NarrowedBounds.NOTHING);
    }

    /** The same, told what the value the position sits in leaves it and who holds each end. */
    private static Border bound(List<Parting> parted, NarrowedBounds narrowed) {
        return Border.at(aLineAt("w.a", 100), aBound(),
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(100)),
                        Endpoint.inclusive(Count.of(1000))),
                parted, narrowed);
    }

    /** A comparison at a hundred, kept above, over the same range, told about {@code parted}. */
    private static Border compared(List<Parting> parted) {
        return Border.at(aLineAt("w.a", 100), aComparisonOrigin(),
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(100)),
                        Endpoint.inclusive(Count.of(1000))),
                parted, NarrowedBounds.NOTHING);
    }

    /** The same bound, with its line written as {@code at}. */
    private static Border boundAt(Count at) {
        AxisId axis = new AxisId("weigh", "w.a");
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(TermPath.of(axis.term()));
        return Border.at(BoundaryTarget.at(
                        new BorderQuantity.OfACoordinate(axis.behavior(), term,
                                TermOrdersFixtures.itself(term, WHOLE)),
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
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(TermPath.of(axis.term()));
        return BoundaryTarget.at(
                new BorderQuantity.OfACoordinate(axis.behavior(), term,
                        TermOrdersFixtures.itself(term, WHOLE)),
                at(value));
    }

    /** The clause the bound is written in, which is only an identity here. */
    private static LineOrigin aBound() {
        return new LineOrigin.InvariantOrigin(
                new DeclaredLine.OfAStatement(new InvariantStatementId(
                        new PartId<>(new RuleRef.Invariant(new Clause.Ref(
                                new Clause.Id(TypeSymbols.declared(
                                        new TypeKey("example.weigh", "Amount")), 0),
                                Optional.of(new ClauseName("cap")))), 0),
                        0)),
                EndSide.LOWER, true);
    }

    /** A body's comparison keeping the values from a hundred up, which is what the readings whose
     *  runs other lines stop are read off. */
    private static LineOrigin aComparisonOrigin() {
        return aComparisonKeeping(1, Towards.ABOVE);
    }

    /** A reading of another line of the body, for a place to be parted by something other than the
     *  line read. */
    private static LineOrigin aComparison() {
        return aComparisonKeeping(2, Towards.BELOW);
    }

    /** The comparison written {@code ordinal}th in the body, keeping the values {@code kept} of
     *  its number. */
    private static LineOrigin aComparisonKeeping(int ordinal, Towards kept) {
        SourceConstructOrigin wrote = new SourceConstructOrigin(
                new WrittenOwner.Body("example.weigh", "weigh"), ordinal, 0,
                SourceConstruct.BINARY);
        return new LineOrigin.ComparisonOrigin(
                new LineOrigin.ComparisonOrigin.Read(
                        new RuleRef.Comparison("weigh", wrote),
                        new ModelOccurrence(wrote, ExpansionLineage.ORIGINAL),
                        new RuleReportAnchor.ByTheModuleThatWroteIt(),
                        List.of(Numberings.comparison(ordinal, 0)), ElementsMetOn.EVERY,
                        LineOrigin.NOTHING_ON_THE_WAY, Optional.empty()),
                Optional.empty(),
                new LineFacts(new ComparisonClaim.Cut(kept, true)),
                new AuthoredPointMapping.Proven(WrittenLine.THE_COMPARISON,
                        new ComparisonClaim.Cut(kept, true),
                        Derivation.AComparisonRead.Facing.NOTHING_WRITTEN, true));
    }
}
