package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AReadingOfAPosition;
import souther.compiler.check.Carrier;
import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.NarrowedBounds;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A declaration is named as taking a run's end in only where that is the end it was read at.
 *
 * <p>Two readings reach a border and they are readings of different rules. Which declarations hold
 * an end comes from the value the position sits in, and is worked out against the number that
 * reading arrived at; where the run actually stops is what every rule reaching the behavior leaves
 * the term, which that reading knew nothing of. So the two can leave the position in different
 * places, and a name carried across without asking is a name written against a number no clause of
 * that declaration moved — an author sent to a line that admits every value the run stops short of.
 *
 * <p>Assembled here rather than read from a model. What decides this is which end the reading was
 * asked about, and a model reaching the case where the two ends differ is a separate question about
 * what the declarations can be made to say — one this does not answer and does not need to.
 */
class ANarrowingIsToldOnlyAboutTheEndItWasReadAtTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    /** Where the rules leave the term: a minimum at a hundred, running to a thousand. */
    private static final NumericDomain.Bounds RUNS_TO_A_THOUSAND = new NumericDomain.Bounds(
            Endpoint.inclusive(Count.of(100)), Endpoint.inclusive(Count.of(1000)));

    /** The reading that answers about the end the run stops at is the one that is heard. */
    @Test
    void aReadingAboutTheEndTheRunStopsAtIsNamedThere() {
        assertEquals(List.of(HELD),
                narrowersInsideTheRun(AReadingOfAPosition.withAnUpperEndAt(
                        Endpoint.inclusive(Count.of(1000)), HELD), RUNS_TO_A_THOUSAND),
                "the reading stops the position where the run stops, so what holds that end holds"
                        + " this one");
    }

    /**
     * And a reading about another end is not.
     *
     * <p>The declaration did move an end; it moved one this run never reaches. Named here, a report
     * would send its author to a clause that leaves every value between the two ends in.
     */
    @Test
    void aReadingAboutAnotherEndIsNotNamedThere() {
        assertEquals(List.of(),
                narrowersInsideTheRun(AReadingOfAPosition.withAnUpperEndAt(
                        Endpoint.inclusive(Count.of(999)), HELD), RUNS_TO_A_THOUSAND),
                "999 is not where the run stops, so what holds it holds nothing here");
    }

    /**
     * Nor is a reading of the end at the other side of the run.
     *
     * <p>The low end of what the rules leave is where this run starts and not where it stops, and
     * the reading answering about it is answering about the other question. Which side each of the
     * two is about travels with it from the reading to here, and the numbers alone do not say: a
     * quantity the rules leave one value stops at that value both ways, and there the two ends are
     * one number ({@code ARangeStoppingAtOneValueStillHasTwoEndsTest}).
     */
    @Test
    void aReadingOfTheEndTheRunStartsAtIsNotNamedWhereItStops() {
        assertEquals(List.of(),
                narrowersInsideTheRun(AReadingOfAPosition.withALowerEndAt(
                        Endpoint.inclusive(Count.of(100)), HELD), RUNS_TO_A_THOUSAND),
                "a hundred is where the run starts, and this end is not the one it stops at");
    }

    /**
     * What a row inside the run is told the run's far end is owed to.
     *
     * <p>The point inside the partition a minimum bounds: its line is the minimum's own, and the far
     * side of the run beside it is where the rules leave the term.
     */
    private static List<TypeSymbol.AtModule> narrowersInsideTheRun(NarrowedBounds narrowed,
                                                                   NumericDomain.Bounds runs) {
        PointAnswer answer = Border.at(aLineAt(100), aMinimum(), runs, List.of(), narrowed)
                .answer(PointRole.IN);
        return ((PointAnswer.InRegion) answer).claims().stream()
                .flatMap(claim -> claim.contributions().narrowers().stream())
                .toList();
    }

    /** A declaration that could have moved where the position stops. */
    private static final TypeSymbol.AtModule HELD =
            TypeSymbols.declared(new TypeKey("example.weigh", "Held"));

    /** The clause the bound is written in, which is only an identity here. */
    private static OriginRef aMinimum() {
        return new OriginRef.InvariantOrigin(new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("example.weigh", "Amount")), 0),
                Optional.of(new ClauseName("floor")))), 0, EndSide.LOWER, true);
    }

    private static BoundaryTarget aLineAt(int value) {
        AxisId axis = new AxisId("weigh", "w.a");
        return BoundaryTarget.at(
                new BorderQuantity.OfACoordinate(axis,
                        new NumericTerm.ValueOf(TermPath.of(axis.term())),
                        TermOrders.itself(WHOLE)),
                new Level.OnACarrier(WHOLE, Count.of(value)));
    }
}
