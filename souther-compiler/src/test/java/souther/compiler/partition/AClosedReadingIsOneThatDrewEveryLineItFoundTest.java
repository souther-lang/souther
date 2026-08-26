package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A reading that lost a line is not a reading that ran out.
 *
 * <p>{@code Closed} is what takes a behavior out of the verdict, and it used to follow from three
 * absences: nothing was set aside, nothing went unanswered, no position went unreached. A rule
 * dropped before it could be set aside leaves all three of those exactly as they were, so a measure
 * built from them reported a model read in full on the strength of a reading that had lost part of
 * it — a {@code Decimal} bounded by two clauses came back as a behavior whose rules draw no line
 * anywhere, and the module was called adequate (issue #1079).
 *
 * <p>So what the reading produced is held against what it found. One rule that drew a cut is one
 * line, and a reading holding fewer lines than cuts has lost one however it went — a null nobody
 * tested for, a {@code continue}, a filter. The count is the only thing that catches all three,
 * since each of them leaves a shorter list and nothing else.
 */
class AClosedReadingIsOneThatDrewEveryLineItFoundTest {

    private static final AxisId AT = new AxisId("take", "h.a");

    /** A reading of one bound that drew its line, which is what a closed one is. */
    @Test
    void aReadingThatDrewItsLineMayBeClosed() {
        MeasureClosure.Both closed =
                MeasureClosure.of(List.of(anAxisWithOneCut()), List.of(), List.of(),
                        Map.of(AT, List.of(aBorder())));

        assertInstanceOf(MeasureClosure.OfTheBorder.Closed.class, closed.border(),
                "every question this measure answers was answered");
        assertInstanceOf(MeasureClosure.OfThePartition.Closed.class, closed.partition());
    }

    /**
     * And one that found a cut and came back without its line is refused rather than closed.
     *
     * <p>Refused and not reported as a gap. What was lost is not known here — a gap says which rule
     * or which position a measure is short of, and a reading that dropped one has nothing to name.
     * This is this compiler having lost something, which is the one thing a document may not be
     * written from.
     */
    @Test
    void aReadingThatLostItsLineIsRefused() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> MeasureClosure.of(List.of(anAxisWithOneCut()), List.of(), List.of(),
                        Map.of()));

        assertEquals("a reading of `h.a` that found 1 line and drew 0: what a measure is short of"
                + " cannot be counted from what a reading lost", refused.getMessage());
    }

    /**
     * Counted per rule that drew the cut and not per cut.
     *
     * <p>An invariant and a {@code guard} naming one value are two rules and one place, and each of
     * them is owed a row: reaching the line through one says nothing about the other. Counted by
     * cuts, a reading that drew one of the two and lost the other came back whole.
     */
    @Test
    void aCutTwoRulesDrewIsTwoLines() {
        Cut both = Cut.at(Carrier.WHOLE, Count.of(5), bound("cap")).and(bound("floor"));
        Axis axis = new Axis(AT, new NumericTerm.ValueOf(TermPath.of("h").then("a")), Type.INT,
                List.of(), List.of(both));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> MeasureClosure.of(List.of(axis), List.of(), List.of(),
                        Map.of(AT, List.of(aBorder()))));

        assertEquals("a reading of `h.a` that found 2 lines and drew 1: what a measure is short of"
                + " cannot be counted from what a reading lost", refused.getMessage());
    }

    /** One position bounded at 5, which is one cut drawn by one rule. */
    private static Axis anAxisWithOneCut() {
        return new Axis(AT, new NumericTerm.ValueOf(TermPath.of("h").then("a")), Type.INT,
                List.of(), List.of(Cut.at(Carrier.WHOLE, Count.of(5), bound("cap"))));
    }

    private static Border aBorder() {
        return Border.at(
                BoundaryTarget.at(
                        new BorderQuantity.OfACoordinate(AT,
                                new NumericTerm.ValueOf(TermPath.of("h").then("a")),
                                souther.compiler.inputs.TermOrders.itself(Carrier.WHOLE)),
                        new Level.OnACarrier(Carrier.WHOLE, Count.of(5))),
                bound("cap"),
                new souther.compiler.numeric.NumericDomain.Bounds(
                        souther.compiler.numeric.Endpoint.inclusive(Count.of(5)), null));
    }

    private static OriginRef bound(String clause) {
        return new OriginRef.InvariantOrigin(new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("example.rate", "Amount")), 0),
                java.util.Optional.of(new ClauseName(clause)))), 0, true);
    }
}
