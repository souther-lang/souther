package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AReadingOfAPosition;
import souther.compiler.check.Carrier;
import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.MatchedEndAttribution;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A clause of a type does not part the values of the position it is about.
 *
 * <p>Nothing outside a bound can be constructed, so a bound has no far side to order against: it is
 * where what it leaves stops rather than a place its values divide. A clause that names one value
 * puts every other value in one class, which is not a run of the order either.
 *
 * <p>Which settles who can be named as stopping a run beside somebody else's line. Only a rule
 * written in a body parts the values, so a run stopping at a line is stopping at a body's rule, and
 * a point owed for such a run exists in that body and nowhere else. A declaration never turns up as
 * the far side of another declaration's line — where it does stop such a run, it stops it by taking
 * the position in, which is an end the rules leave and not a line ({@link FarEnd.AtTheDomain}).
 *
 * <p>Written down because the accounting rests on it. Were a clause to part the values, a run beside
 * an imported line could be owed to a foreign declaration's line, and which module answers for it
 * would be a question this compiler has never been asked.
 */
class AClauseOfATypeDoesNotPartItsValuesTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    /** A bound is where what it leaves stops, and stops nothing else. */
    @Test
    void aBoundPartsNothing() {
        assertEquals(List.of(), Border.partedBy(aLineAt(100), aBound()),
                "nothing is outside a bound, so there is no run on the far side to be beside");
    }

    /** And a bound another declaration took in is still a bound. */
    @Test
    void aBoundADeclarationTookInPartsNothingEither() {
        Endpoint at = Endpoint.inclusive(Count.of(100));
        assertEquals(List.of(), Border.partedBy(aLineAt(100),
                        OriginRef.NarrowedOrigin.of(aBound(), at, aDeclarationHolding(at))),
                "taking an end in moves where the position stops, which is not dividing it");
    }

    /**
     * A reading answering that one declaration holds {@code at} on the side {@link #aBound()}
     * placed.
     *
     * <p>The side is the bound's, because a bound is answered for by the end it placed. Written as
     * the other one, this fixture said a minimum had been taken in by whatever holds a maximum —
     * which is the pairing the origin refuses, and which is why it refuses it here rather than
     * downstream where the two are one number.
     */
    private static MatchedEndAttribution aDeclarationHolding(Endpoint at) {
        return AReadingOfAPosition
                .withALowerEndAt(at, TypeSymbols.declared(new TypeKey("example.weigh", "Held")))
                .matching(EndSide.LOWER, at).orElseThrow();
    }

    /** While a comparison in a body does part them, which is why a run can stop at a line at all. */
    @Test
    void aComparisonInABodyPartsThem() {
        assertNotNull(Border.partedBy(aLineAt(100), aComparison()),
                "a body's comparison orders the values around its line, so there is a run either"
                        + " side of it");
    }

    private static BoundaryTarget aLineAt(int value) {
        AxisId axis = new AxisId("weigh", "w.a");
        return BoundaryTarget.at(
                new BorderQuantity.OfACoordinate(axis,
                        new NumericTerm.ValueOf(TermPath.of(axis.term())),
                        TermOrders.itself(WHOLE)),
                new Level.OnACarrier(WHOLE, Count.of(value)));
    }

    private static OriginRef.InvariantOrigin aBound() {
        return new OriginRef.InvariantOrigin(new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("example.weigh", "Amount")), 0),
                Optional.of(new ClauseName("cap")))), 0, EndSide.LOWER, true);
    }

    private static OriginRef aComparison() {
        return new OriginRef.ComparisonOrigin(new RuleRef.Comparison("weigh",
                new souther.compiler.types.CoverageOrigin("example.weigh", 2, 0,
                        souther.compiler.types.CoverageConstruct.BINARY)),
                new OriginRef.ComparisonOrigin.Read(
                        new souther.compiler.coverage.ComparisonOccurrence(0),
                        new souther.compiler.check.RuleCitation.WrittenAt(
                                souther.compiler.diag.Citation.of(
                                        new souther.compiler.diag.SourcePos(3, 5)))),
                new LineFacts(new souther.compiler.check.ComparisonClaim.Cut(true, true)));
    }
}
