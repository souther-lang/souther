package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A region is narrowed by exactly the conditions the account it is built from says were taken in.
 *
 * <p>The other half of what {@link WayToTheBorder} promises. That the cuts a walk took in hold of
 * every row that arrives is about the walk and is held elsewhere; this is about what the account
 * means — that the region it makes is the one it describes, in the order it describes, and that a
 * condition written down as declined reaches the domains not at all.
 *
 * <p>Measured against a region that records what it is told rather than against what the numbers
 * come to. What a domain does with a cut is the domain's business and two different cuts can leave
 * one region unchanged, so an answer read off the values would hold just as well if half the
 * account were fiction.
 */
class TheCutsAWalkTookInAreTheOnesARegionIsNarrowedByTest {

    /**
     * A region that remembers what it was told and refuses everything else.
     *
     * <p>Refuses rather than answers. What is under test is which conditions reach the domains, and
     * a stand-in that answered questions about values would be inventing a region — the day
     * narrowing starts asking one of them, this says so instead of being read as though the answer
     * had come from somewhere.
     */
    private static final class Recording implements SearchRegion {

        private final List<TakenConstraint> told = new ArrayList<>();

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            told.add(new TakenConstraint.Affine(form, rel));
            return new Assumption.Taken(this);
        }

        @Override
        public SearchRegion assuming(NumericTerm.FromOnePosition term,
                                     souther.compiler.numeric.Place at, Rel rel) {
            told.add(new TakenConstraint.Ordered(term, at, rel));
            return this;
        }

        @Override
        public SearchRegion apartFrom(NumericTerm.FromOnePosition term,
                                      souther.compiler.numeric.Place at) {
            told.add(new TakenConstraint.AwayFrom(term, at));
            return this;
        }

        /** Read back off what this was told, so the two answers about a hole cannot disagree. */
        @Override
        public PlacesApart apartAt(NumericTerm.FromOnePosition term) {
            return PlacesApart.of(told.stream()
                    .filter(each -> each instanceof TakenConstraint.AwayFrom away
                            && away.term().equals(term))
                    .map(each -> ((TakenConstraint.AwayFrom) each).at())
                    .toList());
        }

        @Override
        public SearchRegion given(Map<NumericTerm, souther.compiler.numeric.Place> fixed) {
            throw new UnsupportedOperationException("narrowing fixes no position");
        }

        @Override
        public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
            throw new UnsupportedOperationException("narrowing reads no value");
        }

        @Override
        public Optional<EmptyInput> emptiness() {
            throw new UnsupportedOperationException("narrowing asks nothing about what is left");
        }
    }

    private static TakenConstraint.Affine cut(String position, Rel rel) {
        return new TakenConstraint.Affine(
                LinearForm.atom(new NumericTerm.ValueOf(TermPath.of(position))), rel);
    }

    /** A bound on one position's own order, which is the other vocabulary a condition lands in. */
    private static TakenConstraint.Ordered bound(String position, String at, Rel rel) {
        return new TakenConstraint.Ordered(new NumericTerm.ValueOf(TermPath.of(position)),
                souther.compiler.numeric.Text.of(at), rel);
    }

    /** A condition this reading met, named by nothing but which of them it is. */
    private static ConditionOccurrence met(int which) {
        return new ConditionOccurrence("b", which);
    }

    /** Where a report about it would point, which nothing here reads. */
    private static ConditionReportAnchor somewhere(int which) {
        return new ConditionReportAnchor.WhereTheReadingMetIt("m", met(which));
    }

    /** Every cut the account carries, in the order it carries them, and nothing else. */
    @Test
    void theRegionIsToldTheCutsTheAccountCarries() {
        TakenConstraint first = cut("x", Rel.GE);
        TakenConstraint second = cut("y", Rel.LT);
        Recording region = new Recording();

        SearchRegion narrowed = new WayToTheBorder(List.of(
                new OnTheWay.TakenIn(somewhere(1), first),
                new OnTheWay.TakenIn(somewhere(2), second))).narrowing(region);

        assertEquals(List.of(first, second), region.told,
                "the region is narrowed by the cuts the account says it was narrowed by");
        assertSame(region, narrowed, "and by nothing after them");
    }

    /**
     * A condition nothing could take in narrows nothing.
     *
     * <p>Which is the direction that keeps a region wide enough to hold the rows that arrive. A
     * decline that reached the domains would be this compiler narrowing on a condition it could not
     * read, and the region would then be narrower than the rows it is searched for.
     */
    @Test
    void aDeclinedConditionIsNotToldToTheRegion() {
        TakenConstraint only = cut("x", Rel.GE);
        Recording region = new Recording();

        WayToTheBorder way = new WayToTheBorder(List.of(
                new OnTheWay.Declined(met(1), somewhere(1), new OnTheWay.Why.NoWordsForTheShape()),
                new OnTheWay.TakenIn(somewhere(2), only),
                new OnTheWay.Declined(met(3), somewhere(3), new OnTheWay.Why.OneOfTwoThings())));
        way.narrowing(region);

        assertEquals(List.of(only), region.told, "a decline is a record and not a cut");
        assertEquals(2, way.declined().size(), "and it is still on the account");
        assertEquals(3, way.onTheWay().size(),
                "which holds every condition on the way, in the order the walk met them");
    }

    /**
     * A bound on a position's own order reaches the region as that, beside the arithmetic's.
     *
     * <p>Both vocabularies out of one list and in the order the walk met them. Carried as one shape,
     * a bound on a carrier that counts nothing would have to be spelled as a form of things that do
     * not add — and what the region was told would be a rule nobody wrote.
     */
    @Test
    void aBoundOnAnOrderIsToldToTheRegionAsOne() {
        TakenConstraint arithmetic = cut("n", Rel.GE);
        TakenConstraint ordered = bound("s", "t", Rel.LT);
        Recording region = new Recording();

        new WayToTheBorder(List.of(
                new OnTheWay.TakenIn(somewhere(1), arithmetic),
                new OnTheWay.TakenIn(somewhere(2), ordered))).narrowing(region);

        assertEquals(List.of(arithmetic, ordered), region.told,
                "a condition in either vocabulary narrows the region it landed in");
    }

    /** A border with nothing on the way to it is the region it started as, and says so. */
    @Test
    void aRegionWithNothingOnTheWayIsToldNothing() {
        Recording region = new Recording();

        SearchRegion untouched = WayToTheBorder.UNTOUCHED.narrowing(region);

        assertEquals(List.of(), region.told, "nothing stood on the way, so nothing was taken in");
        assertEquals(List.of(), WayToTheBorder.UNTOUCHED.onTheWay(),
                "and the account says that rather than being absent");
        assertSame(region, untouched);
    }

    /** A cut with a constant in it is handed over as written, since a domain is told `f rel 0`. */
    @Test
    void aCutIsHandedOverAsTheAccountHoldsIt() {
        TakenConstraint shifted = new TakenConstraint.Affine(
                LinearForm.<NumericTerm>atom(new NumericTerm.ValueOf(TermPath.of("x")))
                        .minus(LinearForm.constant(ExactRatio.of(17))), Rel.LE);
        Recording region = new Recording();

        new WayToTheBorder(List.of(new OnTheWay.TakenIn(somewhere(1), shifted))).narrowing(region);

        assertEquals(List.of(shifted), region.told);
    }
}
