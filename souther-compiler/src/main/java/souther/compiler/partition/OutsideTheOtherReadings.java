package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.function.UnaryOperator;

/**
 * The region a row at a class of one reading of a comparison has to be in, beside lying in the
 * class: outside the case every other reading of that comparison decides in.
 *
 * <p>A row in the case of another reading is a row of that reading ({@link
 * StandingAtAPoint.AtALine#forAClass}), so the region a row at the class can be in is the class
 * with each of those cases denied. Where that leaves the class no value, no row is at it, and the
 * realizer proves it as it proves every other region empty. Where the cases of several readings
 * together cover the class, none of them need do so alone.
 *
 * <p>Only what a region can carry is taken in. A case or a part of one that is not a conjunction of
 * comparisons over the input's numbers, or that the region refuses, is left out, which leaves the
 * region wider than the rows that are at the class and never narrower: the absence of a proof is
 * not a proof that none is there.
 */
public final class OutsideTheOtherReadings {

    private OutsideTheOtherReadings() {
    }

    /**
     * {@code region} with each of {@code cases} denied, as far as it can carry them.
     *
     * @param cases where each other reading of the comparison decides
     */
    public static UnaryOperator<SearchRegion> of(List<Proposition> cases) {
        return region -> {
            SearchRegion within = region;
            for (Proposition decides : cases) {
                within = deniedIn(decides.denied(), within);
            }
            return within;
        };
    }

    /** {@code region} with {@code stated} taken in, where it is a conjunction of comparisons. */
    private static SearchRegion deniedIn(Proposition stated, SearchRegion region) {
        return switch (stated) {
            case Proposition.All all -> {
                SearchRegion within = region;
                for (Proposition part : all.parts()) {
                    within = deniedIn(part, within);
                }
                yield within;
            }
            case Proposition.Compared compared -> takenIn(compared, region);
            case Proposition.Always _, Proposition.Any _, Proposition.Truth _,
                 Proposition.InCases _, Proposition.Present _, Proposition.InTheStrings _,
                 Proposition.SameValue _, Proposition.StringInside _, Proposition.LastToHold _,
                 Proposition.Some _, Proposition.Carried _, Proposition.SomeReachable _,
                 Proposition.Unread _, Proposition.OnAnApplication _, Proposition.SoManyHold _,
                 Proposition.WhereItAnswers _, Proposition.OfTheWays _ -> region;
        };
    }

    private static SearchRegion takenIn(Proposition.Compared compared, SearchRegion region) {
        Rel proposition = compared.relation().proposition();
        Rel met = compared.holds() ? proposition : proposition.denied();
        return switch (compared.relation()) {
            case Relation.Affine(LinearForm<Quantity> form, Rel _) -> {
                LinearForm<NumericTerm> against = WhatTheDeclarationsLeave.ofTheInput(form);
                if (against == null) {
                    yield region;
                }
                yield switch (region.assuming(against, met)) {
                    case SearchRegion.Assumption.Taken(SearchRegion taken) -> taken;
                    case SearchRegion.Assumption.Refused _ -> region;
                };
            }
            case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm.FromOnePosition term),
                                  var at, Rel _) -> (TakenConstraint.Ordered.isABound(met)
                    ? new TakenConstraint.Ordered(term, at, met)
                    : new TakenConstraint.AwayFrom(term, at)).narrowing(region);
            case Relation.Ordered _ -> region;
        };
    }
}
