package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import java.util.ArrayList;
import java.util.List;

/**
 * The numbers a search for a value at one target is about.
 *
 * <p><b>The subject of whatever the search concludes.</b> A walk that built nothing says something
 * about these numbers and about no others, so what is written here decides what a reader of the
 * report is licensed to conclude. A value a caller picked to try first is not this — that is a
 * candidate, and it travels beside this rather than in it. Put here instead, a walk that ran out of
 * one candidate would have run out of every number there is, and a class holding values nobody
 * built at would be a class the model leaves empty.
 *
 * <p><b>Two halves, and the second is why the first is not the whole answer.</b> {@code values} is
 * what is exactly known of this target on its own; {@code onlyTogether} is the rules that bear on
 * it and do not say anything about it on its own — a condition over a form of several positions
 * bounds the form, and which numbers it leaves this one turns on what the others took. Both are
 * kept because dropping either loses something a caller has: without the first, a target under a
 * joint condition is searched as though nothing at all were known of it; without the second, a
 * walk of the first would think it had seen everything.
 *
 * <p>One record rather than an arm per case, because every pair of the two is a question somebody
 * asks: a form's position under no rule of its own, a position under its own rule and a form's, and
 * either alone. Written as two arms, {@link #meet} would have to say which arm a crossing lands in
 * and the rule for it is the one below — so the arms would be a second spelling of
 * {@code onlyTogether.isEmpty()} that a reader could ask instead of asking this.
 *
 * @param values       every number the rules leave this target on its own, which is
 *                     {@link LevelRegion#EVERYTHING} where they leave it everything
 * @param onlyTogether the conditions bearing on it that are about a form of several positions and
 *                     not about this one. Empty is the ordinary case and is what makes a walk of
 *                     {@code values} a walk of the whole question
 */
record NumbersAskedFor(LevelRegion values, List<TakenConstraint.Affine> onlyTogether) {

    NumbersAskedFor {
        onlyTogether = List.copyOf(onlyTogether);
    }

    /** Every number the order has, under no condition at all. */
    static final NumbersAskedFor ANYTHING =
            new NumbersAskedFor(LevelRegion.EVERYTHING, List.of());

    /** The numbers a rule leaves this target, said of it alone. */
    static NumbersAskedFor of(LevelRegion values) {
        return new NumbersAskedFor(values, List.of());
    }

    /**
     * A condition over a form of several positions, which leaves each of them everything on its
     * own.
     *
     * <p>Not nothing. What the condition says is true and is carried; what it does not say is which
     * numbers this position may take, and the two are different facts. Recorded as an absence of
     * information, a caller would search this position as widely as it does and also claim to have
     * finished.
     */
    static NumbersAskedFor onlyTogether(TakenConstraint.Affine constraint) {
        return new NumbersAskedFor(LevelRegion.EVERYTHING, List.of(constraint));
    }

    /**
     * What the rules leave {@code term}, said of that term alone.
     *
     * <p>Taken from the region as it was handed over, which is the declarations narrowed by every
     * cut the way took in. Read after a value has been chosen somewhere, this would be what the
     * rules leave given that choice — an answer about one branch of the search written down as the
     * question the search is settling.
     *
     * <p><b>And what a pair of ends cannot say is asked of the cuts themselves.</b> A region
     * answers about a term as a run, so a rule holding the term away from one value inside that run
     * comes back as the run entire: the hole is in the region and not in the projection of it. So
     * the holes are put back here, and a condition over a form of several positions — which leaves
     * this term every number until the others are settled — is carried as what it is.
     *
     * @param cuts every cut the way took in, of which the ones naming {@code term} are read
     * @param on   the order {@code term}'s values are counted on
     */
    static NumbersAskedFor askedOf(NumericTerm.FromOnePosition term,
                                   SearchRegion within, Carrier on,
                                   List<OnTheWay.TakenIn> cuts) {
        NumbersAskedFor asked = switch (within.projectionOf(term)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    of(between(held, on));
            // The rules leave the term nowhere, which is the whole of what is asked of it.
            case NumericDomain.FormProjection.NothingIsLeft _ -> of(new LevelRegion(List.of()));
            case null -> ANYTHING;
        };
        for (OnTheWay.TakenIn cut : cuts) {
            if (!cut.taken().terms().contains(term)) {
                continue;
            }
            asked = asked.meet(switch (cut.taken()) {
                case TakenConstraint.AwayFrom away ->
                        of(LevelRegion.EVERYTHING.without(new Level.OnACarrier(on, away.at())));
                // A form of one term says where that term runs, and the region was narrowed by it
                // where it was taken in. Over several, what it leaves each of them is whatever the
                // others took.
                case TakenConstraint.Affine affine when affine.terms().size() > 1 ->
                        onlyTogether(affine);
                case TakenConstraint.Affine _, TakenConstraint.Ordered _ -> ANYTHING;
            });
        }
        return asked;
    }

    /** The run between a pair of ends, open where an end is not written. */
    private static LevelRegion between(NumericDomain.Bounds held, Carrier on) {
        if (held == null) {
            return LevelRegion.EVERYTHING;
        }
        return LevelRegion.of(new LevelInterval(end(held.min(), on), end(held.max(), on)));
    }

    private static Bound end(Endpoint at, Carrier on) {
        return at == null ? null : Bound.at(new Level.OnACarrier(on, at.at()), at.inclusive());
    }

    /**
     * Both questions at once, which is what a target under two rules is asked.
     *
     * <p>Each half crossed with its own: the values with the values, and the conditions gathered.
     * A joint condition does not take away what is exactly known of the target, so a crossing that
     * has one on either side keeps every value both sides left — which is the difference between
     * searching a position the rules bound and searching the whole of its order.
     */
    NumbersAskedFor meet(NumbersAskedFor other) {
        List<TakenConstraint.Affine> both = new ArrayList<>(onlyTogether);
        for (TakenConstraint.Affine each : other.onlyTogether) {
            if (!both.contains(each)) {
                both.add(each);
            }
        }
        return new NumbersAskedFor(values.meet(other.values), both);
    }

    /**
     * Whether walking {@code values} to the end is walking the whole of what was asked.
     *
     * <p>The one thing a word about the model rests on. A walk that reached no value may say the
     * rules leave none only where this holds; where it does not, the numbers this target may take
     * are the ones some other position's value decides, and none of them was looked at.
     */
    boolean isWalkedWhole() {
        return onlyTogether.isEmpty();
    }

    /**
     * Whether the rules leave this target one number, which one candidate is the whole of.
     *
     * <p>Asked of the question and not of the candidate handed beside it. A search asked for one
     * number that tries that number has tried every number there is of it; a search asked for a
     * class that tries one number out of it has tried one.
     */
    boolean isOneNumber() {
        return isWalkedWhole() && values.parts().size() == 1 && values.parts().getFirst().onePlace();
    }
}
