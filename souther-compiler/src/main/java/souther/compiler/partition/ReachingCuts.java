package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Symbols;
import souther.compiler.coverage.ComparisonOccurrence;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.Citation;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a row has already had to satisfy by the time it arrives at one comparison.
 *
 * <p>The region a border a guard owes is searched in. A guard states a threshold and narrows no
 * declaration, so what the positions are declared to hold is the same everywhere in a body while
 * what actually arrives at a comparison deep in one is not — and a row for a border down there,
 * looked for over the declared domains, is looked for outside the region as readily as inside it.
 *
 * <p><b>Collected where the condition is assumed, and never worked out afterwards from where a
 * comparison sits.</b> A reading that walked back up the tree would be a second account of what was
 * assumed, free to name a condition nothing here could take in — and a region narrowed on a
 * condition nothing established is narrower than the rows that arrive, which is the one direction
 * that takes a coverage item away. So what is here is what the walk itself put in.
 *
 * <p><b>Including what it could not put in.</b> A condition the arithmetic has no word for narrows
 * nothing, and it is written down all the same: what a region is is one question and how it came to
 * be that region is another, and only the second can tell a search that ran over what the
 * declarations leave because nothing stood in the way from one that ran over the same box because a
 * guard above could not be read. Held as {@link OnTheWay}, so the two are one sequence in the order
 * the walk met them rather than a list and a silence.
 *
 * <p><b>Its own value and not its arm.</b> Under {@code A && B} the {@code then} arm is reached with
 * both holding, and the {@code else} arm with neither settled — a row can be in it for failing
 * either. Under {@code A || B} it is the other way round. Which of the two a comparison is in is
 * {@link GuardThresholds}'s reading of the condition, and taking an arm for a conjunct is how a
 * region would come to exclude rows that reach the guard.
 *
 * <p>Nothing here says a row that satisfies all of this arrives. A condition of a shape the
 * arithmetic cannot read is on the list without narrowing anything, so what a region built from
 * this describes is wider than what arrives — which is what {@link SearchRegion} promises and what
 * a proof of unreachability rests on. Being on the list is what lets a report say so; it is not
 * what the region is built from.
 */
public record ReachingCuts(Map<ComparisonOccurrence, List<OnTheWay>> byComparison) {

    public static final ReachingCuts NONE = new ReachingCuts(Map.of());

    public ReachingCuts {
        byComparison = Map.copyOf(byComparison);
    }

    /** One thing a row had to satisfy to get here: {@code form rel 0} over this input's terms. */
    public record Cut(LinearForm<NumericTerm> form, Rel rel) {}

    /**
     * Where a row for a border at {@code site} is looked for: {@code region} narrowed by what the
     * walk to it took in, beside the whole account of that walk.
     *
     * <p>{@code region} itself where nothing was collected there — and the answer says so, rather
     * than leaving a reader to tell a comparison at the top of a body from one this could read
     * nothing on the way to. Both leave a region as wide as the declarations and both are sound;
     * only one of them is a limit of this compiler, and an author who is told nothing has no way to
     * find out which they are looking at.
     */
    public RegionForARow narrowing(SearchRegion region, ComparisonOccurrence site) {
        return RegionForARow.narrowed(region, byComparison.getOrDefault(site, List.of()));
    }

    /**
     * What {@code node} coming out {@code holding} says about this input, and where it says
     * nothing, that.
     *
     * <p>Never empty. Every shape has an answer — a cut where one could be made and a decline
     * where none could — because an empty answer is what made a comparison reached under nothing
     * and one reached past something unreadable into the same reading.
     *
     * <p>One rule for two questions, because they are one question. What reaching the right operand
     * of a condition establishes and what reaching an arm of the fork establishes are both "this
     * subtree came out this way, so what follows" — written apart, the two agreed by having been
     * derived alike, and the day one of them learned to read a new shape of condition would be the
     * day they stopped agreeing.
     *
     * <p>A conjunction coming out true is both its operands true, and a disjunction coming out false
     * is both false. The other two ways round say a disjunction of things, which is not a list of
     * cuts and is not approximated into one: {@code A && B} being false says one of them failed and
     * names neither, and narrowing on either would exclude rows that arrive. So those two are
     * declined whole, at the condition rather than at an operand — neither operand is what could
     * not be carried.
     */
    static List<OnTheWay> stating(Condition node, boolean holding, Symbols symbols) {
        return switch (node) {
            // A conjunction coming out true is both its operands true, and a disjunction coming out
            // false is both false. The other two ways round say a disjunction of things, which is
            // not a list of cuts and is not approximated into one: `A && B` being false says one of
            // them failed and names neither, and narrowing on either would exclude rows that arrive.
            // So the whole node is declined, at the whole node's place.
            case Condition.Both both -> holding
                    ? and(stating(both.left(), true, symbols), stating(both.right(), true, symbols))
                    : List.of(new OnTheWay.Declined(Citation.of(both.at().pos()),
                            OnTheWay.Why.NON_CONJUNCTIVE_OUTCOME));
            case Condition.Either either -> holding
                    ? List.of(new OnTheWay.Declined(Citation.of(either.at().pos()),
                            OnTheWay.Why.NON_CONJUNCTIVE_OUTCOME))
                    : and(stating(either.left(), false, symbols),
                            stating(either.right(), false, symbols));
            case Condition.Compares one -> List.of(of(one, holding, symbols));
            case Condition.NotRead not -> List.of(new OnTheWay.Declined(Citation.of(not.at().pos()),
                    OnTheWay.Why.CONDITION_NOT_READ));
        };
    }

    /**
     * What {@code comparison} states about this input, coming out {@code holding} — or a decline
     * where the arithmetic reads nothing here.
     *
     * <p>Read once, off the same {@link AffineReading} every other reader of a comparison uses. A
     * second reading of what a comparison says is a second thing to keep in step with how a border
     * is drawn, and the two disagreeing is a region that excludes the very level the border is at.
     *
     * <p>One word for both ways the reading comes back empty. A comparison whose operands are
     * outside the affine fragment and one whose operator places nothing leave the same thing
     * missing here — a statement about a position — and what would lift either is the same piece of
     * work.
     */
    private static OnTheWay of(Condition.Compares comparison, boolean holding, Symbols symbols) {
        Citation at = Citation.of(comparison.at().pos());
        AffineReading read = AffineReading.of(comparison.at(), comparison.reads(), symbols);
        Rel states = read == null ? null : relOf(read.claim());
        if (states == null) {
            return new OnTheWay.Declined(at, OnTheWay.Why.NO_CONSTRAINT_REPRESENTED);
        }
        // The form with the threshold moved into it, since what a domain is told is `f rel 0`.
        LinearForm<NumericTerm> against =
                read.form().minus(LinearForm.constant(read.cut()));
        return new OnTheWay.TakenIn(at, new Cut(against, holding ? states : negated(states)));
    }

    /**
     * Which way a comparison holds, off what it claims about the value it names.
     *
     * <p>Two facts and they are enough: whether the value it names is on the side the comparison is
     * true below, and whether the comparison holds at that value. {@code x <= c} holds below and at
     * it; {@code x < c} holds below and not at it, and {@code c} is above; {@code x >= c} holds
     * above and at it; {@code x > c} holds above and not at it, and {@code c} is below. So the true
     * side is the low one exactly where those two agree.
     */
    private static Rel relOf(ComparisonClaim claim) {
        return switch (claim) {
            case ComparisonClaim.Cut cut -> cut.valueBelongsBelow() == cut.holdsAtTheValue()
                    ? (cut.holdsAtTheValue() ? Rel.LE : Rel.LT)
                    : (cut.holdsAtTheValue() ? Rel.GE : Rel.GT);
            case ComparisonClaim.Singled singled ->
                    singled.holdsAtTheValue() ? Rel.EQ : Rel.NE;
            case ComparisonClaim.Nothing _ -> null;
        };
    }

    /** What it states when it does not hold, which is the whole of the rest of the order. */
    private static Rel negated(Rel rel) {
        return switch (rel) {
            case LE -> Rel.GT;
            case LT -> Rel.GE;
            case GE -> Rel.LT;
            case GT -> Rel.LE;
            case EQ -> Rel.NE;
            case NE -> Rel.EQ;
        };
    }

    /** These conditions, with {@code site} reached under {@code assumed}. */
    static final class Collected {

        private final Map<ComparisonOccurrence, List<OnTheWay>> byComparison = new LinkedHashMap<>();

        void reached(ComparisonOccurrence site, List<OnTheWay> assumed) {
            // The first reading of a site stands. One comparison is read once per call of the helper
            // it is written in, and each of those is a site of its own — two readings arriving under
            // one site would be this walk and the plan disagreeing about what a site is.
            byComparison.putIfAbsent(site, List.copyOf(assumed));
        }

        ReachingCuts made() {
            return new ReachingCuts(byComparison);
        }
    }

    /** What a caller is carrying, with more added, keeping what was already there. */
    private static List<OnTheWay> and(List<OnTheWay> assumed, List<OnTheWay> more) {
        List<OnTheWay> out = new java.util.ArrayList<>(assumed);
        out.addAll(more);
        return List.copyOf(out);
    }

}
