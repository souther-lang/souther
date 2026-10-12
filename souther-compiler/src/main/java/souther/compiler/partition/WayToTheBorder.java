package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * How a row for one border came to be looked for where it is: every condition on the way, in the
 * order the walk met them.
 *
 * <p>An account and not a place. Where a row is looked for is {@link #narrowing(SearchRegion)} and
 * {@link #requirements()} of what the declarations leave, and those are worked out from this
 * whenever somebody needs them — so they cannot come to say different things, because there is only
 * one of them. A pair kept side by side would be values that have to agree and nothing able to check
 * that they do: {@link SearchRegion} answers questions about values and does not say which
 * conditions it was built from, on purpose.
 *
 * <p><b>Three vocabularies, because a condition lands in one of them or in none.</b> What a
 * comparison states is a relation over values and what a fork states is which case a value turned
 * out to be, and neither says the other: a region has no word for a case, and a narrowing orders
 * nothing. The comparisons divide again, because the values a carrier holds are not always numbers:
 * an inequality over a form of them is the arithmetic's, and a position held against a written value
 * on an order that counts nothing is a bound on that order ({@link TakenConstraint}). And a truth
 * of a {@code Bool} position is neither: it is a value, which a region has no order for and a
 * narrowing has no case for ({@link #truths()}). So a search composing a row against this reads
 * them all, and what it still does not represent is {@link #declined()}.
 *
 * <p><b>This is what an answer keeps.</b> A region is a way of asking rather than something that
 * says what it is, and one kept in an answer carries the whole reading of a module's rules — down to
 * the store the reading was made against — into a value two compilations of one source have to
 * compare equal. What a reader of a finished search wants from it is what the way declined, which is
 * here; what a search wants is the region, and a search is where the region is built.
 *
 * <p>What a report may say from this is what the entries say and no more. That some condition was
 * declined does not make the region wider than the rows that reach the border: a condition the
 * arithmetic could not take in may have been implied by the ones it did, or may hold everywhere.
 * What is known is that not everything on the way is represented in it.
 */
public record WayToTheBorder(List<OnTheWay> onTheWay) {

    /** Nothing on the way to take in.
     *
     * <p>Which is a border of a rule that is about the values rather than about a place in a body:
     * an invariant holds wherever a value stands, so there is nowhere for a row to have come from.
     * Said by the empty account rather than by the absence of one. */
    public static final WayToTheBorder UNTOUCHED = new WayToTheBorder(List.of());

    public WayToTheBorder {
        onTheWay = List.copyOf(onTheWay);
    }

    /**
     * Whether a row reaches the border whatever it holds: nothing on the way asks anything of it,
     * and nothing on the way went unread.
     *
     * <p>Which is what makes a value the declarations admit a row at the border. Where something on
     * the way does ask — a comparison taken in, a narrowing, a condition this reading declined — a
     * value the declarations admit may be one no row arriving at the border holds, and what the
     * declarations prove about it is about the position and not about the border.
     */
    public boolean asksNothingOfARow() {
        return onTheWay.stream().allMatch(each ->
                each instanceof OnTheWay.Settled settled && settled.thisWay());
    }

    /**
     * {@code base} narrowed by what of the {@link OnTheWay.TakenIn} entries a region can say, in
     * the order they are written.
     *
     * <p>Three things hold of what comes back, and the first two are {@link SearchRegion}'s own:
     *
     * <pre>what reaches the border ⊆ this ⊆ what the declarations leave</pre>
     *
     * <p>A {@link OnTheWay.Declined} entry never narrows it — it is the record that something on the
     * way is not represented in what comes back. Nor does a {@link OnTheWay.Settled} one, which asks
     * nothing of a row or is a way none takes ({@link #neverComesOut}).
     *
     * <p>And what a {@link OnTheWay.TakenIn} entry asks is what a composer builds a row to meet;
     * the region carries the part of it a region can say, which is settled where the entry is made
     * rather than hoped for here. A relation is that whole; that some element meets something is
     * the container holding one; that every element does is nothing a region says, since a
     * container holding none meets it and a region reads a term inside the elements as one that is
     * there. Nor is the region narrower for each relation: a constraint the rules already hold is
     * taken in again and leaves it where it was. What holds is the one thing a reader of an account
     * acts on — that the region a search runs over admits every row that meets what was taken in.
     */
    public SearchRegion narrowing(SearchRegion base) {
        SearchRegion region = base;
        for (OnTheWay each : onTheWay) {
            // What a narrowing says on the position's own order, which a region can carry: the
            // cases it leaves out are values no row past it holds.
            if (each instanceof OnTheWay.Narrowed narrowed) {
                for (TakenConstraint.AwayFrom hole : narrowed.onItsOrder()) {
                    region = hole.narrowing(region);
                }
            }
            if (each instanceof OnTheWay.TakenIn taken) {
                region = switch (taken.demand()) {
                    // Taken in, and the region is asked to take it in: an entry here is one the
                    // region said it could carry when the walk recorded it.
                    case RowDemand.Relational(var relation) -> relation.narrowing(region);
                    // That some element meets these says nothing every row past it holds of each
                    // element, so the region is narrowed only by the container holding one. What
                    // the element meets is composed where the row is.
                    case RowDemand.Exists(var _, var _, var holdingOne) ->
                            holdingOne.constraint().narrowing(region);
                    // That every element meets these, which a container holding none does. A
                    // region reads a term inside the elements as the value of one that is there,
                    // so narrowed on, it would leave nothing where the rules leave the element
                    // nothing — and the way past an empty container would be proved closed. And
                    // the container is not held to holding none either, since elements meeting
                    // these are a way past it too.
                    case RowDemand.ForAll _ -> region;
                    // How many elements meet a statement, which is no number a region holds.
                    case RowDemand.SoMany _ -> region;
                    // A statement no composer writes toward, which a region holds nothing of.
                    case RowDemand.ForTheRun _ -> region;
                    // Which of two values stands at a position no region measures. The row is
                    // written with it where the row is composed, and the region says nothing of it.
                    case RowDemand.ATruth _ -> region;
                };
            }
        }
        return region;
    }

    /**
     * What has to be true of the parameters for a row to reach the border, off the narrowings the
     * way took in.
     *
     * <p>The other half of what a region is. A region says which numbers a position may hold and has
     * no word for which case a value turned out to be, so a fork on the way lands here — and a
     * composer holding both is holding the whole of what this reading could state.
     *
     * <p>Or nothing, where two narrowings on the way cannot hold together. That is a way no row
     * takes, which is a fact about the model and not something to compose against: read as an
     * absence of requirements, a row would be composed for a border down a path nothing reaches.
     */
    public Requirements.Merge requirements() {
        Requirements out = Requirements.NONE;
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.Narrowed narrowed) {
                Requirements.Merge both = out.merge(narrowed.requirements());
                if (!(both instanceof Requirements.Merge.Merged merged)) {
                    return both;
                }
                out = merged.requirements();
            }
        }
        return new Requirements.Merge.Merged(out);
    }

    /**
     * Which value each {@code Bool} position the way read is asked to hold, off the truths it took
     * in — the third of what a row has to be, beside {@link #narrowing} and {@link #requirements}.
     *
     * <p>Or the position asked for both, which is a way no row takes for the reason two narrowings
     * no position holds together are: whichever condition said which, no value is both.
     */
    public TruthsAsked.Merge truths() {
        List<RowDemand.ATruth> asked = new ArrayList<>();
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.TakenIn(var _, RowDemand.ATruth truth)) {
                asked.add(truth);
            }
        }
        return TruthsAsked.of(asked);
    }

    /**
     * What the way asks of a row, each where it was taken in. Only some of them narrow a region
     * built from this: what every element meets leaves it as it is, since a container holding none
     * meets it.
     */
    public List<OnTheWay.TakenIn> takenIn() {
        List<OnTheWay.TakenIn> out = new ArrayList<>();
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.TakenIn taken) {
                out.add(taken);
            }
        }
        return List.copyOf(out);
    }

    /**
     * The first condition on the way that no row brings out the way the walk went, or empty where
     * every one of them can be.
     *
     * <p>A fact about the model, as two narrowings no position can hold together are
     * ({@link #requirements()}): a border down such a way is one nothing reaches, and a row
     * composed for it would be one for a way no input takes.
     */
    public Optional<OnTheWay.Settled> neverComesOut() {
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.Settled settled && !settled.thisWay()) {
                return Optional.of(settled);
            }
        }
        return Optional.empty();
    }

    /** The ones this reading could state in neither vocabulary, which is what a search composing
     *  against both of them still does not represent — inside an alternative as much as beside
     *  one. */
    public List<OnTheWay.Declined> declined() {
        List<OnTheWay.Declined> out = new ArrayList<>();
        declined(onTheWay, out);
        return List.copyOf(out);
    }

    private static void declined(List<OnTheWay> entries, List<OnTheWay.Declined> into) {
        for (OnTheWay each : entries) {
            switch (each) {
                case OnTheWay.Declined left -> into.add(left);
                case OnTheWay.OneOf several ->
                        several.alternatives().forEach(one -> declined(one, into));
                case OnTheWay.TakenIn _, OnTheWay.Narrowed _, OnTheWay.Settled _ -> { }
            }
        }
    }

    /** The conditions on this way that came out one of several ways, in the order the walk met
     *  them. */
    public List<OnTheWay.OneOf> severalWays() {
        return onTheWay.stream().filter(OnTheWay.OneOf.class::isInstance)
                .map(OnTheWay.OneOf.class::cast).toList();
    }

    /**
     * The ways a row past this one may take, each with one alternative of conditions of several
     * ways taken in where it stands ({@link OnTheWay.OneOf}) — and none of them a way that no row
     * takes for the cases or the truths it asks.
     *
     * <p>Every row past this way is past one alternative of each such condition. Conditions that
     * turn on no position in common are chosen apart, so the ways handed on are each open
     * alternative once and not every way of taking them together ({@link OneOfEach}); and nothing
     * reaches the border where every way of some of them closes, which a walk the figures stopped
     * never says.
     */
    OneOfEach.Walked<OnTheWay> along() {
        return OneOfEach.walk(onTheWay, ASKED_OF_A_ROW, CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
    }

    /**
     * What a way asks of a row as far as whether its conditions hold together: the cases it
     * requires and the truths it asks, which are what two conditions on one way contradict each
     * other in ({@link Reachability#of}), and a condition no row brings out the way taken.
     */
    private record HeldTogether(Requirements requirements, List<RowDemand.ATruth> truths) {}

    private static final OneOfEach.Vocabulary<OnTheWay, HeldTogether> ASKED_OF_A_ROW =
            new OneOfEach.Vocabulary<>() {

                @Override
                public List<List<OnTheWay>> alternatives(OnTheWay entry) {
                    return entry instanceof OnTheWay.OneOf several ? several.alternatives() : null;
                }

                @Override
                public Set<TermPath> positions(OnTheWay entry) {
                    return switch (entry) {
                        case OnTheWay.TakenIn taken -> taken.demand().positions();
                        case OnTheWay.Narrowed narrowed -> {
                            Requirements required = narrowed.requirements();
                            Set<TermPath> out = new LinkedHashSet<>(
                                    required.refinements().keySet());
                            for (NameReach.Crossing each : required.crossings()) {
                                out.add(each.at());
                                out.add(each.to());
                            }
                            yield out;
                        }
                        case OnTheWay.Settled _, OnTheWay.Declined _, OnTheWay.OneOf _ ->
                                Set.of();
                    };
                }

                @Override
                public HeldTogether nothing() {
                    return new HeldTogether(Requirements.NONE, List.of());
                }

                @Override
                public HeldTogether with(HeldTogether so, OnTheWay entry) {
                    return switch (entry) {
                        case OnTheWay.Settled settled -> settled.thisWay() ? so : null;
                        case OnTheWay.Narrowed narrowed ->
                                so.requirements().merge(narrowed.requirements())
                                        instanceof Requirements.Merge.Merged(Requirements both)
                                        ? new HeldTogether(both, so.truths()) : null;
                        case OnTheWay.TakenIn(var _, RowDemand.ATruth truth) -> {
                            List<RowDemand.ATruth> truths = new ArrayList<>(so.truths());
                            truths.add(truth);
                            yield TruthsAsked.of(truths) instanceof TruthsAsked.Merge.Merged
                                    ? new HeldTogether(so.requirements(), truths) : null;
                        }
                        case OnTheWay.TakenIn _, OnTheWay.Declined _, OnTheWay.OneOf _ -> so;
                    };
                }
            };
}
