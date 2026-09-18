package souther.compiler.query;

import souther.compiler.partition.Generator;
import souther.compiler.partition.ConditionGap;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * What looking for a row at one point came to, over every search that was made for it.
 *
 * <p><b>Several, because one reading of a line can be searched more than once.</b> A helper called
 * from two arms is one line read once — the same authored line at the same target — and a row for it
 * is composed under each caller's own conditions, so one reading has two searches and they can have
 * come to different things. Held as one outcome, the point carried whichever of them a fold put
 * first, and what the other found out was gone before anything could read it.
 *
 * <p><b>Nothing here ranks them.</b> A row that was composed, a search a budget of this compiler's
 * ended, a search that ran to the end of what this compiler writes, and a search that ran through
 * what it had are facts about one point; there is no order in which one of them stands for another,
 * and every question a reader puts is answered by looking at all of them. What is chosen is a row to offer somebody ({@link #rowToOffer}), which is
 * a choice about what to show and not about what happened.
 */
public record SearchOutcomes(List<ItemAssessment.Attempt> each) {

    public SearchOutcomes {
        each = List.copyOf(each);
    }

    /** Nobody asked for a value to be built here. */
    public static SearchOutcomes none() {
        return new SearchOutcomes(List.of());
    }

    /** One search, or none where {@code attempt} is null. */
    public static SearchOutcomes of(ItemAssessment.Attempt attempt) {
        return attempt == null ? none() : new SearchOutcomes(List.of(attempt));
    }

    /** These and those, in the order they were made. */
    public SearchOutcomes plus(SearchOutcomes other) {
        if (other.each.isEmpty()) {
            return this;
        }
        if (each.isEmpty()) {
            return other;
        }
        List<ItemAssessment.Attempt> out = new ArrayList<>(each);
        out.addAll(other.each);
        return new SearchOutcomes(out);
    }

    /** Whether anybody searched here at all. */
    public boolean ran() {
        return !each.isEmpty();
    }

    /**
     * The one search there was.
     *
     * <p>For a caller that already knows the point was searched once — a line one behavior read
     * once is searched once, and most of them are. Checked rather than assumed: a caller that asks
     * this of a point searched twice is a caller reading one of the two as the whole answer, which
     * is the thing this type exists to stop, and it gets told rather than given the first.
     */
    public ItemAssessment.Attempt only() {
        if (each.size() != 1) {
            throw new IllegalStateException(
                    "one search was asked for at a point that had " + each.size() + ": " + each);
        }
        return each.get(0);
    }

    /**
     * Whether a row was composed and read back standing where it was composed for.
     *
     * <p>Any one of them. The searches are of one point and the point is one point, so what one of
     * them showed about it, they all showed.
     */
    public boolean certified() {
        return each.stream().anyMatch(it -> it instanceof ItemAssessment.Attempt.Certified);
    }

    /**
     * Which figures of this compiler's leave a showing here unable to establish the point, and
     * empty where none do.
     *
     * <p>Said that way and not as "stopped", because the outcomes that name a figure did not all
     * stop: one search ran to the end of a plan short of the point, and one point was never
     * searched at all. What they have in common is what this is for — the question is open, and
     * open on something somebody could raise.
     *
     * <p>All of them. Two searches held back by two figures are two pieces of work, and a reader
     * asking what would have to give is owed both.
     *
     * <p>Kept inside this package, where the one caller is what puts them together
     * ({@link WritabilityKnowledge#of}). They are as many as the searches were, in the order the
     * searches are held, so a reader outside would be taking a plurality nobody has put together
     * and saying it in an order nobody chose.
     */
    Set<EstablishmentGap> prevented() {
        Set<EstablishmentGap> out = new LinkedHashSet<>();
        for (ItemAssessment.Attempt attempt : each) {
            if (attempt instanceof ItemAssessment.Attempt.Prevented it) {
                out.add(it.by());
            }
        }
        return out;
    }

    /**
     * Whether the model itself leaves no value at the point, over every search that was made for
     * it.
     *
     * <p>Asked here and not of one outcome, for the reason {@link #prevented()} is: a point is
     * searched once per way of standing the dependencies in, and what the point comes to is what
     * they all came to. One search proving there is nothing to find proves it of the region that
     * search was composed in, and another caller's region is another region — so a point with a
     * proof beside a search a budget ended has not been shown to be one no row can be written at,
     * and a reader taking the proof for the point's answer would be reading one search as all of
     * them.
     *
     * <p>So the quantifier is universal, and it is this type's to own. Left to a caller, the
     * plurality would be folded again at every place that asks, and an {@code anyMatch} written at
     * one of them is the answer of whichever search a walk reached first.
     *
     * <p>A search nobody could make is not a proof and neither is a walk that stopped, so a point
     * holding one of those is not this whatever else it holds. Which words prove it is the search's
     * own answer ({@link Generator.UnresolvedCombination.Reason#provesInfeasible}), and false is
     * the searches not settling it rather than the rules leaving a value there.
     *
     * <p>Kept inside this package with the one caller that reads it
     * ({@link WritabilityKnowledge#of}).
     */
    boolean provesInfeasible() {
        // Nothing was searched, so nothing proved anything. Said before the quantifier rather than
        // left to it: a universal over no outcomes is true, and true here would be a point nobody
        // looked at coming back as one the rules refuse.
        return ran() && each.stream().allMatch(it ->
                it instanceof ItemAssessment.Attempt.Unresolved unresolved
                        && unresolved.why().reason().provesInfeasible());
    }

    /**
     * A row to put in front of somebody, where any of these composed one.
     *
     * <p>A choice, and the one choice here that is allowed to be one. What a person is offered is
     * one row — two rows for one point is two answers they have to separate — so a row read back
     * where it was built for is offered before one nothing could place. That decides what to show
     * and takes nothing away: what each search came to is still here for whoever asks.
     */
    public Optional<ItemAssessment.Attempt.Built> rowToOffer() {
        Optional<ItemAssessment.Attempt.Built> placed = each.stream()
                .filter(it -> it instanceof ItemAssessment.Attempt.Certified)
                .map(ItemAssessment.Attempt.Built.class::cast)
                .findFirst();
        return placed.isPresent() ? placed : each.stream()
                .filter(it -> it instanceof ItemAssessment.Attempt.Built)
                .map(ItemAssessment.Attempt.Built.class::cast)
                .findFirst();
    }

    /**
     * The searches a reader is owed a sentence about, one per thing that happened.
     *
     * <p><b>Told apart by what they are and never by how they read.</b> Two searches of one reading
     * that came to the same thing are one piece of news; two that came to different things are two,
     * however alike a renderer's words for them. Left to whoever writes the sentences, the same two
     * facts collapse or do not depending on the wording, which puts a decision about what happened
     * in the one place that has stopped looking at it.
     *
     * <p>A search that composed a row is not among them. What such a search came to is the row,
     * which a reader gets by being offered it; what this answers is what a point with nothing at it
     * has to say for itself.
     */
    public List<ItemAssessment.Attempt> worthSaying() {
        List<ItemAssessment.Attempt> out = new ArrayList<>();
        for (ItemAssessment.Attempt attempt : each) {
            if (attempt instanceof ItemAssessment.Attempt.Built
                    || attempt instanceof ItemAssessment.Attempt.Unavailable) {
                continue;
            }
            if (!out.contains(attempt)) {
                out.add(attempt);
            }
        }
        return List.copyOf(out);
    }

    /** Every condition on the way that none of these composed against. */
    public List<ConditionGap> unaccountedFor() {
        List<ConditionGap> out = new ArrayList<>();
        for (ItemAssessment.Attempt attempt : each) {
            for (ConditionGap gap : attempt.unaccountedFor()) {
                if (!out.contains(gap)) {
                    out.add(gap);
                }
            }
        }
        return List.copyOf(out);
    }
}
