package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Symbols;
import souther.compiler.coverage.ComparisonOccurrence;
import souther.compiler.coverage.CoverageSites;
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
 * that takes a coverage item away. So what is here is what the walk itself put in, and a condition
 * the arithmetic has no word for leaves nothing behind.
 *
 * <p><b>Its own value and not its arm.</b> Under {@code A && B} the {@code then} arm is reached with
 * both holding, and the {@code else} arm with neither settled — a row can be in it for failing
 * either. Under {@code A || B} it is the other way round. Which of the two a comparison is in is
 * {@link GuardThresholds}'s reading of the condition, and taking an arm for a conjunct is how a
 * region would come to exclude rows that reach the guard.
 *
 * <p>Nothing here says a row that satisfies all of this arrives. A condition of a shape the
 * arithmetic cannot read is not on the list, so what this describes is wider than what arrives —
 * which is what {@link SearchRegion} promises and what a proof of unreachability rests on.
 */
public record ReachingCuts(Map<ComparisonOccurrence, List<ReachingCuts.Cut>> byComparison) {

    public static final ReachingCuts NONE = new ReachingCuts(Map.of());

    public ReachingCuts {
        byComparison = Map.copyOf(byComparison);
    }

    /** One thing a row had to satisfy to get here: {@code form rel 0} over this input's terms. */
    public record Cut(LinearForm<NumericTerm> form, Rel rel) {}

    /**
     * {@code region}, narrowed to what reaches {@code site}.
     *
     * <p>{@code region} itself where nothing was collected there, which is a comparison at the top
     * of a body as much as it is one this could read nothing on the way to. The two are not told
     * apart because nothing downstream acts on the difference: both leave a region as wide as the
     * declarations, and both are sound.
     */
    public SearchRegion narrowing(SearchRegion region, ComparisonOccurrence site) {
        for (Cut each : byComparison.getOrDefault(site, List.of())) {
            region = region.assuming(each.form(), each.rel());
        }
        return region;
    }

    /**
     * Each comparison of {@code condition}, filed under what a row had already satisfied when it
     * ran.
     *
     * <p><b>In the order a condition is evaluated in, which is what makes this per comparison and
     * not per fork.</b> A condition stops as soon as it is settled: under {@code A && B} the second
     * comparison runs only where the first held, and under {@code A || B} only where it did not. So
     * what has been established by the time a comparison runs differs between the comparisons of one
     * condition, and a reading that handed every comparison of a fork the same thing would be
     * answering about the fork.
     *
     * <p>That is not a missing case, it is the case. Sequential guards and the same conditions run
     * together with {@code &&} state the same model, and a coverage answer that differed between
     * them would be a fact about how the author spelled the condition — the guard at the end of a
     * chain would be searched for over everything its positions could ever hold, which is the
     * defect this whole type exists to remove, arriving by way of a rewrite that changes nothing.
     *
     * <p>Descends through {@code &&} and {@code ||} and nothing else, which is what a condition is
     * built out of. Anything else is where the arithmetic stops, and it contributes nothing rather
     * than being guessed at.
     */
    static void collect(Condition condition, List<Cut> before, CoverageSites.Plan plan,
                        Symbols symbols, Collected out) {
        switch (condition) {
            case Condition.Both both -> {
                collect(both.left(), before, plan, symbols, out);
                collect(both.right(), and(before, stating(both.left(), true, symbols)), plan,
                        symbols, out);
            }
            case Condition.Either either -> {
                collect(either.left(), before, plan, symbols, out);
                collect(either.right(), and(before, stating(either.left(), false, symbols)), plan,
                        symbols, out);
            }
            case Condition.Compares one ->
                    plan.comparisonAt(one.at()).ifPresent(site -> out.reached(site, before));
            case Condition.NotRead _ -> {
                // Nothing runs here as far as this reading is concerned, so nothing is filed and
                // nothing is established for whatever stands beside it.
            }
        }
    }

    /**
     * What {@code node} coming out {@code holding} says about this input, where anything can be
     * said.
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
     * names neither, and narrowing on either would exclude rows that arrive.
     */
    static List<Cut> stating(Condition node, boolean holding, Symbols symbols) {
        return switch (node) {
            // A conjunction coming out true is both its operands true, and a disjunction coming out
            // false is both false. The other two ways round say a disjunction of things, which is
            // not a list of cuts and is not approximated into one: `A && B` being false says one of
            // them failed and names neither, and narrowing on either would exclude rows that arrive.
            case Condition.Both both when holding ->
                    and(stating(both.left(), true, symbols), stating(both.right(), true, symbols));
            case Condition.Either either when !holding ->
                    and(stating(either.left(), false, symbols),
                            stating(either.right(), false, symbols));
            case Condition.Compares one -> {
                Cut cut = of(one, holding, symbols);
                yield cut == null ? List.of() : List.of(cut);
            }
            default -> List.of();
        };
    }

    /**
     * What {@code comparison} states about this input, coming out {@code holding} — or null where
     * the arithmetic reads nothing here.
     *
     * <p>Read once, off the same {@link AffineReading} every other reader of a comparison uses. A
     * second reading of what a comparison says is a second thing to keep in step with how a border
     * is drawn, and the two disagreeing is a region that excludes the very level the border is at.
     */
    private static Cut of(Condition.Compares comparison, boolean holding, Symbols symbols) {
        AffineReading read = AffineReading.of(comparison.at(), comparison.reads(), symbols);
        if (read == null) {
            return null;
        }
        Rel states = relOf(read.claim());
        if (states == null) {
            return null;
        }
        // The form with the threshold moved into it, since what a domain is told is `f rel 0`.
        LinearForm<NumericTerm> against =
                read.form().minus(LinearForm.constant(read.cut()));
        return new Cut(against, holding ? states : negated(states));
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

    /** These cuts, with {@code site} reached under {@code assumed}. */
    static final class Collected {

        private final Map<ComparisonOccurrence, List<Cut>> byComparison = new LinkedHashMap<>();

        void reached(ComparisonOccurrence site, List<Cut> assumed) {
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
    private static List<Cut> and(List<Cut> assumed, List<Cut> more) {
        if (more.isEmpty()) {
            return assumed;
        }
        List<Cut> out = new java.util.ArrayList<>(assumed);
        out.addAll(more);
        return List.copyOf(out);
    }

}
