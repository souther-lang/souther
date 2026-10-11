package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.meaning.AnswerAsAnInput;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;

/**
 * The numbers of the input a statement about an answer turns on, put at values before the answer is
 * composed.
 *
 * <p>Which value a dependency has to answer with is a function of what the row writes at the
 * input: "some element is at most {@code on}" is met by an element for one {@code on} and by
 * another for the next. Composed apart from the row, the answer would be a value for a row nobody
 * wrote. So the numbers are put at values first, the answer is composed for those, and the row is
 * held to the same values — a pair that meets the statement together, which neither half composed
 * alone could promise.
 *
 * <p><b>Several pairs to try, and the first that composes is the one taken.</b> A value that suits
 * the way for the number need not suit the answer: the type of the answer may keep its elements
 * above ten, and the number then has to be ten or more for any element to be at most it. So a
 * number is offered at the values the answer's own bounds make the statement hold at, ahead of the
 * ones the way alone leaves, and the caller asks whether the answer composed for a pair, going on
 * to the next where it did not. Each pair puts the number at a value the region of the way takes
 * in, so a row that reaches the way is not given up for one that does not.
 *
 * <p><b>Two figures, and each bounds the walk and not only what it finds.</b> What is looked at is
 * {@link CompositionBudget#CHOICES_OF_INPUT_NUMBERS_LOOKED_AT}, counted whether or not the way took
 * the choice in, so a walk over a large product of values the way refuses stops where it is told
 * to; and what is offered to compose an answer for is
 * {@link CompositionBudget#PAIRS_OF_INPUT_NUMBERS_AND_AN_ANSWER_TRIED}. Where either ended the walk
 * with more to look at, {@link Pairs#stoppedBy} says which: a statement that none of those composed
 * for is one nothing was composed against, and never one no value meets.
 */
public final class InputNumbersAnAnswerTurnsOn {

    /**
     * The pairs to try, and which figure ended the looking where one did.
     *
     * @param tried     the pairs, the most promising first; one that puts nothing anywhere where
     *                  no statement names a number of the input
     * @param stoppedBy the figures that ended the walk with a choice left unlooked at, which is the
     *                  one thing a search that found no pair has to say about why; empty where
     *                  every choice was looked at
     */
    public record Pairs(List<InputNumbersAnAnswerTurnsOn> tried,
                        Set<CompositionBudget> stoppedBy) {

        public Pairs {
            tried = List.copyOf(tried);
            stoppedBy = Set.copyOf(stoppedBy);
        }

        /** Whether a figure ended the walk with something left unlooked at. */
        public boolean someLeftUntried() {
            return !stoppedBy.isEmpty();
        }
    }

    /** What the subject an answer is composed over is, which says where the answer's places can
     *  lie. */
    public interface AnswerSubjectOf {

        /** The subject for the whole of what {@code dependency} answers, or null where there is
         *  none — an answer that is a union of cases has one subject apiece. */
        MeasuredInput of(ValueName.Behavior dependency);
    }

    private final Map<NumericTerm, ExactRatio> values;
    private final Reachability.Reaching reaching;

    private InputNumbersAnAnswerTurnsOn(Map<NumericTerm, ExactRatio> values,
                                        Reachability.Reaching reaching) {
        this.values = Collections.unmodifiableMap(new LinkedHashMap<>(values));
        this.reaching = reaching;
    }

    /** The value each number was put at. */
    public Map<NumericTerm, ExactRatio> values() {
        return values;
    }

    /** The way, with each of those numbers held at its value. */
    public Reachability.Reaching reaching() {
        return reaching;
    }

    /**
     * The pairs to try for {@code demands} along {@code reaching}, the most promising first.
     *
     * <p>One, and the way itself, where no statement names a number of the input — which is every
     * way over an answer alone. And one where no value of the numbers the statements name is taken
     * in by the way: the way left as it was, and the statements for those numbers are ones no value
     * was composed against.
     */
    public static Pairs of(AnswersDemanded demands, Reachability.Reaching reaching,
                           AnswerSubjectOf answers) {
        InputNumbersAnAnswerTurnsOn unpinned =
                new InputNumbersAnAnswerTurnsOn(Map.of(), reaching);
        Map<NumericTerm, List<ExactRatio>> offered = new LinkedHashMap<>();
        ConditionReportAnchor anchor = null;
        for (AnswerDemand each : demands.stated()) {
            if (!(each instanceof AnswerDemand.AStatement statement)) {
                continue;
            }
            Set<NumericTerm> named = AnswerAsAnInput.inputNumbersIn(statement.statement());
            if (named == null || named.isEmpty()) {
                continue;
            }
            anchor = anchor == null ? statement.anchor() : anchor;
            MeasuredInput subject = answers.of(statement.of().dependency());
            for (NumericTerm term : named) {
                offered.computeIfAbsent(term, _ -> new ArrayList<>())
                        .addAll(boundedByTheAnswer(statement, term, subject));
            }
        }
        if (offered.isEmpty()) {
            return new Pairs(List.of(unpinned), Set.of());
        }
        SearchRegion region = reaching.region();
        List<NumericTerm> terms = new ArrayList<>(offered.keySet());
        List<List<ExactRatio>> candidates = new ArrayList<>();
        for (NumericTerm term : terms) {
            List<ExactRatio> pool = new ArrayList<>(offered.get(term));
            pool.addAll(allowedByTheWay(region, term));
            candidates.add(inTheOrderOffered(region, term, pool));
        }
        CompositionBudget pairsFigure = CompositionBudget.PAIRS_OF_INPUT_NUMBERS_AND_AN_ANSWER_TRIED;
        CompositionBudget lookedFigure = CompositionBudget.CHOICES_OF_INPUT_NUMBERS_LOOKED_AT;
        int mostPairs = pairsFigure.maximum();
        int mostLooked = lookedFigure.maximum();
        List<InputNumbersAnAnswerTurnsOn> out = new ArrayList<>();
        Set<CompositionBudget> stoppedBy = EnumSet.noneOf(CompositionBudget.class);
        int[] looked = {0};
        ConditionReportAnchor at = anchor;
        eachChoice(candidates, 0, new ArrayList<>(), choice -> {
            // The walk is bounded before a choice is looked at: one counted past the figure is one
            // that was never put to the way.
            if (looked[0] == mostLooked) {
                stoppedBy.add(lookedFigure);
                return false;
            }
            looked[0]++;
            InputNumbersAnAnswerTurnsOn pair = pinned(reaching, terms, choice, at);
            if (pair == null) {
                return true;
            }
            if (out.size() == mostPairs) {
                stoppedBy.add(pairsFigure);
                return false;
            }
            out.add(pair);
            return true;
        });
        return out.isEmpty() ? new Pairs(List.of(unpinned), stoppedBy) : new Pairs(out, stoppedBy);
    }

    /**
     * {@code reaching} with {@code terms} held at {@code choice}, or null where the way does not
     * take that in.
     */
    private static InputNumbersAnAnswerTurnsOn pinned(Reachability.Reaching reaching,
                                                     List<NumericTerm> terms,
                                                     List<ExactRatio> choice,
                                                     ConditionReportAnchor anchor) {
        SearchRegion region = reaching.region();
        Map<NumericTerm, ExactRatio> values = new LinkedHashMap<>();
        List<OnTheWay.TakenIn> held = new ArrayList<>();
        for (int at = 0; at < terms.size(); at++) {
            LinearForm<NumericTerm> pin = new LinearForm<>(choice.get(at).negated(),
                    Map.of(terms.get(at), ExactRatio.ONE));
            if (!(region.assuming(pin, Rel.EQ)
                    instanceof SearchRegion.Assumption.Taken(SearchRegion narrowed))) {
                return null;
            }
            region = narrowed;
            values.put(terms.get(at), choice.get(at));
            held.add(new OnTheWay.TakenIn(anchor, new RowDemand.Relational(
                    new TakenConstraint.Affine(pin, Rel.EQ))));
        }
        List<OnTheWay.TakenIn> cuts = new ArrayList<>(reaching.boundedOnTheWay());
        cuts.addAll(held);
        return new InputNumbersAnAnswerTurnsOn(values, new Reachability.Reaching(region,
                reaching.requirements(), reaching.truths(), cuts, reaching.ways()));
    }

    /**
     * Each way of choosing one value for every number, the first number changing slowest, handed
     * to {@code visit} one at a time until it says to stop.
     *
     * <p>One at a time and never the product built first: how many ways there are is the figure of
     * the search's to bound, and a list of every one would be the size of what it declines.
     *
     * @return whether every way was visited, which is false where {@code visit} stopped it
     */
    private static boolean eachChoice(List<List<ExactRatio>> candidates, int at,
                                      List<ExactRatio> chosen,
                                      Predicate<List<ExactRatio>> visit) {
        if (at == candidates.size()) {
            return visit.test(List.copyOf(chosen));
        }
        for (ExactRatio value : candidates.get(at)) {
            chosen.add(value);
            boolean more = eachChoice(candidates, at + 1, chosen, visit);
            chosen.removeLast();
            if (!more) {
                return false;
            }
        }
        return true;
    }

    /**
     * The values of {@code term} at which {@code statement} can hold, given where the places of the
     * answer it is compared with can lie.
     *
     * <p>Each comparison that names the number and places of the answer alone is solved for the
     * number at the ends of those places' bounds: "{@code x - on <= 0}" with {@code x} at least ten
     * holds from {@code on = 10}. The value itself and the ones beside it, since a strict relation
     * holds one past. A comparison that names another number of the input is not solved here — that
     * number's value is not known yet.
     */
    private static List<ExactRatio> boundedByTheAnswer(AnswerDemand.AStatement statement,
                                                       NumericTerm term, MeasuredInput subject) {
        if (subject == null) {
            return List.of();
        }
        String head = subject.parameters().getFirst();
        List<LinearForm<Quantity>> comparisons = AnswerAsAnInput.comparisonsIn(
                statement.statement(), head, subject.rules().inners(), subject.symbols());
        if (comparisons == null) {
            return List.of();
        }
        SearchRegion answerRegion = subject.quantities().region();
        List<ExactRatio> out = new ArrayList<>();
        for (LinearForm<Quantity> form : comparisons) {
            ExactRatio by = coefficientOf(form, term);
            if (by == null || by.signum() == 0) {
                continue;
            }
            List<NumericTerm> places = new ArrayList<>();
            List<ExactRatio> weights = new ArrayList<>();
            boolean solvable = true;
            for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
                if (!(each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm other))
                        || other.equals(term)) {
                    continue;
                }
                if (!other.subjectPath().head().equals(head)) {
                    solvable = false;
                    break;
                }
                places.add(other);
                weights.add(each.getValue());
            }
            if (!solvable || places.isEmpty()) {
                continue;
            }
            for (ExactRatio solved : solvedAtTheEnds(form.constant(), by, places, weights,
                    answerRegion)) {
                // The value and the ones beside it, each only where it is a number a ratio holds.
                out.add(solved);
                ExactRatio above = plusOne(solved);
                if (above != null) {
                    out.add(above);
                }
                ExactRatio below = minusOne(solved);
                if (below != null) {
                    out.add(below);
                }
            }
        }
        return out;
    }

    private static ExactRatio coefficientOf(LinearForm<Quantity> form, NumericTerm term) {
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm one)
                    && one.equals(term)) {
                return each.getValue();
            }
        }
        return null;
    }

    /**
     * {@code term} such that {@code constant + by·term + Σ weights·places} is nought, with each
     * place at each end of what the answer's bounds hold of it.
     */
    private static List<ExactRatio> solvedAtTheEnds(ExactRatio constant, ExactRatio by,
                                                    List<NumericTerm> places,
                                                    List<ExactRatio> weights,
                                                    SearchRegion answerRegion) {
        List<List<ExactRatio>> ends = new ArrayList<>();
        for (NumericTerm place : places) {
            List<ExactRatio> here = new ArrayList<>();
            if (answerRegion.projectionOf(place)
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds)) {
                for (Endpoint end : Arrays.asList(bounds.min(), bounds.max())) {
                    if (end != null && end.at() instanceof Count at) {
                        here.add(at.exactly());
                    }
                }
            }
            if (here.isEmpty()) {
                return List.of();
            }
            ends.add(here);
        }
        List<ExactRatio> out = new ArrayList<>();
        // The ends of every place, which is as many choices as the places have ends multiplied, so
        // the walk over them is held to what a walk over the input's numbers is.
        int[] looked = {0};
        int mostLooked = CompositionBudget.CHOICES_OF_INPUT_NUMBERS_LOOKED_AT.maximum();
        eachChoice(ends, 0, new ArrayList<>(), choice -> {
            if (looked[0]++ == mostLooked) {
                return false;
            }
            ExactRatio rest = constant;
            for (int at = 0; at < choice.size() && rest != null; at++) {
                ExactRatio weighed = weights.get(at).times(choice.get(at)).orNull();
                rest = weighed == null ? null : rest.plus(weighed).orNull();
            }
            ExactRatio solved = rest == null ? null : rest.negated().dividedBy(by).orNull();
            if (solved != null) {
                out.add(solved);
            }
            return true;
        });
        return out;
    }

    private static ExactRatio plusOne(ExactRatio value) {
        return value.plus(ExactRatio.ONE).orNull();
    }

    private static ExactRatio minusOne(ExactRatio value) {
        return value.minus(ExactRatio.ONE).orNull();
    }

    /**
     * The values {@code term} may be put at that the way alone suggests: the ends of what it holds
     * of it, the values just inside them, and then nought and one.
     */
    private static List<ExactRatio> allowedByTheWay(SearchRegion region, NumericTerm term) {
        if (!(region.projectionOf(term)
                instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds))) {
            return List.of();
        }
        List<ExactRatio> out = new ArrayList<>();
        if (bounds.min() != null && bounds.min().at() instanceof Count low) {
            out.add(low.exactly());
            out.add(low.plus(1).exactly());
        }
        if (bounds.max() != null && bounds.max().at() instanceof Count high) {
            out.add(high.exactly());
            out.add(high.minus(1).exactly());
        }
        out.add(ExactRatio.ZERO);
        out.add(ExactRatio.ONE);
        return out;
    }

    /** {@code pool} without repeats and without what the way does not allow, in the order it was
     *  offered. */
    private static List<ExactRatio> inTheOrderOffered(SearchRegion region, NumericTerm term,
                                                      List<ExactRatio> pool) {
        NumericDomain.Bounds bounds = region.projectionOf(term)
                instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds within)
                ? within : null;
        Set<ExactRatio> seen = new LinkedHashSet<>();
        for (ExactRatio each : pool) {
            if (bounds == null || admits(bounds, each)) {
                seen.add(each);
            }
        }
        return List.copyOf(seen);
    }

    private static boolean admits(NumericDomain.Bounds bounds, ExactRatio value) {
        return Count.written(value) instanceof ExactAnswer.Held<Optional<Count>>(var written)
                && written.isPresent() && bounds.admits(written.get());
    }
}
