package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * How far a set of rules lets a whole form run — the one reading of that question there is.
 *
 * <p>{@link Reach} is the arithmetic: what a weighted sum runs between, given what each of its
 * positions runs between. This is the question put to a state, which is a different one: what the
 * positions run between is itself something the rules decide, and the rules say things about sums
 * that no position's own ends carry.
 *
 * <p><b>Three routes, met.</b> What the ends leave the form's own positions; the relation on a
 * difference of two of them, where the form has that shape; and one rule taken off the form, leaving
 * a residual the ends bound — {@code f <= u} with {@code g - f <= r} gives {@code g <= r + u}, which
 * is what relates a guard over a computed value to what the type of the value it was compared
 * against guarantees. Whichever route bounds it tightest is the answer, and a route that bounds it
 * not at all costs nothing.
 *
 * <p><b>One rule to a query, and this is where that is said.</b> The unit is one call to
 * {@link #of}: it may take one rule as a premise, and the residual left once that premise is off is
 * bounded by the ends and the differences and by nothing further, so no query adds two rules
 * together. The unit matters because a caller's own act is usually larger than a query — reducing a
 * rule one position at a time is one act and asks a query per position, so what such an act depends
 * on is its own rule and whatever single premise each query took. The two are not the same count,
 * and saying "one rule" without saying one rule to what is what left it readable both ways.
 *
 * <p>Longer chains are not this. What a query derives becomes an end the next round reads, so rules
 * compose through successive ranges — which is what keeps a query a function of the state it was
 * handed rather than of how many times it has been asked.
 *
 * <p><b>Nothing else states this rule.</b> Every reader here is a reader and points back; a copy of
 * it beside a caller is a second statement to keep true, and the one that stood beside
 * {@link NumericDomain#proves} went on describing a residual bounded by the ends alone after the
 * differences had been added to it.
 *
 * <p><b>Held two ways before this, and the two disagreed.</b> The question a goal asked read the
 * ends, the differences and one rule; the question a rule's own reduction asked read the ends alone
 * ({@link AffineReduction}), and the weaker of the two was the one that built the ends every
 * one-position question is answered by. So a relation a guard stated was held and never read: a
 * construction over {@code x - y} under {@code guard x >= y} came out owed, while the same
 * construction under a guard putting each of the two in a range of its own came out discharged
 *. Which of those an author wrote is not a distinction the language makes.
 *
 * <p><b>A value, not a view.</b> What it reads is handed over — the rules, the ends at the start of
 * the round, and the differences closed over those rules — and it cannot ask for anything else. That
 * is what makes a round's readings a function of the round it started in rather than of the order
 * the rules happened to be read in.
 *
 * @param <A> what the caller calls a position
 */
final class FormReach<A> {

    private final List<AffineConstraint<A>> rules;
    private final Box<A> ends;
    private final DifferenceBounds<A> differences;

    /** The one order a walk of a form's positions takes them in — see {@link CanonicalOrder}. */
    private final CanonicalOrder<A> order;

    /** Every half-space of every rule, stated once for the round — see {@link #premises}. Null
     *  until the first form of two or more positions asks. */
    private List<Premise<A>> premises;

    private FormReach(List<AffineConstraint<A>> rules, Box<A> ends,
                      DifferenceBounds<A> differences, CanonicalOrder<A> order) {
        this.rules = rules;
        this.ends = ends;
        this.differences = differences;
        this.order = order;
    }

    /**
     * The reading {@code rules} give, against the ends they have been worked out to leave so far.
     *
     * <p>Refused where the differences hold nothing, for the reason {@link DifferenceBounds} refuses
     * to answer there: no bound is the tightest when every bound holds, and "no bound" reads as
     * unbounded, which is the opposite of the truth. A caller with a state that holds nothing has an
     * answer already and does not need this one — {@link ClosedState} asks {@code holdsNothing}
     * before it ever builds a round.
     */
    static <A> FormReach<A> over(List<AffineConstraint<A>> rules, Box<A> ends,
                                 DifferenceBounds<A> differences, CanonicalOrder<A> order) {
        if (differences.holdsNothing()) {
            throw new IllegalStateException(
                    "nothing is left, so there is no reach to read; ask holdsNothing first");
        }
        return new FormReach<>(rules, ends, differences, order);
    }

    /** The ends this was handed, for a reader that needs them as well and must not derive a second
     *  set of its own. */
    Box<A> ends() {
        return ends;
    }

    /** The rules this reads. Handed back so that a reader reducing them reduces the very rules this
     *  answers from: two lists would be two chances for the set being narrowed and the set being
     *  read to come apart. */
    List<AffineConstraint<A>> rules() {
        return rules;
    }

    /** What {@code Σ coefs·position + constant} runs between. */
    Reach of(Map<A, ExactRatio> coefs, ExactRatio constant) {
        return between(inOrder(coefs), constant, null);
    }

    /**
     * {@code coefs} in the one order its positions decide, which every sum here is taken in.
     *
     * <p>Taken once, where a form comes in, because the sums are exact and an exact sum can fail
     * part of the way: a term far enough apart in scale from the sum so far has no representation
     * beside it, and whether it does turns on which terms were added before it. Walked in whatever
     * order the caller's map iterates in — a hash table's, a copy whose order changes from one run
     * to the next — a bound would be found or not found by the order of a table rather than by the
     * form. Every walk below keeps the order it is handed.
     */
    private Map<A, ExactRatio> inOrder(Map<A, ExactRatio> coefs) {
        // One term is added in one order, and most forms here have one.
        if (coefs.size() < 2) {
            return coefs;
        }
        Map<A, ExactRatio> out = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> each : order.walking(coefs.entrySet(), Map.Entry::getKey)) {
            out.put(each.getKey(), each.getValue());
        }
        return out;
    }

    /**
     * The same for the rest of {@code asking}'s own form, read while {@code asking} is being reduced
     * — with {@code asking} itself left out of the rules.
     *
     * <p>Not a soundness measure. Every route here derives a consequence of the rules, and a
     * consequence is a sound premise however it was reached, so a rule bounding the rest of itself
     * cannot make what comes back admit less than the rules do. It is left out because it was
     * measured to buy nothing, and a derivation that buys nothing and raises the question of whether
     * a conclusion propped up its own premise is better not written.
     *
     * <p>What is left out is the rule, and not what the closure made of it. A rule of difference
     * shape has been read into the closed differences before this is asked anything, and those are
     * the state rather than any one rule's — so such a rule reaches its own rest by that route
     * whatever is done here, as it did before this existed. Excluding it there would mean closing
     * the differences afresh for every rule, which is a cost for a distinction nothing has asked
     * for.
     */
    Reach ofTheRestOf(AffineConstraint<A> asking, Map<A, ExactRatio> coefs, ExactRatio constant) {
        return between(inOrder(coefs), constant, asking);
    }

    /**
     * What the ends and the closed differences leave the form, with the rules beside them left out.
     *
     * <p>A different question from what the rules leave it, and the one an account of what was
     * derived wants — and not the product of the ranges either, which holds less than this does.
     */
    ExactCut mostFromTheEndsAndTheDifferences(Map<A, ExactRatio> coefs, ExactRatio constant) {
        return fromTheEnds(inOrder(coefs), constant);
    }

    /** The highest the form is proven to come to, or null where nothing bounds it above. */
    ExactCut most(Map<A, ExactRatio> coefs, ExactRatio constant) {
        return highest(inOrder(coefs), constant, null);
    }

    private Reach between(Map<A, ExactRatio> coefs, ExactRatio constant, AffineConstraint<A> without) {
        ExactCut most = highest(coefs, constant, without);
        // The least a form comes to is the highest its negation comes to, on the other side of
        // nought. Asked that way rather than derived a second time, so the two ends are one reading
        // and cannot come apart.
        ExactCut flipped = highest(negated(coefs), constant.negated(), without);
        ExactCut least = flipped == null ? null
                : new ExactCut(flipped.at().negated(), flipped.inclusive());
        return new Reach(least, most);
    }

    private static <A> Map<A, ExactRatio> negated(Map<A, ExactRatio> coefs) {
        Map<A, ExactRatio> out = new LinkedHashMap<>();
        coefs.forEach((position, weight) -> out.put(position, weight.negated()));
        return out;
    }

    private ExactCut highest(Map<A, ExactRatio> coefs, ExactRatio constant,
                                AffineConstraint<A> without) {
        if (coefs.size() <= 1) {
            // A form naming one position is answered by the ends and by nothing else, because the
            // ends *are* this step at one position, run until they stop moving or until the rounds
            // run out. Taking one more here would be one round past whatever the closure was
            // allowed, and where the rounds do run out that showed: a chain longer than the budget
            // left the range of a position with no bound while the same position asked as a form
            // went one link further and found one. Two answers about one position, and the budget
            // bounding neither.
            return fromTheEnds(coefs, constant);
        }
        ExactCut ranges = fromTheRanges(coefs, constant);
        ExactCut best = withTheDifference(coefs, constant, ranges);
        // What a premise naming none of the form's positions leaves is the form and the premise
        // side by side. Where the form weighs two positions or more, that residual has three or
        // more, so the ranges are its only route — see passesOver for when they bound it no lower
        // than what is already held.
        boolean residualsAreRangedOnly = weighed(coefs) >= 2;
        for (Premise<A> each : premises()) {
            if (each.rule().equals(without)) {
                continue;
            }
            AffineConstraint.HalfSpace<A> premise = each.half();
            if (residualsAreRangedOnly && namesNoneOf(premise, coefs) && passesOver(each, ranges)) {
                continue;
            }
            // A model's own decimals can put this premise's bound, or one of its own
            // coefficients, far enough apart in scale from what it is being merged with that the
            // exact arithmetic cannot hold the sum. Where that happens this premise composes no
            // route this round — the same as a premise this form does not name — which costs a
            // tighter bound this route might have found and claims nothing this route did not.
            Map<A, ExactRatio> without1 = withoutThe(premise, coefs);
            ExactRatio residualConstant =
                    without1 == null ? null : constant.plus(premise.bound().at()).orNull();
            ExactCut residual = residualConstant == null ? null
                    : fromTheEnds(without1, residualConstant);
            if (residual != null) {
                // The form reaches the sum only where the residual reaches its own end and the
                // premise reaches its bound.
                best = ExactCut.tighterUpper(best, new ExactCut(residual.at(),
                        residual.inclusive() && premise.bound().inclusive()));
            }
        }
        return best;
    }

    /** How many of {@code coefs}' positions carry a weight. */
    private static <A> int weighed(Map<A, ExactRatio> coefs) {
        int weighed = 0;
        for (ExactRatio weight : coefs.values()) {
            if (!weight.isZero()) {
                weighed++;
            }
        }
        return weighed;
    }

    /** Whether {@code premise}'s sum names none of the positions {@code coefs} holds, weighed or
     *  not — a position held at nought is still one a merge would combine. */
    private static <A> boolean namesNoneOf(AffineConstraint.HalfSpace<A> premise,
                                           Map<A, ExactRatio> coefs) {
        for (A position : coefs.keySet()) {
            if (premise.form().coefs().containsKey(position)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether a premise naming none of a form of two weighed positions or more can be passed over:
     * whether the residual it leaves is bounded, by the ranges alone, no lower than {@code ranges},
     * the ranges' bound on the form, which is no lower than what is already held.
     *
     * <p>The ranges bound the residual at their bound on the form plus their bound on
     * {@code bound - Σ w·x}, the premise's own room. Where an end that room needs is missing, the
     * residual is bounded nowhere and so tightens nothing. Where the room is above nought, the
     * residual is bounded above {@code ranges}. Anything else — the room at or below nought, or a sum
     * the exact arithmetic could not hold — is merged in the way every premise is, so what is
     * answered here decides how much work is done and never what comes of it.
     */
    private boolean passesOver(Premise<A> each, ExactCut ranges) {
        return switch (each.room(this)) {
            case NOT_REACHED -> true;
            case ABOVE_NOUGHT -> ranges != null;
            case NOT_SETTLED -> false;
        };
    }

    /** Where {@code half}'s room — {@code bound - Σ w·x} at the most the ranges let it come to —
     *  stands. */
    private Room roomOf(AffineConstraint.HalfSpace<A> half) {
        Map<A, ExactRatio> negated = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> each : half.form().entriesIn(order)) {
            ExactRatio weight = each.getValue().negated();
            ExactCut end = weight.signum() > 0 ? ends.mostOf(each.getKey())
                    : ends.leastOf(each.getKey());
            if (end == null) {
                return Room.NOT_REACHED;
            }
            negated.put(each.getKey(), weight);
        }
        ExactCut room = Reach.of(negated, half.bound().at(), this::rangeOf).most();
        return room != null && room.at().signum() > 0 ? Room.ABOVE_NOUGHT : Room.NOT_SETTLED;
    }

    /** Where a premise's room stands against the ranges of this round. */
    private enum Room {
        /** An end the room needs is missing, so the ranges bound it nowhere. */
        NOT_REACHED,
        /** The ranges bound it above nought. */
        ABOVE_NOUGHT,
        /** Neither of those is known: at or below nought, or a sum the exact arithmetic could not
         *  hold. */
        NOT_SETTLED
    }

    /**
     * Every half-space of every rule, in the order the rules are held.
     *
     * <p>Once for the round rather than once for every form asked in it: an equality states its two
     * half-spaces afresh each time it is asked for them.
     *
     * <p>Worked out on the first ask and kept. What is kept is a function of what this was handed,
     * so two threads that both work it out work out the same list.
     */
    private List<Premise<A>> premises() {
        List<Premise<A>> read = premises;
        if (read == null) {
            List<Premise<A>> out = new ArrayList<>();
            for (AffineConstraint<A> rule : rules) {
                for (AffineConstraint.HalfSpace<A> half : rule.halfSpaces()) {
                    out.add(new Premise<>(rule, half));
                }
            }
            read = List.copyOf(out);
            premises = read;
        }
        return read;
    }

    /**
     * One half-space of a rule, and where its room stands once a form has asked.
     *
     * <p>The room is the premise's and the ranges', and not the form's, so it is worked out the
     * first time a form naming none of the premise asks and kept for the round. Two threads that
     * both work it out work out the same answer.
     */
    private static final class Premise<A> {

        private final AffineConstraint<A> rule;
        private final AffineConstraint.HalfSpace<A> half;
        private Room room;

        Premise(AffineConstraint<A> rule, AffineConstraint.HalfSpace<A> half) {
            this.rule = rule;
            this.half = half;
        }

        AffineConstraint<A> rule() {
            return rule;
        }

        AffineConstraint.HalfSpace<A> half() {
            return half;
        }

        Room room(FormReach<A> round) {
            Room read = room;
            if (read == null) {
                read = round.roomOf(half);
                room = read;
            }
            return read;
        }
    }

    /** {@code coefs} with {@code premise}'s form taken off it, which is what is left to bound once
     *  the premise has been used — or {@code null} where a coefficient the merge combines is one the
     *  exact arithmetic cannot sum. */
    private Map<A, ExactRatio> withoutThe(AffineConstraint.HalfSpace<A> premise,
                                          Map<A, ExactRatio> coefs) {
        Map<A, ExactRatio> left = new LinkedHashMap<>(coefs);
        // The premise walked in the one order its positions decide. What comes of the merge is the
        // same whichever order it is taken in, and the walk is what would let the next change here
        // start depending on one the premise does not hold.
        boolean[] everyMergeWasComposed = {true};
        premise.form().entriesIn(order).forEach(each -> left.merge(each.getKey(),
                each.getValue().negated(), (a, b) -> {
                    ExactAnswer<ExactRatio> sum = a.plus(b);
                    if (sum instanceof ExactAnswer.Held<ExactRatio> held) {
                        return held.value();
                    }
                    everyMergeWasComposed[0] = false;
                    return a;
                }));
        if (!everyMergeWasComposed[0]) {
            return null;
        }
        left.values().removeIf(ExactRatio::isZero);
        return left;
    }

    /** What the ends and the closed differences leave the form, which is where every route starts. */
    private ExactCut fromTheEnds(Map<A, ExactRatio> coefs, ExactRatio constant) {
        if (coefs.isEmpty()) {
            return ExactCut.inclusive(constant);
        }
        return withTheDifference(coefs, constant, fromTheRanges(coefs, constant));
    }

    /** What the ends leave the form, each position read at its own end. */
    private ExactCut fromTheRanges(Map<A, ExactRatio> coefs, ExactRatio constant) {
        return Reach.of(coefs, constant, this::rangeOf).most();
    }

    private Reach rangeOf(A position) {
        return Reach.between(ends.leastOf(position), ends.mostOf(position));
    }

    /** {@code best}, tightened by the closed differences where the form is the difference of two
     *  positions. */
    private ExactCut withTheDifference(Map<A, ExactRatio> coefs, ExactRatio constant,
                                       ExactCut fromTheRanges) {
        ExactCut best = fromTheRanges;
        Apart<A> apart = difference(coefs);
        if (apart != null) {
            ExactCut held = differences.differenceBound(apart.above(), apart.below());
            // Where the difference and the constant are too far apart in scale for the exact
            // arithmetic to sum, this route bounds nothing this round rather than composing a value
            // it cannot hold.
            ExactRatio at = held == null ? null
                    : held.at().times(apart.by()).flatMap(scaled -> scaled.plus(constant)).orNull();
            if (at != null) {
                best = ExactCut.tighterUpper(best, new ExactCut(at, held.inclusive()));
            }
        }
        return best;
    }

    /**
     * The two positions of {@code k·(a - b)} and the {@code k}, or null where the form is not that.
     *
     * <p>Any {@code k} and not only one. A form asked as {@code 2a - 2b} is the difference
     * {@code a - b} twice over, and the closed differences bound it at twice what they bound that —
     * so recognising the shape only when it is spelled with ones is the same trap
     * {@link CanonicalForm} removed from the rules, one level down in the reading.
     */
    private static <A> Apart<A> difference(Map<A, ExactRatio> coefs) {
        if (coefs.size() != 2) {
            return null;
        }
        // Which of the two is taken away from the other is read off the sign of what each weighs,
        // and not off which of them the mapping hands over first. The two readings agree wherever
        // the weights really are one of each sign, which is the only shape this answers about — and
        // one of them is an answer about the form while the other is about the walk.
        A above = null;
        A below = null;
        ExactRatio by = null;
        for (Map.Entry<A, ExactRatio> each : coefs.entrySet()) {
            if (each.getValue().signum() > 0) {
                above = each.getKey();
                by = each.getValue();
            } else {
                below = each.getKey();
            }
        }
        if (above == null || below == null
                || !coefs.get(above).equals(coefs.get(below).negated())) {
            return null;
        }
        return new Apart<>(above, below, by);
    }

    /** {@code by · (above - below)}, with {@code by} positive. */
    private record Apart<A>(A above, A below, ExactRatio by) {}
}
