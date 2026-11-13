package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.atomic.LongAdder;
import java.util.function.Function;

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

    /** What the holes among the rules came to against an earlier reading: premises beside the rules,
     *  never among them, so a caller reducing {@link #rules} does not reduce a bound the hole it came
     *  from is being read to again. */
    private final Collection<AffineConstraint.HalfSpace<A>> derived;
    private final Box<A> ends;
    private final DifferenceBounds<A> differences;

    /** The one order a walk of a form's positions takes them in — see {@link CanonicalOrder}. */
    private final CanonicalOrder<A> order;

    /** A rule's form walked in {@link #order}: the same walk as {@link CanonicalForm#entriesIn},
     *  which a reader that keeps the walks of the forms it is asked about hands over. */
    private final Function<CanonicalForm<A>, List<Map.Entry<A, ExactRatio>>> walked;

    /** Every half-space of every rule, stated once for the round, and which of them name each
     *  position — see {@link #premises}. Null until the first form of two or more positions asks. */
    private Premises<A> premises;

    /** The places of the premises each rule gives, which a form read without one of the rules
     *  asks of it — see {@link #placesOf}. Null until such a form asks. Held as one immutable
     *  value, as {@link #premises} is, so that two threads that both work it out publish equal
     *  ones and neither reads one half built. */
    private Map<AffineConstraint<A>, List<Integer>> placesOfRule;

    private static final int[] NO_PLACES = {};

    /** The work this might start from, best first; see {@link #working}. */
    private List<RoundWork<A>> parentWorks = List.of();

    /** The work of {@link #parentWorks} that can be moved over, in the same order, once asked for
     *  ({@link #starts}). */
    private List<Start<A>> starts;

    /** Where the answers of {@link Rests} are left, or null; see {@link #working}. */
    private RoundWork<A> workOut;

    /** How many positions may have other ends than the work was done against for its answers to be
     *  moved to this reading's. A cost and not a condition on what comes back: moving an answer is
     *  one step for each position that moved, and past this many it is no cheaper than summing it
     *  again, so the reading is worked out in full. */
    private static final int MOST_MOVED = 1;

    /**
     * A round's work that can be moved to the ends this reading starts in, and the positions whose
     * ends are not the ones it was done against.
     */
    private record Start<P>(RoundWork<P> work, List<P> moved) {
    }

    /**
     * What a start left of one question, which is what is moved to this reading's ends.
     *
     * <p>Chosen for the question and not for the reading: a start can be moved over whatever it
     * holds, but it holds only the questions its round had room to keep, so which of the starts a
     * question is moved from is the first that kept it.
     */
    private record Carry<P>(Start<P> from, RoundWork.Candidates before) {
    }

    /**
     * How many premises this has merged into a form, and how many it has held against the ends, for
     * a test holding a premise the ends already hold to being passed over and to being held against
     * them once a round. Counts and nothing else: what any form comes to is the same either way.
     */
    private long merged;
    private long heldAgainstTheEnds;

    /**
     * How many times, over every reading, a premise has been looked at for a question: once for each
     * premise a question runs over, and once more for each sum taken of one, each answer moved from
     * the work before and each premise merged into a form — and once for each term of the question
     * and of the premise that a sum is first built over. What a question costs is the premises it
     * visits and what is done to each, so this is what a test holds to growing with the rules and
     * their width and not with the rules and the questions together. Counted rather than timed: that
     * is a shape and not a speed.
     */
    private static final LongAdder PREMISES_WORKED = new LongAdder();

    static long premisesWorked() {
        return PREMISES_WORKED.sum();
    }

    private FormReach(List<AffineConstraint<A>> rules,
                      Collection<AffineConstraint.HalfSpace<A>> derived, Box<A> ends,
                      DifferenceBounds<A> differences, CanonicalOrder<A> order,
                      Function<CanonicalForm<A>, List<Map.Entry<A, ExactRatio>>> walked) {
        this.rules = rules;
        this.derived = derived;
        this.ends = ends;
        this.differences = differences;
        this.order = order;
        this.walked = walked;
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
        return over(rules, ends, differences, order, form -> form.entriesIn(order));
    }

    /** The same, with {@code derived} beside the rules; see the overload that walks through a
     *  function. */
    static <A> FormReach<A> over(List<AffineConstraint<A>> rules,
                                 Collection<AffineConstraint.HalfSpace<A>> derived, Box<A> ends,
                                 DifferenceBounds<A> differences, CanonicalOrder<A> order) {
        return over(rules, derived, ends, differences, order, form -> form.entriesIn(order));
    }

    /**
     * The same, walking a rule's form through {@code walked} rather than sorting it each time it is
     * asked: the walk of a form is settled by the form and the order, and a reading is asked about
     * the same rules' forms for every form it is put.
     *
     * @param walked what {@link CanonicalForm#entriesIn} answers under {@code order}
     */
    static <A> FormReach<A> over(List<AffineConstraint<A>> rules, Box<A> ends,
                                 DifferenceBounds<A> differences, CanonicalOrder<A> order,
                                 Function<CanonicalForm<A>, List<Map.Entry<A, ExactRatio>>> walked) {
        return over(rules, List.of(), ends, differences, order, walked);
    }

    /**
     * The same, with the half-spaces the holes among {@code rules} came to read as premises beside
     * them.
     *
     * @param derived implied by the rules, so a premise like any other; not among {@link #rules}
     */
    static <A> FormReach<A> over(List<AffineConstraint<A>> rules,
                                 Collection<AffineConstraint.HalfSpace<A>> derived, Box<A> ends,
                                 DifferenceBounds<A> differences, CanonicalOrder<A> order,
                                 Function<CanonicalForm<A>, List<Map.Entry<A, ExactRatio>>> walked) {
        if (differences.holdsNothing()) {
            throw new IllegalStateException(
                    "nothing is left, so there is no reach to read; ask holdsNothing first");
        }
        return new FormReach<>(rules, derived, ends, differences, order, walked);
    }

    /**
     * This reading with {@code more} read as premises beside what it already reads.
     *
     * <p>A new value and not a change to this one: what a reading answers is a function of what it
     * was handed, and the index of premises it keeps is of those.
     */
    FormReach<A> alsoReading(Collection<AffineConstraint.HalfSpace<A>> more) {
        List<AffineConstraint.HalfSpace<A>> both = new ArrayList<>(derived);
        both.addAll(more);
        return new FormReach<>(rules, both, ends, differences, order, walked);
    }

    /** The premises read beside the rules; see {@link #derived}. */
    Collection<AffineConstraint.HalfSpace<A>> derived() {
        return derived;
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

    /** How many premises this has merged into a form — see {@link #merged}. */
    long premisesMerged() {
        return merged;
    }

    /** How many premises this has held against the ends — see {@link #merged}. */
    long premisesHeldAgainstTheEnds() {
        return heldAgainstTheEnds;
    }

    /**
     * How many premises this has moved from the work of the closure before rather than summed, for a
     * test holding a closure worked from another to having been. Counts and nothing else: what any
     * question comes to is the same either way.
     */
    long premisesCarried() {
        return carriedOver;
    }

    private long carriedOver;

    /**
     * How many times the sum of a premise taken off a question has been read for it, for a test
     * holding a premise that names no position of the question to being passed over or merged as it
     * always was and not summed for it. Counts and nothing else: what any question comes to is the
     * same either way.
     */
    long sumsTaken() {
        return sumsTaken;
    }

    private long sumsTaken;

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
     * The least the rest of {@code asking}'s own form comes to, read while {@code asking} is being
     * reduced — with {@code asking} itself left out of the rules — or null where nothing bounds it
     * below.
     *
     * <p>The least and nothing more, because a rule is reduced against the least its rest comes to
     * and nothing else ({@link AffineReduction}). The highest is a second walk over every premise,
     * and this is asked of every position of every rule in every round of a closure.
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
    ExactCut leastOfTheRestOf(AffineConstraint<A> asking, Map<A, ExactRatio> coefs,
                              ExactRatio constant) {
        Map<A, ExactRatio> ordered = inOrder(coefs);
        return least(ordered, constant, asking, namingAnyOf(ordered));
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
        if (weighsAPositionNothingReaches(coefs)) {
            return null;
        }
        Map<A, ExactRatio> ordered = inOrder(coefs);
        return highest(ordered, constant, null, namingAnyOf(ordered));
    }

    /**
     * Whether the form weighs a position that nothing here reaches on the side the form runs up on:
     * it has no end there and no premise names it.
     *
     * <p>Every route to a bound on the form goes through the ends or a premise, a difference being
     * one of the rules, and none of them holds that position. Whatever the others come to, the form
     * is as high as the position is let to be, so it is bounded by nothing above. Asked before the
     * form is put in order, which is the cost of a walk over its positions to come to the same
     * answer.
     */
    private boolean weighsAPositionNothingReaches(Map<A, ExactRatio> coefs) {
        for (Map.Entry<A, ExactRatio> each : coefs.entrySet()) {
            A position = each.getKey();
            int sign = each.getValue().signum();
            ExactCut end = sign > 0 ? ends.mostOf(position) : ends.leastOf(position);
            if (sign != 0 && end == null && !premises().naming().containsKey(position)) {
                return true;
            }
        }
        return false;
    }

    private Reach between(Map<A, ExactRatio> coefs, ExactRatio constant, AffineConstraint<A> without) {
        // The form and its negation name the same positions, so which premises name one of them is
        // asked once for the two.
        BitSet naming = namingAnyOf(coefs);
        return new Reach(least(coefs, constant, without, naming),
                highest(coefs, constant, without, naming));
    }

    /**
     * The least the form comes to: the highest its negation comes to, on the other side of nought.
     * Asked that way rather than derived a second time, so the two ends are one reading and cannot
     * come apart.
     */
    private ExactCut least(Map<A, ExactRatio> coefs, ExactRatio constant,
                           AffineConstraint<A> without, BitSet naming) {
        ExactCut flipped = highest(negated(coefs), constant.negated(), without, naming);
        return flipped == null ? null : new ExactCut(flipped.at().negated(), flipped.inclusive());
    }

    /**
     * What the rest of each position of one half-space of {@code asking} comes to, asked of this
     * reading with {@code asking} left out of the rules — the same answers as
     * {@link #leastOfTheRestOf} gives for each position's rest, worked out together.
     *
     * <p>The rests of one half-space differ from each other at one position each, so what a premise
     * leaves of all of them is one sum with one term changed. That sum is taken once for a premise
     * and kept for the positions asking, which is what keeps a rule over many positions from being
     * merged with each premise once for every position it names.
     */
    Rests rests(AffineConstraint<A> asking, AffineConstraint.HalfSpace<A> half) {
        return new Rests(asking, half);
    }

    /**
     * This reading, working what it asks out from the {@code parents} it can be moved over and
     * leaving what it works out in {@code out}.
     *
     * <p>Said once, before anything is asked, and only of a reading made from the rules and the ends
     * of a round's start: a reading made from this one ({@link #alsoReading}) reads premises this
     * does not hold, and has neither.
     *
     * <p>Work can be moved over where the rules it was done over are these rules without the ones
     * said after, and the ends it was done against are these ends but for at most
     * {@link #MOST_MOVED} positions. Which round of which closure that is does not matter to what
     * comes back, so a question is moved from the first of them that qualifies and kept it.
     *
     * @param parents the work of rounds over these rules or the rules before them, best first
     * @param out     where the answers to the questions of {@link Rests} are left, or null where
     *                none are kept
     */
    FormReach<A> working(List<RoundWork<A>> parents, RoundWork<A> out) {
        this.parentWorks = parents;
        this.workOut = out;
        return this;
    }

    /** The work this might start from that can be moved over, best first; worked out the first
     *  time it is asked for. */
    private List<Start<A>> starts() {
        if (starts == null) {
            List<Start<A>> out = new ArrayList<>(parentWorks.size());
            for (RoundWork<A> each : parentWorks) {
                if (each != null && each != workOut && each.precedes(rules)) {
                    List<A> apart = each.endsThatMoved(ends, MOST_MOVED);
                    if (apart != null) {
                        out.add(new Start<>(each, apart));
                    }
                }
            }
            starts = out;
        }
        return starts;
    }

    /**
     * What the first start that kept a question left of it, or null where none did.
     *
     * @param kept     what a round kept of the question, or null where it kept none
     * @param premises how many premises this reading holds, which the kept answer may not exceed
     */
    private Carry<A> carryOf(Function<RoundWork<A>, RoundWork.Candidates> kept, int premises) {
        for (Start<A> each : starts()) {
            RoundWork.Candidates held = kept.apply(each.work());
            if (held != null && held.places() == each.work().premises()
                    && held.places() <= premises) {
                return new Carry<>(each, held);
            }
        }
        return null;
    }

    /** The rests of the positions of one half-space; see {@link #rests}. */
    final class Rests {

        private final AffineConstraint<A> asking;
        private final AffineConstraint.HalfSpace<A> half;
        private final Map<A, ExactRatio> form;
        private final Map<Integer, Aggregate> aggregates = new HashMap<>();

        /** The places of the premises {@code asking} is, which a question leaves out. */
        private BitSet leftOut;

        /** The form's positions in the order they are walked in, once asked for. */
        private Map<A, ExactRatio> inOrderForm;

        private Map<A, ExactRatio> negatedForm;

        private int[] namedBy;

        private Rests(AffineConstraint<A> asking, AffineConstraint.HalfSpace<A> half) {
            this.asking = asking;
            this.half = half;
            this.form = half.form().coefs();
        }

        /** The least the half-space's form comes to without {@code atom}, or null where nothing
         *  bounds it below. */
        ExactCut leastOfTheRest(A atom) {
            // The rest of a position is the form's positions in the order they are walked in with
            // that position left out: an order is not changed by taking one away, and the form is
            // put in order once for all its positions and not once for each.
            if (inOrderForm == null) {
                inOrderForm = inOrder(form);
            }
            Map<A, ExactRatio> ordered = new LinkedHashMap<>(inOrderForm);
            ordered.remove(atom);
            Map<A, ExactRatio> coefs = negated(ordered);
            ExactRatio constant = ExactRatio.ZERO.negated();
            ExactCut best;
            if (coefs.size() <= 1) {
                // A rest of one position or none is answered by the ends and by nothing else, as
                // any form of one position is: see highest.
                best = fromTheEnds(coefs, constant);
            } else {
                ExactCut ranges = fromTheRanges(coefs, constant);
                best = withTheDifference(difference(coefs), constant, ranges);
                List<Premise<A>> all = premises().each();
                best = tightenedBy(best, ranges, candidatesOf(atom, coefs, all), all, coefs,
                        constant);
            }
            return best == null ? null : new ExactCut(best.at().negated(), best.inclusive());
        }

        /**
         * What each premise leaves of the rest of {@code atom}, whose negation is {@code coefs}; kept
         * for the closure after where this reading leaves work.
         *
         * <p>Where the closure before these rules left what its premises left of this question, a
         * premise it held is carried over to the ends this reading starts in
         * ({@link #carried}) and only the premises the added rules gave are summed.
         */
        private RoundWork.Candidates candidatesOf(A atom, Map<A, ExactRatio> coefs,
                                                    List<Premise<A>> all) {
            RoundWork.Candidates out = new RoundWork.Candidates(all.size());
            Carry<A> carry = null;
            if (workOut != null) {
                workOut.premisesHeld(all.size());
                carry = carryOf(work -> work.of(asking, half.form(), atom), all.size());
            }
            BitSet left = leftOut();
            // The rest of the atom names what the form names but for the atom, so a premise names
            // a position of it where it names more of the form's positions than the atom is.
            int[] named = positionsNamedBy(all.size()).clone();
            List<Integer> ofAtom = premises().naming().getOrDefault(atom, List.of());
            for (int place : ofAtom) {
                named[place]--;
            }
            for (int place = 0; place < all.size(); place++) {
                if (left.get(place)) {
                    out.kinds[place] = RoundWork.ABSENT;
                    continue;
                }
                if (named[place] == 0) {
                    out.kinds[place] = RoundWork.UNNAMED;
                    continue;
                }
                Premise<A> premise = all.get(place);
                if (carry != null && place < carry.before().places()
                        && carry.before().kinds[place] != RoundWork.ABSENT
                        && carry.before().kinds[place] != RoundWork.UNNAMED) {
                    carried(carry, place, premise.half(), coefs, out);
                    continue;
                }
                aggregates.computeIfAbsent(place,
                        _ -> new Aggregate(negatedForm(), premise.half()))
                        .fill(atom, out, place);
            }
            if (workOut != null) {
                workOut.put(asking, half.form(), atom, out);
            }
            return out;
        }

        /** For each premise, by place, how many of the form's positions it names: once for the
         *  half-space, whichever position is left out of it. */
        private int[] positionsNamedBy(int premises) {
            if (namedBy == null) {
                namedBy = new int[premises];
                Map<A, List<Integer>> naming = premises().naming();
                for (A position : form.keySet()) {
                    for (int place : naming.getOrDefault(position, List.of())) {
                        namedBy[place]++;
                    }
                }
            }
            return namedBy;
        }

        /** The half-space's form negated: the question each premise is taken off, before the term of
         *  the position left out is replaced. */
        private Map<A, ExactRatio> negatedForm() {
            if (negatedForm == null) {
                negatedForm = negated(form);
            }
            return negatedForm;
        }

        private BitSet leftOut() {
            if (leftOut == null) {
                leftOut = new BitSet();
                for (int place : placesLeftOutWith(asking)) {
                    leftOut.set(place);
                }
            }
            return leftOut;
        }
    }

    /**
     * What {@code before} left of one premise, moved to the ends this reading starts in.
     *
     * <p>The residual is a sum of one end of each position it weighs, and a position whose ends are
     * not the ones it was summed against moves it by that weight times the difference of the end it
     * reads — and by one in the count of ends missing or not reached where the end itself came or
     * went or changed how it is reached. A premise left to be worked out where the arithmetic could
     * not hold the move.
     *
     * @param coefs the question the premise is taken off
     */
    private void carried(Carry<A> carry, int place,
                         AffineConstraint.HalfSpace<A> premise, Map<A, ExactRatio> coefs,
                         RoundWork.Candidates into) {
        RoundWork.Candidates before = carry.before();
        into.kinds[place] = before.kinds[place];
        if (before.kinds[place] != RoundWork.SUMMED) {
            return;
        }
        ExactRatio sum = before.sums[place];
        int missing = before.withoutEnd[place];
        int strict = before.notReached[place];
        for (A position : carry.from().moved()) {
            ExactRatio coef = coefs.getOrDefault(position, ExactRatio.ZERO);
            ExactRatio off = premise.form().coefs().get(position);
            if (off != null) {
                coef = coef.plus(off.negated()).orNull();
                if (coef == null) {
                    into.kinds[place] = RoundWork.ASKED;
                    return;
                }
            }
            if (coef.isZero()) {
                continue;
            }
            ExactCut was = carry.from().work().ends()
                    .endWeighedBy(position, coef.signum(), true);
            ExactCut now = ends.endWeighedBy(position, coef.signum(), true);
            if (was == null) {
                missing--;
            } else {
                strict -= was.inclusive() ? 0 : 1;
                ExactRatio term = coef.times(was.at()).orNull();
                sum = term == null ? null : sum.plus(term.negated()).orNull();
            }
            if (sum == null) {
                into.kinds[place] = RoundWork.ASKED;
                return;
            }
            if (now == null) {
                missing++;
            } else {
                strict += now.inclusive() ? 0 : 1;
                ExactRatio term = coef.times(now.at()).orNull();
                sum = term == null ? null : sum.plus(term).orNull();
            }
            if (sum == null) {
                into.kinds[place] = RoundWork.ASKED;
                return;
            }
        }
        into.sums[place] = sum;
        into.withoutEnd[place] = missing;
        into.notReached[place] = strict;
        carriedOver++;
        PREMISES_WORKED.increment();
        workOut.moved++;
    }

    /**
     * {@code best} tightened by every premise's candidate in {@code held}, which is what
     * {@link #highest} comes to: a premise passed over is one whose candidate cannot bound the form
     * lower than what is held already, so the lowest of all the candidates is the lowest of those
     * that were not.
     *
     * <p>A premise that names a position of the question has its candidate in {@code held}. One that
     * names none is passed over or merged as {@link #highest} does, against the ends as they are:
     * what it leaves is the question beside it, which holds nothing to move to other ends, and
     * which of those premises are passed over is decided from the ends and not by anything a
     * closure before could have kept.
     *
     * @param ranges what the ends alone leave {@code coefs}
     * @param coefs  the question the candidates are of
     */
    private ExactCut tightenedBy(ExactCut best, ExactCut ranges, RoundWork.Candidates held,
                                 List<Premise<A>> all, Map<A, ExactRatio> coefs,
                                 ExactRatio constant) {
        ExactCut out = best;
        int weighs = weighed(coefs);
        boolean residualsAreRangedOnly = weighs >= 2;
        int unbounded = residualsAreRangedOnly ? unboundedIn(coefs) : 0;
        PREMISES_WORKED.add(all.size());
        for (int place = 0; place < all.size(); place++) {
            ExactCut residual;
            switch (held.kinds[place]) {
                case RoundWork.ABSENT -> {
                    continue;
                }
                case RoundWork.UNNAMED -> {
                    Premise<A> each = all.get(place);
                    if ((residualsAreRangedOnly && passesOver(each, ranges))
                            || (ranges != null && heldAlready(each, coefs, weighs))
                            || (residualsAreRangedOnly
                                    && leavesNothing(each.half(), coefs, weighs, unbounded))) {
                        continue;
                    }
                    merged++;
                    PREMISES_WORKED.increment();
                    residual = fromTheEndsWithout(each.half(), coefs, constant);
                }
                case RoundWork.ASKED -> residual =
                        fromTheEndsWithout(all.get(place).half(), coefs, constant);
                default -> residual = held.withoutEnd[place] > 0 ? null
                        : new ExactCut(held.sums[place], held.notReached[place] == 0);
            }
            if (residual != null) {
                out = ExactCut.tighterUpper(out, new ExactCut(residual.at(),
                        residual.inclusive() && all.get(place).half().bound().inclusive()));
            }
        }
        return out;
    }

    /**
     * What the form {@code coefs} of {@code asking} runs between, read from what every premise
     * leaves of it and not from the premises that are not passed over — the answer {@link #of}
     * gives, worked from the work of an earlier round where there is one that can be moved over and
     * leaving its own for the round after.
     *
     * <p>A question of {@link Rests} is a form with one position taken off; this is the whole form,
     * asked for its two ends. They share how a premise's answer is moved and nothing of what they
     * ask, so each keeps its own questions in the work.
     */
    Reach ofKept(AffineConstraint<A> asking, Map<A, ExactRatio> coefs) {
        if (workOut == null || coefs.size() <= 1) {
            return of(coefs, ExactRatio.ZERO);
        }
        Map<A, ExactRatio> ordered = inOrder(coefs);
        ExactCut most = highestKept(asking, 0, ordered);
        ExactCut flipped = highestKept(asking, 1, negated(ordered));
        return new Reach(flipped == null ? null
                : new ExactCut(flipped.at().negated(), flipped.inclusive()), most);
    }

    /** The highest {@code coefs} comes to, which is one end of the form of {@link #ofKept}. */
    private ExactCut highestKept(AffineConstraint<A> asking, int direction,
                                 Map<A, ExactRatio> coefs) {
        ExactRatio constant = ExactRatio.ZERO;
        ExactCut ranges = fromTheRanges(coefs, constant);
        ExactCut best = withTheDifference(difference(coefs), constant, ranges);
        List<Premise<A>> all = premises().each();
        workOut.premisesHeld(all.size());
        RoundWork.Candidates held = new RoundWork.Candidates(all.size());
        Carry<A> carry = carryOf(work -> work.whole(asking, direction), all.size());
        BitSet naming = namingAnyOf(coefs);
        for (int place = 0; place < all.size(); place++) {
            if (!naming.get(place)) {
                held.kinds[place] = RoundWork.UNNAMED;
                continue;
            }
            AffineConstraint.HalfSpace<A> premise = all.get(place).half();
            if (carry != null && place < carry.before().places()
                    && carry.before().kinds[place] != RoundWork.ABSENT
                    && carry.before().kinds[place] != RoundWork.UNNAMED) {
                carried(carry, place, premise, coefs, held);
            } else {
                new Aggregate(coefs, premise).fillWhole(held, place);
            }
        }
        workOut.putWhole(asking, direction, held);
        return tightenedBy(best, ranges, held, all, coefs, constant);
    }

    /**
     * What the ends leave the question with a premise's form taken off it and its bound added, as a
     * sum over every position either names — the residual of {@link #fromTheEndsWithout}, kept as
     * the sum, how many of its ends are missing and how many are not reached so that one position's
     * term can be replaced.
     *
     * <p>Not kept where the exact arithmetic could not hold a term or a partial sum, and not
     * decided where the residual weighs two positions, which the closed differences may bound lower
     * than the ends do: both are answered by {@link #fromTheEndsWithout} itself, so what comes back
     * is what it would have said.
     */
    private final class Aggregate {

        private final AffineConstraint.HalfSpace<A> premise;
        private final Map<A, ExactRatio> question;
        private boolean held = true;
        private ExactRatio sum;
        private int withoutEnd;
        private int notReached;
        private int weighed;

        Aggregate(Map<A, ExactRatio> question, AffineConstraint.HalfSpace<A> premise) {
            PREMISES_WORKED.add(question.size() + premise.form().coefs().size());
            this.premise = premise;
            this.question = question;
            sum = ExactRatio.ZERO.plus(premise.bound().at()).orNull();
            if (sum == null) {
                held = false;
                return;
            }
            for (Map.Entry<A, ExactRatio> each : question.entrySet()) {
                ExactRatio off = premise.form().coefs().get(each.getKey());
                ExactRatio weight = each.getValue();
                if (off != null) {
                    weight = weight.plus(off.negated()).orNull();
                    if (weight == null) {
                        held = false;
                        return;
                    }
                }
                add(each.getKey(), weight);
            }
            for (Map.Entry<A, ExactRatio> each : premise.form().coefs().entrySet()) {
                if (!question.containsKey(each.getKey())) {
                    add(each.getKey(), each.getValue().negated());
                }
            }
        }

        private void add(A position, ExactRatio weight) {
            if (!held || weight.isZero()) {
                return;
            }
            weighed++;
            ExactCut end = ends.endWeighedBy(position, weight.signum(), true);
            if (end == null) {
                withoutEnd++;
                return;
            }
            if (!end.inclusive()) {
                notReached++;
            }
            ExactRatio term = weight.times(end.at()).orNull();
            sum = term == null ? null : sum.plus(term).orNull();
            if (sum == null) {
                held = false;
            }
        }

        /**
         * Writes what the residual of the whole question comes to into {@code into} at
         * {@code place}, with no position's term replaced, or {@link RoundWork#ASKED} where the sum is
         * not one this decides.
         */
        void fillWhole(RoundWork.Candidates into, int place) {
            sumsTaken++;
            PREMISES_WORKED.increment();
            if (!held || weighed == 2) {
                into.kinds[place] = RoundWork.ASKED;
                return;
            }
            into.kinds[place] = RoundWork.SUMMED;
            into.sums[place] = sum;
            into.withoutEnd[place] = withoutEnd;
            into.notReached[place] = notReached;
        }

        /**
         * Writes what the residual comes to into {@code into} at {@code place} with the term of
         * {@code atom} replaced by what the premise alone leaves of it — the residual of the
         * question without that position: the sum, how many of its ends are missing and how many are
         * not reached, or {@link RoundWork#ASKED} where the sum is not one this decides.
         */
        void fill(A atom, RoundWork.Candidates into, int place) {
            sumsTaken++;
            PREMISES_WORKED.increment();
            into.kinds[place] = RoundWork.ASKED;
            if (!held) {
                return;
            }
            ExactRatio off = premise.form().coefs().get(atom);
            ExactRatio was = question.getOrDefault(atom, ExactRatio.ZERO);
            if (off != null) {
                was = was.plus(off.negated()).orNull();
                if (was == null) {
                    return;
                }
            }
            ExactRatio now = off == null ? ExactRatio.ZERO : off.negated();
            int size = this.weighed - (was.isZero() ? 0 : 1) + (now.isZero() ? 0 : 1);
            if (size == 2) {
                return;
            }
            int missing = withoutEnd;
            int strict = notReached;
            ExactRatio total = sum;
            if (!was.isZero()) {
                ExactCut end = ends.endWeighedBy(atom, was.signum(), true);
                if (end == null) {
                    missing--;
                } else {
                    strict -= end.inclusive() ? 0 : 1;
                    ExactRatio term = was.times(end.at()).orNull();
                    total = term == null ? null : total.plus(term.negated()).orNull();
                    if (total == null) {
                        return;
                    }
                }
            }
            if (!now.isZero()) {
                ExactCut end = ends.endWeighedBy(atom, now.signum(), true);
                if (end == null) {
                    missing++;
                } else {
                    strict += end.inclusive() ? 0 : 1;
                    ExactRatio term = now.times(end.at()).orNull();
                    total = term == null ? null : total.plus(term).orNull();
                    if (total == null) {
                        return;
                    }
                }
            }
            into.kinds[place] = RoundWork.SUMMED;
            into.sums[place] = total;
            into.withoutEnd[place] = missing;
            into.notReached[place] = strict;
        }
    }

    private static <A> Map<A, ExactRatio> negated(Map<A, ExactRatio> coefs) {
        Map<A, ExactRatio> out = new LinkedHashMap<>();
        coefs.forEach((position, weight) -> out.put(position, weight.negated()));
        return out;
    }

    /**
     * @param naming which premises, by their place in {@link #premises}, name one of
     *               {@code coefs}' positions ({@link #namingAnyOf}); null for a form of one
     *               position or none, which asks no premise
     */
    private ExactCut highest(Map<A, ExactRatio> coefs, ExactRatio constant,
                                AffineConstraint<A> without, BitSet naming) {
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
        ExactCut best = withTheDifference(difference(coefs), constant, ranges);
        // What a premise naming none of the form's positions leaves is the form and the premise
        // side by side. Where the form weighs two positions or more, that residual has three or
        // more, so the ranges are its only route — see passesOver for when they bound it no lower
        // than what is already held.
        int weighs = weighed(coefs);
        boolean residualsAreRangedOnly = weighs >= 2;
        int unbounded = residualsAreRangedOnly ? unboundedIn(coefs) : 0;
        int[] left = without == null ? NO_PLACES : placesLeftOutWith(without);
        PREMISES_WORKED.add(premises().each().size());
        for (Premise<A> each : premises().each()) {
            if (isAmong(left, each.place())) {
                continue;
            }
            AffineConstraint.HalfSpace<A> premise = each.half();
            if (residualsAreRangedOnly && !naming.get(each.place())
                    && passesOver(each, ranges)) {
                continue;
            }
            if (ranges != null && heldAlready(each, coefs, weighs)) {
                continue;
            }
            if (residualsAreRangedOnly && leavesNothing(premise, coefs, weighs, unbounded)) {
                continue;
            }
            merged++;
            PREMISES_WORKED.increment();
            // A model's own decimals can put this premise's bound, or one of its own
            // coefficients, far enough apart in scale from what it is being merged with that the
            // exact arithmetic cannot hold the sum. Where that happens this premise composes no
            // route this round — the same as a premise this form does not name — which costs a
            // tighter bound this route might have found and claims nothing this route did not.
            ExactCut residual = fromTheEndsWithout(premise, coefs, constant);
            if (residual != null) {
                // The form reaches the sum only where the residual reaches its own end and the
                // premise reaches its bound.
                best = ExactCut.tighterUpper(best, new ExactCut(residual.at(),
                        residual.inclusive() && premise.bound().inclusive()));
            }
        }
        return best;
    }

    /**
     * Whether the residual {@code premise} leaves {@code coefs} is bounded nowhere above, read off
     * the signs of the weights the merge leaves and which ends the positions have.
     *
     * <p>A residual weighing three positions or more is bounded by the ranges alone
     * ({@link #fromTheEnds}), and the ranges bound nothing where one position the residual weighs
     * has no end the way its weight runs it up. Such a premise tightens nothing, and merging it is
     * a map built and a sum taken over every position of the form. Where the form's positions have
     * no ends, as the bounds an {@code Int} puts on each partial sum of a long addition have none,
     * that is most of the premises over it.
     *
     * <p>A residual of fewer than three, or one every position of which has its end, is merged the
     * way every premise is, so what is answered here decides how much work is done and never what
     * comes of it.
     *
     * @param unbounded how many of {@code coefs}' weighed positions have no end the way their
     *                  weight runs them up ({@link #unboundedIn})
     */
    private boolean leavesNothing(AffineConstraint.HalfSpace<A> premise, Map<A, ExactRatio> coefs,
                                  int weighs, int unbounded) {
        int weighsAfter = weighs;
        int unboundedAfter = unbounded;
        // Which of the premise's positions the merge leaves weighed, and which way, is read off the
        // order of the two weights and needs no sum of them.
        for (Map.Entry<A, ExactRatio> each : premise.form().coefs().entrySet()) {
            ExactRatio was = coefs.getOrDefault(each.getKey(), ExactRatio.ZERO);
            int left = was.compareTo(each.getValue());
            if (!was.isZero() && left == 0) {
                weighsAfter--;
            } else if (was.isZero() && left != 0) {
                weighsAfter++;
            }
            // The position's range is read once for both weights: it is two lookups of the ends,
            // and this is asked of every position of every premise a form is held against.
            Reach range = rangeOf(each.getKey());
            unboundedAfter += (runsWithoutEnd(range, left) ? 1 : 0)
                    - (runsWithoutEnd(range, was.signum()) ? 1 : 0);
        }
        return weighsAfter >= 3 && unboundedAfter > 0;
    }

    /** How many of {@code coefs}' weighed positions have no end the way their weight runs them
     *  up. */
    private int unboundedIn(Map<A, ExactRatio> coefs) {
        int unbounded = 0;
        for (Map.Entry<A, ExactRatio> each : coefs.entrySet()) {
            int sign = each.getValue().signum();
            if (sign != 0 && ends.endWeighedBy(each.getKey(), sign, true) == null) {
                unbounded++;
            }
        }
        return unbounded;
    }

    /** Whether a position whose ends are {@code range}, weighed with the sign {@code sign}, has no
     *  end the way that weight runs it up — never where it is weighed nought. */
    private static boolean runsWithoutEnd(Reach range, int sign) {
        return sign != 0 && range.endWeighedBy(sign, true) == null;
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

    /**
     * Which premises, by their place in {@link #premises}, name one of the positions {@code coefs}
     * holds, weighed or not — a position held at nought is still one a merge would combine. Null for
     * a form of one position or none, which {@link #highest} answers without a premise.
     *
     * <p>Made for the one form and let go after it, and no longer than the round has premises.
     */
    private BitSet namingAnyOf(Map<A, ExactRatio> coefs) {
        if (coefs.size() <= 1) {
            return null;
        }
        Map<A, List<Integer>> naming = premises().naming();
        BitSet out = new BitSet();
        for (A position : coefs.keySet()) {
            for (int place : naming.getOrDefault(position, List.of())) {
                out.set(place);
            }
        }
        return out;
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
        for (Map.Entry<A, ExactRatio> each : walked.apply(half.form())) {
            ExactRatio weight = each.getValue().negated();
            ExactCut end = weight.signum() > 0 ? ends.mostOf(each.getKey())
                    : ends.leastOf(each.getKey());
            if (end == null) {
                return Room.NOT_REACHED;
            }
            negated.put(each.getKey(), weight);
        }
        ExactCut room = Reach.mostOf(negated, half.bound().at(), ends::endWeighedBy);
        return room != null && room.at().signum() > 0 ? Room.ABOVE_NOUGHT : Room.NOT_SETTLED;
    }

    /**
     * Whether {@code each} is a bound on one position that the ends already hold at least as
     * tightly, in a way that leaves the form no route through it below the ranges' bound on the
     * form — so passing it over changes nothing that comes back.
     *
     * <p>Say the premise is {@code x <= b} with the ends holding {@code x} at most at {@code m}, no
     * looser than {@code b}, and the form weighs {@code x} by {@code c}. Taken off, it leaves
     * {@code x} weighed by {@code c - 1} and the bound {@code b} added. Where {@code c} is one or
     * more the residual reads {@code x} at {@code m} as the form does, and {@code (c - 1)·m + b} is
     * no less than {@code c·m}. Where {@code c} is below one the residual reads {@code x} at its
     * least, {@code l}, and comes to {@code (1 - c)·(m - l) + (b - m)} or more above the form, which
     * is not below it where the ends leave {@code x} a value. Where the two come to one value,
     * {@code b} is {@code m}, and a premise no looser than an end that is reached is reached too, so
     * the residual is not the strict one of the two. {@code -x <= b} is the same on the other side.
     *
     * <p>All of that is the ranges. A residual that is the difference of two positions is also
     * bounded by the closed differences, which can hold it lower than any range does, so a premise
     * leaving one of those is merged in like any other — and a residual of three positions or more
     * is not one, which is every residual of a form weighing four.
     *
     * @param weighs how many positions the form weighs
     */
    private boolean heldAlready(Premise<A> each, Map<A, ExactRatio> coefs, int weighs) {
        HeldEnd<A> held = each.heldEnd(this);
        if (held == null) {
            return false;
        }
        if (!held.holdsAValue()) {
            ExactRatio weighed = coefs.get(held.at());
            if (weighed == null || (held.above() ? weighed.compareTo(ExactRatio.ONE) < 0
                    : weighed.compareTo(MINUS_ONE) > 0)) {
                return false;
            }
        }
        return weighs >= 4 || !leavesADifference(coefs, held.at(),
                held.above() ? ExactRatio.ONE : MINUS_ONE);
    }

    private static final ExactRatio MINUS_ONE = ExactRatio.ONE.negated();

    /**
     * {@code half} as a bound on one position the ends hold at least as tightly, or null where it is
     * not one — which is the premise's and the ends', and no form's.
     */
    private HeldEnd<A> heldEndOf(AffineConstraint.HalfSpace<A> half) {
        heldAgainstTheEnds++;
        if (half.form().coefs().size() != 1) {
            return null;
        }
        A at = null;
        ExactRatio weight = null;
        for (Map.Entry<A, ExactRatio> each : walked.apply(half.form())) {
            at = each.getKey();
            weight = each.getValue();
        }
        boolean above = ExactRatio.ONE.equals(weight);
        if (!above && !MINUS_ONE.equals(weight)) {
            return null;
        }
        ExactCut least = ends.leastOf(at);
        ExactCut most = ends.mostOf(at);
        ExactCut bound = half.bound();
        boolean noLooser = above
                ? most != null && noLooserThan(most.at().compareTo(bound.at()), most, bound)
                : least != null
                        && noLooserThan(bound.at().negated().compareTo(least.at()), least, bound);
        if (!noLooser) {
            return null;
        }
        int apart = least == null || most == null ? -1 : least.at().compareTo(most.at());
        return new HeldEnd<>(at, above,
                apart < 0 ? least != null : apart == 0 && least.inclusive() && most.inclusive());
    }

    /**
     * A premise bounding {@code at} that the ends hold at least as tightly, on the upper side where
     * {@code above}, and whether the ends leave {@code at} a value.
     */
    private record HeldEnd<A>(A at, boolean above, boolean holdsAValue) {}

    /**
     * Whether an end is no looser than a premise's bound, given {@code order} — negative where the
     * end is inside the bound, nought where the two are at one value.
     */
    private static boolean noLooserThan(int order, ExactCut end, ExactCut bound) {
        return order < 0 || (order == 0 && (!end.inclusive() || bound.inclusive()));
    }

    /** Whether {@code coefs} with {@code weight} taken off {@code at} is the difference of two
     *  positions, or a sum the exact arithmetic cannot hold — either way one to merge in. */
    private static <A> boolean leavesADifference(Map<A, ExactRatio> coefs, A at,
                                                 ExactRatio weight) {
        ExactRatio left = coefs.containsKey(at)
                ? coefs.get(at).minus(weight).orNull() : weight.negated();
        if (left == null) {
            return true;
        }
        int weighs = left.isZero() ? 0 : 1;
        ExactRatio up = left.signum() > 0 ? left : null;
        ExactRatio down = left.signum() < 0 ? left : null;
        for (Map.Entry<A, ExactRatio> each : coefs.entrySet()) {
            if (each.getKey().equals(at) || each.getValue().isZero()) {
                continue;
            }
            weighs++;
            if (each.getValue().signum() > 0) {
                up = each.getValue();
            } else {
                down = each.getValue();
            }
        }
        return weighs == 2 && up != null && down != null && up.compareTo(down.negated()) == 0;
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
     * Every half-space of every rule, in the order the rules are held, and which of them name each
     * position.
     *
     * <p>Once for the round rather than once for every form asked in it: an equality states its two
     * half-spaces afresh each time it is asked for them, and which premises a form names is the
     * same question for every form that holds one position.
     *
     * <p>Worked out on the first ask and kept, the two in one value so that no thread reads one
     * without the other. What is kept is a function of what this was handed, so two threads that
     * both work it out work out the same.
     */
    private Premises<A> premises() {
        Premises<A> read = premises;
        if (read == null) {
            List<Premise<A>> out = new ArrayList<>();
            Map<A, List<Integer>> naming = new HashMap<>();
            for (AffineConstraint<A> rule : rules) {
                for (AffineConstraint.HalfSpace<A> half : rule.halfSpaces()) {
                    addPremise(rule, half, out, naming);
                }
            }
            for (AffineConstraint.HalfSpace<A> half : derived) {
                addPremise(half, half, out, naming);
            }
            // Each position holds the places of the premises that name it and no more, so the
            // index holds as many places as the premises name positions: one set of bits per
            // position would be as long as the last place that names it, which over positions
            // each named once is the square of the round.
            Map<A, List<Integer>> places = new HashMap<>();
            naming.forEach((position, named) -> places.put(position, List.copyOf(named)));
            read = new Premises<>(List.copyOf(out), Map.copyOf(places));
            premises = read;
        }
        return read;
    }

    /**
     * The places of the premises {@code rule} gives, or none where this holds no rule equal to it.
     *
     * <p>Asked once for the rule left out and not once for every premise: a form read without a
     * rule asks it at each of the premises a round holds, and holding each against the rule is a
     * comparison of two constraints as many times as there are premises. Which premises a rule
     * gives is the same for every form asked in the round, so it is worked out the first time a form
     * asks and kept, as one immutable value. Two threads that both work it out work out the same.
     */
    private List<Integer> placesOf(AffineConstraint<A> rule) {
        Map<AffineConstraint<A>, List<Integer>> read = placesOfRule;
        if (read == null) {
            Map<AffineConstraint<A>, List<Integer>> given = new HashMap<>();
            for (Premise<A> each : premises().each()) {
                given.computeIfAbsent(each.rule(), _ -> new ArrayList<>()).add(each.place());
            }
            given.replaceAll((_, places) -> List.copyOf(places));
            read = Map.copyOf(given);
            placesOfRule = read;
        }
        return read.getOrDefault(rule, List.of());
    }

    /**
     * {@link #placesOf} as a fresh array, which a form read without {@code rule} holds each premise
     * against as it goes: the ends of a walk over the premises, where a premise is held against
     * them as many times as there are premises, and a number is not made of each.
     *
     * <p>Its own method, and one that is handed no form. What a form read without a rule skips is
     * a set of places of premises, which has no order of the form's in it; a method that holds the
     * form's coefficients and takes a list by its position is one the rule that keeps a form's
     * order out of answers finds, whatever the list is of.
     */
    private int[] placesLeftOutWith(AffineConstraint<A> rule) {
        return placesOf(rule).stream().mapToInt(Integer::intValue).toArray();
    }

    private static boolean isAmong(int[] places, int place) {
        for (int each : places) {
            if (each == place) {
                return true;
            }
        }
        return false;
    }

    private void addPremise(AffineConstraint<A> rule, AffineConstraint.HalfSpace<A> half,
                            List<Premise<A>> out, Map<A, List<Integer>> naming) {
        Premise<A> premise = new Premise<>(rule, half, out.size());
        for (Map.Entry<A, ExactRatio> weighed : walked.apply(half.form())) {
            naming.computeIfAbsent(weighed.getKey(), _ -> new ArrayList<>())
                    .add(premise.place());
        }
        out.add(premise);
    }

    /** {@link #premises}: each premise, and the places of the premises naming each position
     *  ({@link Premise#place}). */
    private record Premises<A>(List<Premise<A>> each, Map<A, List<Integer>> naming) {}

    /**
     * One half-space of a rule, and where its room stands once a form has asked.
     *
     * <p>The room is the premise's and the ranges', and not the form's, so it is worked out the
     * first time a form naming none of the premise asks and kept for the round. So is whether it is
     * a bound the ends already hold ({@link #heldEndOf}). Two threads that both work either out
     * work out the same answer.
     */
    private static final class Premise<A> {

        private final AffineConstraint<A> rule;
        private final AffineConstraint.HalfSpace<A> half;

        /** Which premise of the round this is, in the order the rules are held: what the index
         *  of the premises naming each position is by. */
        private final int place;
        private Room room;

        /** {@link #heldEndOf}'s answer, empty where it is not such a bound, and null until asked. */
        private Optional<HeldEnd<A>> held;

        Premise(AffineConstraint<A> rule, AffineConstraint.HalfSpace<A> half, int place) {
            this.rule = rule;
            this.half = half;
            this.place = place;
        }

        int place() {
            return place;
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

        HeldEnd<A> heldEnd(FormReach<A> round) {
            Optional<HeldEnd<A>> read = held;
            if (read == null) {
                read = Optional.ofNullable(round.heldEndOf(half));
                held = read;
            }
            return read.orElse(null);
        }
    }

    /**
     * What the ends and the closed differences leave {@code coefs·position + constant} once
     * {@code premise}'s form is taken off it and its bound added — what is left to bound once the
     * premise has been used. Null where a coefficient the merge combines, or the bound it adds, is
     * one the exact arithmetic cannot sum.
     *
     * <p>The residual is added up as it is made and not held in a map: it is asked of once for each
     * premise a form is merged with, and is let go after. It is taken in the order a map copied from
     * {@code coefs} and merged with the premise's form, walked in the one order its positions
     * decide, iterates in — the positions of {@code coefs} where they were, then those only the
     * premise names, in the premise's order — because a sum is exact and can fail part of the way,
     * and whether it does turns on which terms were added before it. A position weighed nought, in
     * {@code coefs} or by what the merge leaves, is no term.
     */
    ExactCut fromTheEndsWithout(AffineConstraint.HalfSpace<A> premise, Map<A, ExactRatio> coefs,
                                ExactRatio constant) {
        List<Map.Entry<A, ExactRatio>> taken = walked.apply(premise.form());
        Map<A, ExactRatio> takenAt = taken.size() > FEW_TAKEN ? indexed(taken) : null;
        OrderedTerms<A> left = new OrderedTerms<>(coefs.size() + taken.size());
        for (Map.Entry<A, ExactRatio> each : coefs.entrySet()) {
            ExactRatio weight = each.getValue();
            ExactRatio off = weightTaken(taken, takenAt, each.getKey());
            if (off != null) {
                if (!(weight.plus(off.negated()) instanceof ExactAnswer.Held<ExactRatio> sum)) {
                    return null;
                }
                weight = sum.value();
            }
            left.addUnlessNought(each.getKey(), weight);
        }
        for (Map.Entry<A, ExactRatio> each : taken) {
            if (!coefs.containsKey(each.getKey())) {
                left.addUnlessNought(each.getKey(), each.getValue().negated());
            }
        }
        ExactRatio residualConstant = constant.plus(premise.bound().at()).orNull();
        if (residualConstant == null) {
            return null;
        }
        if (left.size() == 0) {
            return ExactCut.inclusive(residualConstant);
        }
        ExactCut fromTheRanges = Reach.mostOfTerms(left, residualConstant, ends::endWeighedBy);
        Apart<A> apart = left.size() == 2 ? apartOf(left) : null;
        return withTheDifference(apart, residualConstant, fromTheRanges);
    }

    /** How many positions a premise names before looking them up one by one costs more than
     *  indexing them. */
    private static final int FEW_TAKEN = 8;

    private static <A> Map<A, ExactRatio> indexed(List<Map.Entry<A, ExactRatio>> taken) {
        Map<A, ExactRatio> out = HashMap.newHashMap(taken.size());
        taken.forEach(each -> out.put(each.getKey(), each.getValue()));
        return out;
    }

    /** What the premise weighs {@code position} by, or null where it does not name it. */
    private static <A> ExactRatio weightTaken(List<Map.Entry<A, ExactRatio>> taken,
                                              Map<A, ExactRatio> takenAt, A position) {
        if (takenAt != null) {
            return takenAt.get(position);
        }
        for (Map.Entry<A, ExactRatio> each : taken) {
            if (each.getKey().equals(position)) {
                return each.getValue();
            }
        }
        return null;
    }

    /** What the ends and the closed differences leave the form, which is where every route starts. */
    ExactCut fromTheEnds(Map<A, ExactRatio> coefs, ExactRatio constant) {
        if (coefs.isEmpty()) {
            return ExactCut.inclusive(constant);
        }
        return withTheDifference(difference(coefs), constant, fromTheRanges(coefs, constant));
    }

    /** What the ends leave the form, each position read at its own end. The highest alone, which
     *  is every route's question here. */
    private ExactCut fromTheRanges(Map<A, ExactRatio> coefs, ExactRatio constant) {
        return Reach.mostOf(coefs, constant, ends::endWeighedBy);
    }

    private Reach rangeOf(A position) {
        return Reach.between(ends.leastOf(position), ends.mostOf(position));
    }

    /** {@code best}, tightened by the closed differences where the form is the difference of two
     *  positions. */
    private ExactCut withTheDifference(Apart<A> apart, ExactRatio constant,
                                       ExactCut fromTheRanges) {
        ExactCut best = fromTheRanges;
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
        return coefs.size() == 2 ? apartOf(coefs.entrySet()) : null;
    }

    /** {@link #difference} of a form of the two positions {@code terms} hands over. */
    private static <A> Apart<A> apartOf(Iterable<? extends Map.Entry<A, ExactRatio>> terms) {
        // Which of the two is taken away from the other is read off the sign of what each weighs,
        // and not off which of them the mapping hands over first. The two readings agree wherever
        // the weights really are one of each sign, which is the only shape this answers about — and
        // one of them is an answer about the form while the other is about the walk.
        A above = null;
        A below = null;
        ExactRatio by = null;
        ExactRatio belowWeighs = null;
        for (Map.Entry<A, ExactRatio> each : terms) {
            if (each.getValue().signum() > 0) {
                above = each.getKey();
                by = each.getValue();
            } else {
                below = each.getKey();
                belowWeighs = each.getValue();
            }
        }
        if (above == null || below == null || !by.equals(belowWeighs.negated())) {
            return null;
        }
        return new Apart<>(above, below, by);
    }

    /** {@code by · (above - below)}, with {@code by} positive. */
    private record Apart<A>(A above, A below, ExactRatio by) {}
}
