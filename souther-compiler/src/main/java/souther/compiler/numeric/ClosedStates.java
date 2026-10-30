package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Function;

/**
 * Where a closure is worked out, and for how long one is kept to stand for the next question equal
 * to it.
 *
 * <p>A domain keeps what its own rules leave once it has been asked. What it cannot see is another
 * domain holding the same rules — and a reader that builds a domain per question builds that one
 * over and over, through different contexts that leave the numbers the same and through readings
 * made from one another. So the closure is asked of one of these, which a domain carries and lends
 * to every domain made from it.
 *
 * <p><b>What a closure is, is the arithmetic's to say; how long one is kept is the owner's.</b> Two
 * questions are one closure where they are equal ({@link ClosureQuestion}), and nothing here or in
 * the owner decides that. What the owner decides is the lifetime: it makes one of these where the
 * repetition it wants shared lives and drops it with whatever holds it. Everything else asks
 * {@link #NONE}, which keeps nothing, and is where a reader stays until somebody has measured a
 * repetition it owns.
 *
 * <p>A question is a part of the rules that names no position another part names, because that is
 * what one closure is: the rules together leave the product of what their parts leave
 * ({@link ClosedState}). So rules that differ from rules asked before in some of their parts are
 * lent the closure of every other part. Nothing here knows why two sets of rules share a part — a
 * search fixing one position and leaving the rest, or two contexts reading one declaration — and
 * nothing here needs to.
 *
 * <p>Carried and not part of what a domain is. Two domains holding the same rules are the same
 * domain whichever of these they carry; what differs is only whether working the rules out is done
 * again.
 *
 * <p>Asked from any thread a reading is asked from. A closure worked out twice by two threads that
 * met at one question is the same closure, so either may be the one kept.
 */
public final class ClosedStates {

    /** Nothing kept: every domain works out what its rules leave for itself. */
    public static final ClosedStates NONE = new ClosedStates(null, null, null, false);

    /**
     * Nothing kept, and every set of rules closed in one run rather than a part at a time
     * ({@link ClosedState#closedTogether}).
     *
     * <p>For a test holding what a domain answers over the product of its parts to what it answers
     * over the closure that product stands for — including the questions a domain is asked after
     * the closure, about forms over positions of two parts. Nothing else asks for this: the two are
     * one closure, and this one costs what the rules cost together.
     */
    static final ClosedStates IN_ONE_RUN = new ClosedStates(null, null, null, true);

    /** One closure per question, kept for as long as whatever holds this is held. */
    public static ClosedStates kept() {
        return new ClosedStates(new ConcurrentHashMap<>(), new ConcurrentHashMap<>(),
                new ConcurrentHashMap<>(), false);
    }

    private final Map<ClosureQuestion<?>, ClosedState<?>> answers;

    /**
     * Where each order puts each set of positions it has been asked about
     * ({@link ClosureQuestion#placesIn}).
     *
     * <p>Kept because putting a question to the table means stating it, and stating it means
     * sorting the positions its rules weigh — with a comparison that can be dear, once per question
     * asked and not once per closure worked out. The positions repeat far more than the rules do.
     *
     * <p>Keyed by the order as the object it is, which is not what makes two questions one: two
     * orders written apart that put the positions in the same places are two entries here and one
     * question at {@link #answers}. An entry missed is a sort done again and nothing else.
     */
    private final Map<CanonicalOrder<?>, Map<Set<?>, Map<?, Integer>>> places;

    /**
     * How each form has been walked in each order it has been asked of ({@link CanonicalForm#entriesIn}).
     *
     * <p>Kept for the reason {@link #places} is: the walk of a form is settled by the form and the
     * order alone, and the rules a reading is asked about are the same few forms for every form it is
     * put. Keyed by the order as the object it is, so an order written apart that walks alike is a
     * walk done again and nothing else. Null for a table that keeps nothing.
     */
    private final Map<CanonicalOrder<?>, Map<CanonicalForm<?>, List<?>>> walks;

    private final AtomicLong workedOut = new AtomicLong();

    private final AtomicLong walkedOut = new AtomicLong();

    private final AtomicLong asked = new AtomicLong();

    /** Whether the rules are closed in one run, which is {@link #IN_ONE_RUN} and nothing else. */
    private final boolean inOneRun;

    private ClosedStates(Map<ClosureQuestion<?>, ClosedState<?>> answers,
                         Map<CanonicalOrder<?>, Map<Set<?>, Map<?, Integer>>> places,
                         Map<CanonicalOrder<?>, Map<CanonicalForm<?>, List<?>>> walks,
                         boolean inOneRun) {
        this.answers = answers;
        this.places = places;
        this.walks = walks;
        this.inOneRun = inOneRun;
    }

    /**
     * How a form is walked under {@code order}: {@link CanonicalForm#entriesIn}, worked out once for
     * each form where this keeps what it is asked, and worked out each time where it does not.
     *
     * <p>A walk that is refused is refused each time it is asked, and nothing of it is kept.
     */
    <A> Function<CanonicalForm<A>, List<Map.Entry<A, ExactRatio>>> walksIn(
            CanonicalOrder<A> order) {
        if (walks == null) {
            return form -> form.entriesIn(order);
        }
        Map<CanonicalForm<?>, List<?>> kept = walks.computeIfAbsent(order,
                _ -> new ConcurrentHashMap<>());
        return form -> {
            // The cast holds because an entry is only ever put under the form it is the walk of, in
            // the order the table above is keyed by.
            @SuppressWarnings("unchecked")
            List<Map.Entry<A, ExactRatio>> had = (List<Map.Entry<A, ExactRatio>>) kept.get(form);
            if (had != null) {
                return had;
            }
            List<Map.Entry<A, ExactRatio>> made = form.entriesIn(order);
            walkedOut.incrementAndGet();
            kept.put(form, made);
            return made;
        };
    }

    /**
     * How many walks of a form this has worked out rather than lent, for a test holding a reader to
     * asking for the walk of a rule's form once however many readings are asked about it. Counted
     * for the same reason {@link #workedOut} is: that a walk asked again is not done again is a
     * shape and not a speed.
     */
    long walksWorkedOut() {
        return walkedOut.get();
    }

    /** What {@code rules} leave, spaced by {@code spacing} and walked in {@code order}. */
    <A> ClosedState<A> of(List<AffineConstraint<A>> rules, Function<A, Granularity> spacing,
                          CanonicalOrder<A> order) {
        return of(rules, spacing, order, null).state();
    }

    /**
     * The same, lent every part of {@code before} that the rules said after it do not reach.
     *
     * <p>For a domain made from another by saying more rules: the rules {@code before} was worked
     * out from come first among {@code rules}, in the same order, and what follows them reaches
     * some of its parts and not the others. A part it does not reach is the same question it was
     * ({@link ClosureQuestion}), so its closure is the one {@code before} already holds; a part it
     * does reach is a question of its own and is asked here as every question is. What comes back
     * is the closure {@code rules} put without anything lent, part for part — lending decides what
     * is worked out again and never what it comes to.
     *
     * @param before what a domain these rules were said onto worked out, or null where there is
     *               none to lend from
     */
    <A> Parted<A> of(List<AffineConstraint<A>> rules, Function<A, Granularity> spacing,
                     CanonicalOrder<A> order, Parted<A> before) {
        if (inOneRun) {
            return Parted.whole(ClosedState.closedTogether(rules, spacing, order));
        }
        // Nothing kept, so nothing to state: the question is what a kept closure is found by, and a
        // closure that is not kept is worked out from what it was handed, as it always was.
        if (answers == null) {
            return Parted.whole(ClosedState.of(rules, spacing, order));
        }
        Parted<A> lent = before == null ? null : before.followedBy(rules, this);
        if (lent == null) {
            lent = Parted.unread(ClosureQuestion.independentRules(rules), rules, this);
        }
        // Asked a part at a time. A question is one closure on its own, and two sets of rules that
        // differ only in some of their parts put the same question for every other part. A part
        // lent is lent only where its rules still put the question it was worked out for, which is
        // the question's to say.
        Function<Set<A>, Map<A, Integer>> placing = weighed -> placed(weighed, order);
        List<ClosureQuestion<A>> questions = new ArrayList<>(lent.parts.size());
        List<ClosedState<A>> closed = new ArrayList<>(lent.parts.size());
        boolean everyPartLent = true;
        for (int at = 0; at < lent.parts.size(); at++) {
            ClosureQuestion<A> had = lent.questions.get(at);
            if (had != null && had.isPutBy(spacing, order, placing)) {
                questions.add(had);
                closed.add(lent.closed.get(at));
                continue;
            }
            everyPartLent = false;
            ClosureQuestion<A> asked =
                    ClosureQuestion.of(lent.parts.get(at), spacing, order, placing);
            questions.add(asked);
            closed.add(of(asked));
        }
        if (everyPartLent && lent.complete) {
            return lent;
        }
        return new Parted<>(this, rules, lent.parts, questions, closed, lent.partOf, null, true);
    }

    /**
     * A closure worked out a part at a time, with the parts it was worked out from.
     *
     * <p>Held beside the domain it is the closure of, so that a domain made from that one by saying
     * more rules can be lent the parts those rules do not reach ({@link #of(List, Function,
     * CanonicalOrder, Parted)}). The parts are {@link ClosureQuestion#independentRules} of the
     * rules, in its order, and each closure is the one the question beside it puts.
     *
     * @param <A> what a position of the rules is
     */
    public static final class Parted<A> {

        /** Where the parts were asked, or null where nothing was parted. */
        private final ClosedStates owner;
        private final List<AffineConstraint<A>> rules;
        private final List<List<AffineConstraint<A>>> parts;

        /** The question each part put, or null for a part that has yet to put one. */
        private final List<ClosureQuestion<A>> questions;

        /** What each part's question leaves, beside it. */
        private final List<ClosedState<A>> closed;

        /** Which part weighs each position. */
        private final Map<A, Integer> partOf;

        /** The closures of the parts put together: worked out when asked for, since a question
         *  about the positions of one part is answered by that part's closure alone. */
        private volatile ClosedState<A> state;

        /** Whether every part has its closure, which is what a closure of all the rules is. */
        private final boolean complete;

        private Parted(ClosedStates owner, List<AffineConstraint<A>> rules,
                       List<List<AffineConstraint<A>>> parts, List<ClosureQuestion<A>> questions,
                       List<ClosedState<A>> closed, Map<A, Integer> partOf,
                       ClosedState<A> state, boolean complete) {
            this.owner = owner;
            this.rules = rules;
            this.parts = parts;
            this.questions = questions;
            this.closed = closed;
            this.partOf = Map.copyOf(partOf);
            this.state = state;
            this.complete = complete;
        }

        /** A closure worked out in one piece, with no parts to lend. */
        private static <A> Parted<A> whole(ClosedState<A> state) {
            return new Parted<>(null, List.of(), List.of(), List.of(), List.of(), Map.of(), state,
                    true);
        }

        /** {@code parts} of {@code rules}, none of them asked yet. */
        private static <A> Parted<A> unread(List<List<AffineConstraint<A>>> parts,
                                            List<AffineConstraint<A>> rules, ClosedStates owner) {
            Map<A, Integer> partOf = new HashMap<>();
            List<ClosureQuestion<A>> unasked = new ArrayList<>(parts.size());
            List<ClosedState<A>> unclosed = new ArrayList<>(parts.size());
            for (int at = 0; at < parts.size(); at++) {
                for (AffineConstraint<A> rule : parts.get(at)) {
                    putting(rule, at, partOf);
                }
                unasked.add(null);
                unclosed.add(null);
            }
            return new Parted<>(owner, rules, parts, unasked, unclosed, partOf, null, false);
        }

        /** What the rules leave. */
        public ClosedState<A> state() {
            ClosedState<A> had = state;
            if (had == null) {
                had = ClosedState.product(closed);
                state = had;
            }
            return had;
        }

        /**
         * Whether the rules leave nothing, which is whether any part does: parts share no position,
         * so one that leaves nothing leaves the rules together nothing, and none that does leaves
         * them a value apiece.
         */
        public boolean holdsNothing() {
            ClosedState<A> put = state;
            if (put != null) {
                return put.holdsNothing();
            }
            for (ClosedState<A> each : closed) {
                if (each.holdsNothing()) {
                    return true;
                }
            }
            return false;
        }

        /** Whether every part composed every bound it tried to, which is what the parts put
         *  together do — and nothing is left to compose where a part holds nothing. */
        public boolean everyBoundWasComposed() {
            ClosedState<A> put = state;
            if (put != null) {
                return put.everyBoundWasComposed();
            }
            boolean composed = true;
            for (ClosedState<A> each : closed) {
                if (each.holdsNothing()) {
                    return true;
                }
                composed &= each.everyBoundWasComposed();
            }
            return composed;
        }

        /**
         * What the part weighing {@code position} leaves, or null where no part does — which
         * includes a closure worked out in one piece, whose state is the only one there is.
         */
        public ClosedState<A> partWeighing(A position) {
            Integer at = partOf.get(position);
            return at == null || !complete ? null : closed.get(at);
        }

        /** The rules of the part weighing {@code position}; null where {@link #partWeighing} is. */
        public List<AffineConstraint<A>> rulesOfThePartWeighing(A position) {
            Integer at = partOf.get(position);
            return at == null || !complete ? null : parts.get(at);
        }

        /**
         * The parts of {@code more}, which these rules followed by others are, with the question and
         * the closure of each part the others do not reach — or null where this cannot say what the
         * parts are.
         *
         * <p>A rule said later joins the part of every position it weighs, and parts come in the
         * order of their first rule with each part's rules in the order they were said
         * ({@link ClosureQuestion#independentRules}). So a later rule weighing positions of one part
         * goes at the end of that part, and one weighing no position of any goes into a part after
         * all of these. A rule weighing positions of two parts joins them, and where the rules of
         * the two then go is a merge this does not make: it is null, and the parts are worked out
         * from the rules.
         *
         * <p>Null as well where {@code more} does not start with these rules, the very ones in the
         * same order, or is kept by another owner. Whether a part not reached still puts its
         * question under the spacing and the order {@code more} is closed with is asked of the
         * question, where the closure is asked for.
         */
        private Parted<A> followedBy(List<AffineConstraint<A>> more, ClosedStates asking) {
            if (owner != asking || more.size() < rules.size()) {
                return null;
            }
            for (int at = 0; at < rules.size(); at++) {
                if (more.get(at) != rules.get(at)) {
                    return null;
                }
            }
            if (more.size() == rules.size()) {
                return this;
            }
            Map<A, Integer> into = new HashMap<>(partOf);
            List<List<AffineConstraint<A>>> grown = new ArrayList<>(parts);
            List<ClosureQuestion<A>> asked = new ArrayList<>(questions);
            // Which parts hold a list of their own here, to be added to; the rest are this one's.
            BitSet ownList = new BitSet();
            for (int at = rules.size(); at < more.size(); at++) {
                AffineConstraint<A> rule = more.get(at);
                int part = partWeighedBy(rule, into);
                if (part == SEVERAL) {
                    return null;
                }
                if (part == NONE) {
                    part = grown.size();
                    grown.add(new ArrayList<>());
                    asked.add(null);
                } else if (!ownList.get(part)) {
                    grown.set(part, new ArrayList<>(grown.get(part)));
                    asked.set(part, null);
                }
                ownList.set(part);
                grown.get(part).add(rule);
                putting(rule, part, into);
            }
            List<List<AffineConstraint<A>>> parted = new ArrayList<>(grown.size());
            grown.forEach(each -> parted.add(List.copyOf(each)));
            List<ClosedState<A>> kept = new ArrayList<>(closed);
            while (kept.size() < asked.size()) {
                kept.add(null);
            }
            return new Parted<>(owner, more, parted, asked, kept, into, null, false);
        }

        /** What {@link #partWeighedBy} answers for a rule weighing no position of any part. */
        private static final int NONE = -1;

        /** What {@link #partWeighedBy} answers for a rule weighing positions of two parts. */
        private static final int SEVERAL = -2;

        /**
         * The one part {@code partOf} has the positions {@code rule} weighs in, {@link #NONE} where
         * it has none of them and {@link #SEVERAL} where they are in more than one — which of its
         * positions is taken first decides none of the three.
         */
        private static <A> int partWeighedBy(AffineConstraint<A> rule, Map<A, Integer> partOf) {
            int found = NONE;
            for (A position : rule.form().coefs().keySet()) {
                Integer its = partOf.get(position);
                if (its == null) {
                    continue;
                }
                if (found != NONE && found != its) {
                    return SEVERAL;
                }
                found = its;
            }
            return found;
        }

        /** {@code partOf} with every position {@code rule} weighs in {@code part}. */
        private static <A> void putting(AffineConstraint<A> rule, int part,
                                        Map<A, Integer> partOf) {
            for (A position : rule.form().coefs().keySet()) {
                partOf.put(position, part);
            }
        }
    }

    /** What {@code question} leaves, lent where it has been worked out before. */
    private <A> ClosedState<A> of(ClosureQuestion<A> question) {
        // The cast holds because an entry is only ever put under the question it answers, and a
        // question over positions of type A is answered by a closure over the same positions.
        asked.incrementAndGet();
        @SuppressWarnings("unchecked")
        ClosedState<A> had = (ClosedState<A>) answers.get(question);
        if (had != null) {
            return had;
        }
        // Worked out outside the table: a closure takes long enough that holding the table while
        // it is worked out would stop every other question waiting on it.
        ClosedState<A> made = ClosedState.of(question);
        workedOut.incrementAndGet();
        @SuppressWarnings("unchecked")
        ClosedState<A> raced = (ClosedState<A>) answers.putIfAbsent(question, made);
        return raced == null ? made : raced;
    }

    /** {@link ClosureQuestion#placesIn}, kept for the order and the positions it was asked of. */
    private <A> Map<A, Integer> placed(Set<A> positions, CanonicalOrder<A> order) {
        Map<Set<?>, Map<?, Integer>> under =
                places.computeIfAbsent(order, _ -> new ConcurrentHashMap<>());
        // The cast holds because an entry is only ever put under the positions it places.
        @SuppressWarnings("unchecked")
        Map<A, Integer> had = (Map<A, Integer>) under.get(positions);
        if (had != null) {
            return had;
        }
        Map<A, Integer> made = ClosureQuestion.placesIn(positions, order);
        @SuppressWarnings("unchecked")
        Map<A, Integer> raced = (Map<A, Integer>) under.putIfAbsent(Set.copyOf(positions), made);
        return raced == null ? made : raced;
    }

    /**
     * How many closures this has worked out rather than lent, for a test holding a reader to sharing
     * them. Nought for {@link #NONE}, which lends nothing and counts nothing.
     *
     * <p>Counted rather than timed: what is held is that a question asked again is not worked out
     * again, which is a shape and not a speed.
     */
    public long workedOut() {
        return workedOut.get();
    }

    /**
     * How many questions have been put to this, worked out or lent, for a test holding a closure
     * lent part by part to asking only for the parts the rules said since reach. Nought for
     * {@link #NONE}, which is asked nothing.
     */
    long questionsAsked() {
        return asked.get();
    }
}
