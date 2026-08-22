package souther.compiler.values;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.Function;

/**
 * Several readings of admissible values, held together and not multiplied together.
 *
 * <p>An {@link AdmissibleValues} is a union of products, so a conjunction of two of them distributes
 * — every alternative of one against every alternative of the other. That is right where the two
 * speak about the same positions, and it is what a declaration's own clauses are read with, under a
 * budget counted before any of them is read. Two readings that share no position are a different
 * case: no pair is ever dropped, every product is the two maps put side by side, and the {@code m ×
 * n} alternatives say exactly what the pair {@code (m, n)} says. Expanding there buys nothing and
 * costs the product.
 *
 * <p>Which is not a corner case once readings of several values are said together. Ten parameters of
 * a record whose clauses leave two alternatives are a thousand and twenty-four alternatives, and the
 * budget that admitted each reading was counted per declaration and has nothing to say about their
 * conjunction.
 *
 * <p><b>The factors have pairwise disjoint vocabularies.</b> That is the invariant, and it is what
 * makes the answers exact rather than approximate:
 *
 * <pre>
 *     isBottom()   any factor holding nothing, since the rest constrain none of its positions
 *     at(subject)  the one factor that names it, since no other says anything about it
 * </pre>
 *
 * <p>So a conjunction is kept factored only where keeping it factored loses nothing. Where two
 * factors do share a position, the exact conjunction is the product, and it is {@link
 * AdmissibleValues#meet} that works it out — this decides where that is needed and never what it
 * comes to.
 *
 * <p><b>What is not promised.</b> Not that a conjunction is bounded. Two readings that name the same
 * position, each admitted under a budget of its own, still multiply when they are met, and nothing
 * here stops that: what is bounded is one declaration's reading, and a caller conjoining two of them
 * over one vocabulary is asking for their product. What is promised is that a conjunction pays the
 * product only where the positions actually meet.
 *
 * <p>No join. A choice between alternatives happens while one declaration is read, which is below
 * this and inside {@link AdmissibleValues}. A disjunction of two factored conjunctions would have to
 * expand them to be said at all, and nothing asks for one.
 */
public final class ConjoinedAdmissibleValues<A> {

    /** In the order the readings arrived. Nothing here answers with one of them, but what is written
     *  out of a compilation has to come out the same on two runs of it. */
    private final List<AdmissibleValues<A>> factors;
    /**
     * Which factor names each subject, worked out once.
     *
     * <p>Both the index the answers are read off and the thing that holds the invariant up: a
     * subject arriving from two factors is two readings that were called disjoint and are not, and
     * it is seen here rather than by a caller wondering why a position was answered from a reading
     * that says nothing about it. Built for every one of these, so a factoring that goes wrong is
     * refused where it is made and not where it is read.
     */
    private final Map<A, AdmissibleValues<A>> naming;

    private ConjoinedAdmissibleValues(List<AdmissibleValues<A>> factors) {
        this.factors = List.copyOf(factors);
        Map<A, AdmissibleValues<A>> named = new LinkedHashMap<>();
        for (AdmissibleValues<A> each : this.factors) {
            for (A subject : each.subjects()) {
                if (named.put(subject, each) != null) {
                    throw new IllegalStateException("`" + subject + "` is named by two of these"
                            + " readings, so they are not the disjoint factors this holds");
                }
            }
        }
        this.naming = Collections.unmodifiableMap(named);
    }

    /** Nothing read, so every position holds every value. */
    public static <A> ConjoinedAdmissibleValues<A> top() {
        return new ConjoinedAdmissibleValues<>(List.of());
    }

    /** One reading, which is a conjunction of one. */
    public static <A> ConjoinedAdmissibleValues<A> of(AdmissibleValues<A> read) {
        return new ConjoinedAdmissibleValues<>(List.of(read));
    }

    /**
     * The readings this holds, in the order they arrived.
     *
     * <p>Not public. How a conjunction is held apart is this type's own business — every question
     * anybody asks of it is asked of the conjunction and answered from whichever factor names the
     * subject — and a caller counting the factors would be reading a representation as though it
     * were an answer. What is here for is a test measuring that a conjunction of readings over
     * disjoint vocabularies is not multiplied into one.
     */
    List<AdmissibleValues<A>> factors() {
        return factors;
    }

    /**
     * How many readings have been taken into this.
     *
     * <p>A count of readings and not of anything they say. What it is for is a caller that takes a
     * reading in once and has to be able to say so — {@link
     * souther.compiler.check.ConstraintState#takingValuesRead} is written against nothing having
     * been taken in yet, and a second reading arriving there would replace the first without a word.
     */
    public int readingsTaken() {
        return factors.size();
    }

    /**
     * Whether nothing satisfies the readings together.
     *
     * <p>Any factor on its own. The others say nothing about the positions it names, so nothing they
     * hold can put a value back into a factor that has none — and a factor that holds nothing leaves
     * the conjunction nothing whatever the rest admit.
     */
    public boolean isBottom() {
        return factors.stream().anyMatch(AdmissibleValues::isBottom);
    }

    /**
     * Which values may stand at one subject.
     *
     * <p>Asked of the factor that names it and of no other. The rest do not name it, and a reading
     * that does not name a subject admits every value at it — so meeting their answers in would be
     * meeting with everything.
     */
    public ValueSet at(A subject) {
        AdmissibleValues<A> names = naming.get(subject);
        return names == null ? ValueSet.ANY : names.at(subject);
    }

    /**
     * Whether what is held at one subject is what the rules leave it, rather than something wider.
     *
     * <p>Asked of the factor that names it. A reading that does not name a subject did not widen
     * anything there — it holds every value at it exactly, having been told nothing — so a
     * conjunction no factor of which names the subject is exact at it.
     */
    public boolean projectionExactAt(A subject) {
        AdmissibleValues<A> names = naming.get(subject);
        return names == null || names.projectionExactAt(subject);
    }

    /**
     * What stopped a subject's rules from being read, or null where nothing did.
     *
     * <p>Asked of the factor that names it, for the same reason: a reading that never heard of a
     * subject has no rule about it that went unread.
     */
    public UnreadReason whyUnread(A subject) {
        AdmissibleValues<A> names = naming.get(subject);
        return names == null ? null : names.whyUnread(subject);
    }

    /** Every subject any factor names. */
    public Set<A> subjects() {
        return naming.keySet();
    }

    /**
     * Both conjunctions holding at once.
     *
     * <p>The factors of the two put together and then normalised: factors whose vocabularies meet
     * are one factor, and what that factor is is {@link AdmissibleValues#meet}'s to say.
     *
     * <p><b>Over connected components and not over pairs.</b> Merging two overlapping factors makes
     * a factor with both vocabularies, which may now meet a third that neither of them met — a
     * factor over {@code {a, b}} beside one over {@code {c}}, met with one over {@code {b, c}},
     * is one factor over all three. Merged pairwise in one pass, the result would hold two factors
     * that share {@code c}, and every answer that rests on the vocabularies being disjoint would be
     * answering from a factor that is not the only one naming its subject.
     */
    public ConjoinedAdmissibleValues<A> meet(ConjoinedAdmissibleValues<A> other) {
        if (other.factors.isEmpty()) {
            return this;
        }
        if (factors.isEmpty()) {
            return other;
        }
        List<AdmissibleValues<A>> both = new ArrayList<>(factors);
        both.addAll(other.factors);
        return new ConjoinedAdmissibleValues<>(byComponent(both));
    }

    /**
     * The same readings about the same subjects, under the names {@code naming} gives them.
     *
     * <p>Factor by factor, and the vocabularies stay disjoint because the naming names two subjects
     * two subjects — which is the caller's to hold to and is what
     * {@code souther.compiler.check.InjectiveRenaming} is.
     */
    public <B> ConjoinedAdmissibleValues<B> renamed(Function<A, B> naming) {
        List<AdmissibleValues<B>> out = new ArrayList<>(factors.size());
        factors.forEach(each -> out.add(each.renamed(naming)));
        return new ConjoinedAdmissibleValues<>(out);
    }

    /**
     * One factor per connected component of "these two name a subject in common".
     *
     * <p><b>Which factors are one is found by walking; the order they are met in is not.</b> The
     * walk reaches a component's members through whichever subject it happens to look at first, and
     * met as they are reached, a component of three would be folded in the order its vocabularies
     * were iterated. {@link AdmissibleValues#meet} does not answer the same either way — what stopped
     * a position's rules from being read is the first reason given for it, so two readings that
     * both went unread at one position are told apart by which of them was met first. Read off a
     * walk, that reason would be settled by which subject a factor's vocabulary happened to list
     * first rather than by which reading arrived first.
     *
     * <p>So the members are collected, and then the readings are folded in the order they arrived.
     * Connectivity decides who is met with whom; arrival decides in what order.
     */
    private static <A> List<AdmissibleValues<A>> byComponent(List<AdmissibleValues<A>> of) {
        List<Set<A>> vocabularies = new ArrayList<>(of.size());
        of.forEach(each -> vocabularies.add(each.subjects()));
        // Which factors name each subject, which is what says two of them are in one component
        // without every pair of them being compared.
        Map<A, List<Integer>> naming = new LinkedHashMap<>();
        for (int at = 0; at < of.size(); at++) {
            int here = at;
            vocabularies.get(at).forEach(
                    subject -> naming.computeIfAbsent(subject, _ -> new ArrayList<>()).add(here));
        }
        List<AdmissibleValues<A>> out = new ArrayList<>();
        boolean[] taken = new boolean[of.size()];
        for (int at = 0; at < of.size(); at++) {
            if (taken[at]) {
                continue;
            }
            // Every reading this one reaches, gathered before any of them is met.
            SortedSet<Integer> members = new TreeSet<>();
            taken[at] = true;
            members.add(at);
            Deque<Integer> reaching = new ArrayDeque<>();
            reaching.add(at);
            while (!reaching.isEmpty()) {
                for (A subject : vocabularies.get(reaching.remove())) {
                    for (int also : naming.getOrDefault(subject, List.of())) {
                        if (!taken[also]) {
                            taken[also] = true;
                            members.add(also);
                            reaching.add(also);
                        }
                    }
                }
            }
            // And then met in the order they arrived, which is the order they are held in.
            AdmissibleValues<A> component = null;
            for (int each : members) {
                component = component == null ? of.get(each) : component.meet(of.get(each));
            }
            out.add(component);
        }
        return out;
    }

    @Override
    public String toString() {
        return factors.isEmpty() ? "everything" : String.join(" and ", factors.stream()
                .map(Object::toString).toList());
    }
}
