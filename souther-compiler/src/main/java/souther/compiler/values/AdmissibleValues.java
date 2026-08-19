package souther.compiler.values;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.BinaryOperator;

/**
 * Which values each position may hold, over all the rules a reading took in.
 *
 * <p>A state and not a set. A rule is written about a whole value and may name several of its
 * positions, and the connectives join whole readings rather than the answer at one position — so
 * what a conjunction and a disjunction are applied to is this, and the arithmetic at one position
 * is {@link ValueSet}.
 *
 * <p><b>Bottom is a state and not always a position.</b> The rules leave nothing where some position
 * is left no value — and also where every alternative of a choice is one nobody can take, which is
 * not a fact about any one position. The second is {@code nothing}: a choice between two impossible
 * alternatives that fail at different positions admits nothing, and neither position is one the
 * choice leaves empty.
 *
 * <p><b>A position not held here is at {@link ValueSet#ANY}.</b> That is what makes the two
 * connectives what they are below, and it is the one thing to hold on to while reading them.
 *
 * <pre>
 *     meet             the keys of both, each side missing one standing at ANY
 *     join             the keys of both, each side missing one standing at ANY
 * </pre>
 *
 * <p>Which reads the same and is not: joining at a key one side does not hold is joining with ANY,
 * and that is ANY — so a join keeps only what both sides spoke about, and a meet keeps everything
 * either did. {@code value == "A" || something-this-cannot-read} has to come out saying nothing
 * about {@code value}, and a join written as a merge of the two maps says {@code "A"}.
 *
 * <h2>What the reading knows about itself</h2>
 *
 * <p>Beside the values, which positions this can speak for. A reading that could not take a rule in
 * leaves the values wider than the rules are, which is the safe direction for refusing a
 * declaration — nothing is admitted that the rules exclude — and the wrong direction for saying
 * that a model divides a position into these classes and no others. The two answers are different
 * questions and are kept apart: {@link #at} says which values, {@link #speaksFor} says whether that
 * is the whole of what the rules leave.
 *
 * <p>What a position holds is answered from two sides. {@link #at} is an upper approximation and
 * {@link #guaranteedAt} a lower one, and between them sits what the rules truly leave:
 *
 * <pre>
 *     guaranteedAt(p)   &#8838;   what is truly admitted at p   &#8838;   at(p)
 * </pre>
 *
 * <p>The lower one is what a choice needs. An alternative that admits every value at a position
 * settles it however little was read beside it, and a reading holding only "something went unread"
 * has thrown away what it would take to know that — which is why the two ends are carried and not
 * a flag standing for their difference.
 *
 * <p>Two things spoil it, and the second is the one that is easy to miss.
 *
 * <p>A rule this could not read spoils the positions it names, and what stopped it travels with
 * them ({@link UnreadReason}). It cannot spoil a position it does not name: nothing here relates
 * one position to another, so a rule that narrows a position names it — a rule relating two of them
 * names both, and is itself a rule this cannot read.
 *
 * <p>A rule this could not read spoils, under a disjunction, every position the other branch spoke
 * about, whether or not it names them. {@code value == "A" || opaque()} leaves {@code value} at ANY
 * because a value satisfying the second branch is under no obligation from the first — and ANY
 * arrived at that way is not the ANY of a position nothing was written about. Without this a
 * position would be reported as one the model draws no distinction at, when what happened is that
 * this reading could not follow the distinction the model draws.
 *
 * <p>Unless the alternatives already cover the position, which is the one thing that stops it.
 * {@code (value == "A" || value /= "A") || opaque()} leaves nothing for the unread branch to take
 * back: the two that were read admit every value between them, and a choice one of whose
 * alternatives admits every value at a position admits every value at it. That is what
 * {@link #guaranteedAt} is carried for, and holding "something went unread" alone would answer the
 * same clause two ways depending on where its brackets fell.
 */
public record AdmissibleValues<A>(Map<A, ValueSet> values, Map<A, UnreadReason> unread,
                                  boolean dropped, boolean nothing,
                                  Map<A, ValueSet> guaranteed, ValueSet defaultGuaranteed) {

    /**
     * @param values  what each position admits. A position at {@link ValueSet#ANY} is left out, so
     *                that what is held is what was said
     * @param unread  the positions this reading cannot speak for, each with what stopped it. Why
     *                and not only which: two of these are lifted by different work and reported
     *                differently, and a reader handed the positions alone would have to go back to
     *                the rules to find out which it was
     * @param dropped whether a rule was left unread anywhere in this reading, which is what a
     *                disjunction needs in order to know that a branch widened it. What stopped that
     *                rule is not carried: a position the other branch spoke about is spoiled by
     *                there having been an alternative it could not read, and not by whatever the
     *                rule in that alternative was about
     * @param guaranteed which values each position is guaranteed to admit — read through
     *                {@link #guaranteedAt} rather than off this map, since a position guaranteed
     *                {@code defaultGuaranteed} is left out and what is held is what differs from it
     * @param defaultGuaranteed what a position this holds no guarantee for is guaranteed to admit.
     *                Not {@link #dropped} said another way: {@code value == 5} joined with a rule
     *                nothing could read has this at {@link ValueSet#ANY} and {@code dropped} set,
     *                because the alternative that was read guarantees every value at every position
     *                it says nothing about, while a rule of the choice did go unread
     */
    public AdmissibleValues {
        Map<A, ValueSet> said = new LinkedHashMap<>();
        values.forEach((atom, set) -> {
            if (!set.isAny()) {
                said.put(atom, set);
            }
        });
        // Kept in the order the positions were read, as {@link ValueSet} keeps its values: what is
        // written out of these has to come out the same on two runs of the compiler, and the
        // iteration order of an immutable copy does not.
        values = Collections.unmodifiableMap(said);
        unread = Collections.unmodifiableMap(new LinkedHashMap<>(unread));
        // A reading that admits nothing guarantees nothing, and at every position rather than at
        // the one that emptied: no value of it exists, so there is none to be counted on anywhere.
        // Settled here because every way of building one of these arrives at nothing differently —
        // a leaf left no value, two rules that cannot both hold, a caller that showed it from
        // outside — and a guarantee surviving any of them is a lower bound on the empty set.
        if (nothing || said.values().stream().anyMatch(ValueSet::isEmpty)) {
            guaranteed = Map.of();
            defaultGuaranteed = ValueSet.NONE;
        }
        Map<A, ValueSet> beyond = new LinkedHashMap<>();
        ValueSet otherwise = defaultGuaranteed;
        guaranteed.forEach((atom, set) -> {
            if (!set.equals(otherwise)) {
                beyond.put(atom, set);
            }
        });
        guaranteed = Collections.unmodifiableMap(beyond);
    }

    /**
     * Which values this reading can guarantee are admitted at {@code atom}, however much the rules
     * it could not read turn out to exclude.
     *
     * <p>A lower approximation where {@link #at} is an upper one, and equal to it at a position
     * this says that nothing left unread is why the answer is as wide as it is. It does not say the
     * answer is what the model leaves: a rule reaching across two positions is read here one
     * position at a time, so what is reported can be wider than the rules are with every rule read.
     *
     * <p><b>Carried through both connectives and read by one.</b> {@link #join} discharges an
     * unread rule at a position the alternatives already cover, because a choice one of whose
     * alternatives admits every value there admits every value there. {@link #meet} does not, and
     * this is not an omission: a rule stated beside others narrows rather than widens, so what an
     * unread one costs there is answered by the positions it names — which is what {@link #unread}
     * has held all along. The two connectives are dual in what they do to the values and are not
     * dual in this, and folding them together would report a conjunction short of its rules at
     * every position wherever a single clause of it went unread.
     */
    public ValueSet guaranteedAt(A atom) {
        return guaranteed.getOrDefault(atom, defaultGuaranteed);
    }

    /** Nothing read and nothing missed, which is what a reading starts from. */
    public static <A> AdmissibleValues<A> top() {
        return new AdmissibleValues<>(Map.of(), Map.of(), false, false, Map.of(), ValueSet.ANY);
    }

    /**
     * This where it already admits nothing, and a state admitting nothing where it does not.
     *
     * <p>What a caller says when something outside this showed that nothing satisfies the rules —
     * another domain reading the same clause, say. Nothing is claimed about any position: what is
     * known is about the whole, and writing it at a position would name one the rules are fine with.
     */
    public AdmissibleValues<A> leavingNothing() {
        return isBottom() ? this
                : new AdmissibleValues<>(Map.of(), unread, dropped, true, Map.of(), ValueSet.NONE);
    }

    /** One position said to admit {@code set}, and nothing missed. */
    public static <A> AdmissibleValues<A> at(A atom, ValueSet set) {
        return new AdmissibleValues<>(Map.of(atom, set), Map.of(), false, false,
                Map.of(atom, set), ValueSet.ANY);
    }

    /**
     * A rule this could not read, which says nothing about any position and spoils the ones it
     * names.
     *
     * <p>{@code named} may be empty — a rule reaching no position this can name is still a rule that
     * was not read, and what that costs is settled where it is joined rather than here.
     */
    public static <A> AdmissibleValues<A> unreadable(Set<A> named, UnreadReason why) {
        Map<A, UnreadReason> spoiled = new LinkedHashMap<>();
        named.forEach(each -> spoiled.put(each, why));
        // Nothing is guaranteed anywhere, and at the positions it does not name as much as at the
        // ones it does: what a rule this has no word for admits is not known, so a choice offering
        // it as an alternative is offering nothing that can be counted on.
        return new AdmissibleValues<>(Map.of(), spoiled, true, false, Map.of(), ValueSet.NONE);
    }

    /** What {@code atom} may hold, everything being admitted where nothing was said. */
    public ValueSet at(A atom) {
        return values.getOrDefault(atom, ValueSet.ANY);
    }

    /**
     * Whether {@link #at} is the whole of what the rules leave {@code atom}, rather than a wider
     * answer this reading could not narrow.
     */
    public boolean speaksFor(A atom) {
        return !unread.containsKey(atom);
    }

    /** What stopped this reading from speaking for {@code atom}, or null where nothing did. */
    public UnreadReason whyUnread(A atom) {
        return unread.get(atom);
    }

    /** Whether nothing satisfies these rules, at a position or otherwise. */
    public boolean isBottom() {
        return nothing || values.values().stream().anyMatch(ValueSet::isEmpty);
    }

    /** Both readings holding at once. */
    public AdmissibleValues<A> meet(AdmissibleValues<A> other) {
        Map<A, ValueSet> out = new LinkedHashMap<>(values);
        other.values.forEach((atom, set) -> out.merge(atom, set, ValueSet::meet));
        return new AdmissibleValues<>(out, union(unread, other.unread),
                dropped || other.dropped, nothing || other.nothing,
                guaranteedBy(guaranteed, defaultGuaranteed,
                        other.guaranteed, other.defaultGuaranteed, ValueSet::meet),
                defaultGuaranteed.meet(other.defaultGuaranteed));
    }

    /**
     * Either reading holding.
     *
     * <p>Over the positions both spoke about, since a position one of them left open is one the two
     * of them together leave open. And over the positions the other spoke about, where this branch
     * had something it could not read: those are open too, and open because of the reading rather
     * than because of the model.
     */
    public AdmissibleValues<A> join(AdmissibleValues<A> other) {
        // An alternative nobody can take leaves the answer to the others. Both being that is a
        // different case: no side speaks for the other, and meeting them would state a conjunction
        // the alternatives never stood in. What the choice admits nothing at is what every
        // alternative admits nothing at, and where there is no such position the choice still
        // admits nothing.
        if (isBottom() && other.isBottom()) {
            Map<A, ValueSet> both = new LinkedHashMap<>();
            values.forEach((atom, set) -> {
                ValueSet there = other.values.get(atom);
                if (set.isEmpty() && there != null && there.isEmpty()) {
                    both.put(atom, set);
                }
            });
            return new AdmissibleValues<>(both, union(unread, other.unread),
                    dropped || other.dropped, true, Map.of(), ValueSet.NONE);
        }
        if (isBottom()) {
            return other;
        }
        if (other.isBottom()) {
            return this;
        }
        Map<A, ValueSet> out = new LinkedHashMap<>();
        values.forEach((atom, set) -> {
            ValueSet there = other.values.get(atom);
            if (there != null) {
                out.put(atom, set.join(there));
            }
        });
        // What the alternatives guarantee between them, which is what settles whether anything is
        // left for an unread rule to have widened.
        Map<A, ValueSet> covered = guaranteedBy(guaranteed, defaultGuaranteed,
                other.guaranteed, other.defaultGuaranteed, ValueSet::join);
        ValueSet coveredElsewhere = defaultGuaranteed.join(other.defaultGuaranteed);
        Map<A, UnreadReason> spoiled = union(unread, other.unread);
        // Spoiled by there having been an alternative this could not read, which is what happened
        // to them: a value satisfying that branch is under no obligation from this one. Not by what
        // the unread rule was about — a rule relating two other positions relates this one to
        // nothing, and lending its reason here would say that it did.
        if (other.dropped) {
            spoiled = spoiling(spoiled, values.keySet());
        }
        if (dropped) {
            spoiled = spoiling(spoiled, other.values.keySet());
        }
        // And struck where the alternatives already cover what is reported. ANY is the top of this
        // lattice, so a choice that reached it on the alternatives it could read cannot be widened
        // by one it could not — and a position whose reported set is met exactly by what is
        // guaranteed is one no unread rule is answerable for, wherever it came by its reason.
        Map<A, UnreadReason> standing = new LinkedHashMap<>();
        spoiled.forEach((atom, why) -> {
            if (!covered.getOrDefault(atom, coveredElsewhere)
                    .equals(out.getOrDefault(atom, ValueSet.ANY))) {
                standing.put(atom, why);
            }
        });
        return new AdmissibleValues<>(out, standing, dropped || other.dropped, false,
                covered, coveredElsewhere);
    }

    /** What both sides guarantee, at every position either of them holds a guarantee for, each
     *  side missing one standing at its own default. */
    private static <A> Map<A, ValueSet> guaranteedBy(Map<A, ValueSet> these, ValueSet theseElse,
                                                     Map<A, ValueSet> those, ValueSet thoseElse,
                                                     BinaryOperator<ValueSet> both) {
        Set<A> named = new LinkedHashSet<>(these.keySet());
        named.addAll(those.keySet());
        Map<A, ValueSet> out = new LinkedHashMap<>();
        named.forEach(each -> out.put(each, both.apply(these.getOrDefault(each, theseElse),
                those.getOrDefault(each, thoseElse))));
        return out;
    }

    /** The same, with {@code these} left open by an alternative — where nothing has spoiled them
     *  already. A reason already recorded for a position is a rule that named it, which is nearer
     *  than a branch that widened it from outside. */
    private static <A> Map<A, UnreadReason> spoiling(Map<A, UnreadReason> had, Set<A> these) {
        if (these.isEmpty()) {
            return had;
        }
        Map<A, UnreadReason> out = new LinkedHashMap<>(had);
        these.forEach(each -> out.putIfAbsent(each, UnreadReason.ALTERNATIVE_NOT_READ));
        return out;
    }

    private static <A> Map<A, UnreadReason> union(Map<A, UnreadReason> these,
                                                  Map<A, UnreadReason> those) {
        if (those.isEmpty()) {
            return these;
        }
        Map<A, UnreadReason> out = new LinkedHashMap<>(these);
        those.forEach(out::putIfAbsent);
        return out;
    }
}
