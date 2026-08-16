package souther.compiler.values;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

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
 */
public record AdmissibleValues<A>(Map<A, ValueSet> values, Map<A, UnreadReason> unread,
                                  boolean dropped, boolean nothing) {

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
    }

    /** Nothing read and nothing missed, which is what a reading starts from. */
    public static <A> AdmissibleValues<A> top() {
        return new AdmissibleValues<>(Map.of(), Map.of(), false, false);
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
                : new AdmissibleValues<>(Map.of(), unread, dropped, true);
    }

    /** One position said to admit {@code set}, and nothing missed. */
    public static <A> AdmissibleValues<A> at(A atom, ValueSet set) {
        return new AdmissibleValues<>(Map.of(atom, set), Map.of(), false, false);
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
        return new AdmissibleValues<>(Map.of(), spoiled, true, false);
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
                dropped || other.dropped, nothing || other.nothing);
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
                    dropped || other.dropped, true);
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
        return new AdmissibleValues<>(out, spoiled, dropped || other.dropped, false);
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
