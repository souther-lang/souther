package souther.compiler.values;

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
 * <p>A rule this could not read spoils the positions it names. It cannot spoil a position it does
 * not name: nothing here relates one position to another, so a rule that narrows a position names
 * it — a rule relating two of them names both, and is itself a rule this cannot read.
 *
 * <p>A rule this could not read spoils, under a disjunction, every position the other branch spoke
 * about, whether or not it names them. {@code value == "A" || opaque()} leaves {@code value} at ANY
 * because a value satisfying the second branch is under no obligation from the first — and ANY
 * arrived at that way is not the ANY of a position nothing was written about. Without this a
 * position would be reported as one the model draws no distinction at, when what happened is that
 * this reading could not follow the distinction the model draws.
 */
public record AdmissibleValues<A>(Map<A, ValueSet> values, Set<A> unread, boolean dropped) {

    /**
     * @param values  what each position admits. A position at {@link ValueSet#ANY} is left out, so
     *                that what is held is what was said
     * @param unread  the positions this reading cannot speak for
     * @param dropped whether any rule at all was left unread, which is what a disjunction needs in
     *                order to know that a branch widened it
     */
    public AdmissibleValues {
        Map<A, ValueSet> said = new LinkedHashMap<>();
        values.forEach((atom, set) -> {
            if (!set.isAny()) {
                said.put(atom, set);
            }
        });
        values = Map.copyOf(said);
        unread = Set.copyOf(unread);
    }

    /** Nothing read and nothing missed, which is what a reading starts from. */
    public static <A> AdmissibleValues<A> top() {
        return new AdmissibleValues<>(Map.of(), Set.of(), false);
    }

    /** One position said to admit {@code set}, and nothing missed. */
    public static <A> AdmissibleValues<A> at(A atom, ValueSet set) {
        return new AdmissibleValues<>(Map.of(atom, set), Set.of(), false);
    }

    /**
     * A rule this could not read, which says nothing about any position and spoils the ones it
     * names.
     *
     * <p>{@code named} may be empty — a rule reaching no position this can name is still a rule that
     * was not read, and what that costs is settled where it is joined rather than here.
     */
    public static <A> AdmissibleValues<A> unreadable(Set<A> named) {
        return new AdmissibleValues<>(Map.of(), named, true);
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
        return !unread.contains(atom);
    }

    /** Whether some position admits no value, so that nothing satisfies these rules. */
    public boolean isBottom() {
        return values.values().stream().anyMatch(ValueSet::isEmpty);
    }

    /** Both readings holding at once. */
    public AdmissibleValues<A> meet(AdmissibleValues<A> other) {
        Map<A, ValueSet> out = new LinkedHashMap<>(values);
        other.values.forEach((atom, set) -> out.merge(atom, set, ValueSet::meet));
        return new AdmissibleValues<>(out, union(unread, other.unread), dropped || other.dropped);
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
        Map<A, ValueSet> out = new LinkedHashMap<>();
        values.forEach((atom, set) -> {
            ValueSet there = other.values.get(atom);
            if (there != null) {
                out.put(atom, set.join(there));
            }
        });
        Set<A> spoiled = union(unread, other.unread);
        if (other.dropped) {
            spoiled = union(spoiled, values.keySet());
        }
        if (dropped) {
            spoiled = union(spoiled, other.values.keySet());
        }
        return new AdmissibleValues<>(out, spoiled, dropped || other.dropped);
    }

    private static <A> Set<A> union(Set<A> these, Set<A> those) {
        if (those.isEmpty()) {
            return these;
        }
        Set<A> out = new LinkedHashSet<>(these);
        out.addAll(those);
        return out;
    }
}
