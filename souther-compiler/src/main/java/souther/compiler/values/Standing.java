package souther.compiler.values;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * What a reading could not take in, and which places each of those rules was written at.
 *
 * <p>One entry per rule the reading gave up on, holding every position that rule named. Which is
 * what the reading was handed: a rule about two positions is one rule, and a rule about one is one
 * rule, and either way what stopped the reading stopped it once. Filed as a map from position to
 * reasons, that fact came apart on the way in — a rule naming two places became two entries, and
 * the order the author wrote their rules in was recoverable only inside one place.
 *
 * <p><b>Only a producer's face is public.</b> What is here is read to answer whether a reading
 * speaks for what stands at a position and, where it does not, what stopped it
 * ({@link AdmissibleValues#speaksFor}, {@link AdmissibleValues#whyUnread}). Those two are one
 * derivation over the positions that hold one value, and a reader that could take the entries out
 * and look at one position would be answering the same question a second way — which is how a
 * position held as one value with another came to be reported as fully read. So a caller may make
 * one of these and add to it, and everything that reads it is here or beside it.
 *
 * @param <A> what a position is called
 */
public final class Standing<A> {

    /**
     * One rule this reading could not take in.
     *
     * <p>The positions together, because that is what was given up on: a rule relating two of them
     * is one rule, and telling a reader about it at one place and again at the other would be two
     * accounts of one thing.
     */
    private record Entry<A>(Set<A> positions, UnreadReason why) {

        private Entry {
            positions = Collections.unmodifiableSet(new LinkedHashSet<>(positions));
        }
    }

    /** In the order the reading met them, which is the order the rules were written. */
    private final List<Entry<A>> entries;

    private Standing(List<Entry<A>> entries) {
        this.entries = List.copyOf(entries);
    }

    /** Nothing was left standing, which is what a reading that read everything holds. */
    public static <A> Standing<A> nothing() {
        return new Standing<>(List.of());
    }

    /**
     * One rule that went unread, and the positions it named.
     *
     * <p>{@code named} may be empty — a rule reaching no position this reading can name is still a
     * rule it did not read, and what that costs is settled where it is joined.
     */
    public static <A> Standing<A> of(Set<A> named, UnreadReason why) {
        return new Standing<>(List.of(new Entry<>(named, why)));
    }

    /** Whether every rule the reading was handed was taken in. */
    public boolean isEmpty() {
        return entries.isEmpty();
    }

    /**
     * Both accounts, each rule kept and said once.
     *
     * <p>Appended and not chosen between, in the order the two were read. Two parts of one clause
     * stop a reading at one position in two ways and each is a rule of the author's to act on, so
     * dropping either would tell them about whichever part happened to be read first.
     */
    public Standing<A> and(Standing<A> other) {
        if (other.isEmpty()) {
            return this;
        }
        if (isEmpty()) {
            return other;
        }
        return new Standing<>(joined(entries, other.entries));
    }

    /** This, with one more rule that went unread at {@code positions}. */
    public Standing<A> alsoAt(Set<A> positions, UnreadReason why) {
        return and(Standing.of(positions, why));
    }

    /**
     * This, with {@code these} left open by an alternative nothing could read — where nothing has
     * spoiled them already.
     *
     * <p>The one rule for what an unread alternative does to the account beside it. A value
     * satisfying the branch nothing read is under no obligation from the branch that was read, so
     * the positions that branch reached are left open. The one place a reason is not added beside
     * the reasons already there: what this says is that the choice offered an alternative nothing
     * could read, which is one fact about the choice however many positions it reaches, and a
     * position whose own rules already stopped a reading is not stopped a second time by it. A
     * reason recorded there is a rule that named the position, which is nearer than a branch that
     * widened it from outside.
     */
    Standing<A> leftOpenAt(Set<A> these) {
        Set<A> open = new LinkedHashSet<>();
        these.forEach(position -> {
            if (at(position).isEmpty()) {
                open.add(position);
            }
        });
        return open.isEmpty() ? this : and(Standing.of(open, UnreadReason.ALTERNATIVE_NOT_READ));
    }

    /**
     * What stopped this reading at {@code position}, in the order the rules were written.
     *
     * <p>Every one of them and each once. Two rules stopped by the same limit are one thing for a
     * reader to lift, and which of them were the parts is the clause's rather than this reading's.
     */
    List<UnreadReason> at(A position) {
        return across(Set.of(position));
    }

    /**
     * The same over several positions at once, which is what a value held at more than one place
     * is asked.
     *
     * <p>A rule naming any of them is a rule about the value all of them hold, so what comes back
     * is every reason once, in the order the rules were written. Which is why the entries are kept
     * whole: read out of a map filed by position, an order over two places would be one this
     * compiler invented.
     */
    List<UnreadReason> across(Set<A> positions) {
        List<UnreadReason> out = new ArrayList<>();
        for (Entry<A> each : entries) {
            if (!Collections.disjoint(each.positions(), positions) && !out.contains(each.why())) {
                out.add(each.why());
            }
        }
        return Collections.unmodifiableList(out);
    }

    /** Every position a rule was left standing at. */
    Set<A> positions() {
        Set<A> out = new LinkedHashSet<>();
        entries.forEach(each -> out.addAll(each.positions()));
        return Collections.unmodifiableSet(out);
    }

    /** The same account of the same rules, under the names {@code naming} gives the positions. */
    <B> Standing<B> renamed(Function<A, B> naming) {
        List<Entry<B>> out = new ArrayList<>();
        entries.forEach(each -> {
            Set<B> positions = new LinkedHashSet<>();
            each.positions().forEach(position -> positions.add(naming.apply(position)));
            out.add(new Entry<>(positions, each.why()));
        });
        return new Standing<>(out);
    }

    /**
     * The same account, said in the order {@code read} were read rather than the order the work
     * was done in.
     *
     * <p>Only the writing down. Every rule here is one of theirs or one the work added, and which
     * they are does not change — what changes is that a reader is shown them in the order the rules
     * were written.
     */
    Standing<A> inTheOrderOf(List<Standing<A>> read) {
        List<Entry<A>> out = new ArrayList<>();
        read.forEach(each -> out.addAll(each.entries));
        return new Standing<>(joined(out, entries));
    }

    private static <A> List<Entry<A>> joined(List<Entry<A>> these, List<Entry<A>> those) {
        List<Entry<A>> out = new ArrayList<>(these);
        those.forEach(each -> {
            if (!out.contains(each)) {
                out.add(each);
            }
        });
        return out;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof Standing<?> it && entries.equals(it.entries);
    }

    @Override
    public int hashCode() {
        return entries.hashCode();
    }

    @Override
    public String toString() {
        return entries.toString();
    }
}
