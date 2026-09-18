package souther.compiler.numeric;

import java.util.Comparator;

/**
 * One order over the positions of an atom domain, for a walk that has to take them in one.
 *
 * <p><b>What a value of that domain is, said as an order.</b> A form is a mapping and holds no order
 * of its own; a reader that walks it to work a bound out at each position, or to say which of them a
 * rule left unbounded, has the order it walked in inside its answer. So two forms that are equal
 * have to hand that reader one walk, and what settles the walk has to be the same thing that settles
 * whether two positions are one.
 *
 * <p><b>Which is why this is not a comparator a value carries.</b> Held inside a form, an order
 * would make one rule two values under two policies; hidden inside one, equal forms would walk two
 * ways under two policies and the reader's answer would be back where it started. It belongs to the
 * atom domain, and it is asked for where the walk is.
 *
 * <p><b>The law.</b> {@code compare(a, b) == 0} exactly where {@code a.equals(b)}. Weaker than that,
 * a walk would take two positions for one and hand one of them over twice and the other never;
 * stronger is not a thing an order can be. A domain that cannot promise it for every pair it may
 * meet says so by refusing the pair it cannot tell apart rather than by choosing between them —
 * {@link CanonicalForm#entriesIn} is where such a pair is met.
 *
 * <p><b>And read off what equality reads and nothing else.</b> A rendering is written for a person:
 * two positions rendering alike are not one position, which is why an order taken off the renderings
 * is not one of these however well it happens to work today.
 *
 * @param <A> what a position of the domain is
 */
public interface CanonicalOrder<A> extends Comparator<A> {

    /**
     * The order a domain whose positions compare consistently with their own equality already has.
     *
     * <p>For a position that is a string, a number, an enum constant or anything else whose
     * {@code compareTo} is nought exactly where {@code equals} is true — which is what
     * {@link Comparable} asks of an implementation and what most of them keep. Such a domain has
     * nothing of its own to say here, and saying it again would be a second spelling of the same
     * order to fall out of step with the first.
     *
     * <p>A domain whose comparison is coarser than its equality is not one of these, however well it
     * reads. It says what its order is itself, and where two positions it cannot tell apart reach
     * one walk it refuses rather than choosing between them.
     */
    static <A extends Comparable<A>> CanonicalOrder<A> asTheyCompare() {
        return Comparable::compareTo;
    }
}
