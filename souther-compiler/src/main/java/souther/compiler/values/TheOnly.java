package souther.compiler.values;

import java.util.Collection;

/**
 * The one thing a collection holds, where holding one is what was proved of it.
 *
 * <p><b>Not a reading of where anything is.</b> A collection of one has one element whichever order
 * it is held in, so taking it is an answer about what the collection holds. Written as the first the
 * walk hands over, it reads as an answer about the walk — and the two are the same answer only
 * while the collection really does hold one, which is the part nothing was saying.
 *
 * <p>So the claim is made where it is relied on. A caller that knows a set holds one block, or that
 * a relation holds a position on one, says that here and is refused where it is wrong; a caller
 * reaching for the first of several is a caller whose answer was settled by how its collection was
 * built, and this is where that stops rather than where it is spelled more carefully.
 *
 * <p>Refused and not chosen between, for the reason a walk of anything unordered refuses: there is
 * no picking one of several that is about the value rather than about the walk, and the several are
 * named so that whoever reads the refusal can see what was in hand.
 */
public final class TheOnly {

    private TheOnly() {
    }

    /**
     * The one element of {@code these}.
     *
     * @param what what these are, for the refusal to name — a reader of one is holding a claim
     *             that failed and needs to know which claim
     * @throws IllegalStateException where these are not one, since an answer taken from several
     *         would be about which of them the collection hands over first
     */
    public static <T> T of(Collection<T> these, String what) {
        if (these.size() != 1) {
            throw new IllegalStateException(
                    "one " + what + " was asked for, and these are " + InOneOrder.of(these));
        }
        return these.iterator().next();
    }
}
