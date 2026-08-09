package souther.compiler.fmt;

import java.util.List;

/**
 * A break the layout wrote: where it is, how far in the line after it starts, and the nestings it
 * was written under, outermost first.
 *
 * <p>The nestings are named rather than measured. The indentation rule answers about a pair of
 * consecutive levels, and a written indent of eight says only what the second of the two came to —
 * a formatter indenting the first level by four and the second by six writes the same eight.
 */
record Newline(int offset, int indent, List<Doc.NestRef> under, Cause cause) {

    Newline {
        under = List.copyOf(under);
    }

    /**
     * What wrote a break.
     *
     * <p>Two, because the layout writes one for two different reasons and a reader given only the
     * newline cannot tell them apart. Neither is a rule's name: the first carries the obligation the
     * boundary was built for and the second points at the opportunity, which is what
     * {@link Opportunity} settles by naming the group.
     */
    sealed interface Cause {

        /** Written whatever the width, for the obligation named. */
        record Forced(Obligation obligation) implements Cause {}

        /** Written because the group settling this opportunity was not laid out flat. */
        record Settled(Doc.LineRef line) implements Cause {}
    }
}
