package souther.compiler.publish;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;

/**
 * Everything of one kind a document writes, in the order it writes them.
 *
 * <p>Beside {@link CanonicalSelection} and not a widening of it. That one is a finite list of
 * places with at most one member to a place, which is what a plurality of a kind of reason is; this
 * is for an array whose length is not bounded by any vocabulary — the facts a verdict is open on,
 * the reasons a module could not read everything — where two members can be the same word and both
 * are written.
 *
 * <p>So the two need different arithmetic. A selection takes the order and keeps what is held and
 * never compares two members; there is nothing else it could do, and nothing here it could do
 * either, because a place per member would be a list as long as the model. What is written down for
 * one of these is a key and an order over keys, and the sequence is what sorting by that comes to.
 *
 * <p><b>Which is safe only because a tie is not a choice.</b> Two members whose keys compare equal
 * would be published in whichever order the sort left them in, and that order is the one the caller
 * handed over — a walk's. So the key must tell apart everything a reader can tell apart, and it is
 * held to that here: two members that compare equal and are not equal are refused. A sort's
 * stability is then something nothing rests on.
 *
 * <p>What follows is that these are arranged over what a document writes and never over what it
 * writes them from. A key over the values a measure produced would be free to leave out what a
 * document prints, and the two members it could not tell apart would come out in the order they
 * were met.
 *
 * @param <T> what one entry of the array is, as the document writes it
 */
public final class CanonicalArrangement<T> {

    private final List<T> written;

    private CanonicalArrangement(List<T> written) {
        this.written = written;
    }

    /** The entries, in the order they are written. */
    public List<T> written() {
        return written;
    }

    public boolean isEmpty() {
        return written.isEmpty();
    }

    public int size() {
        return written.size();
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof CanonicalArrangement<?> it && written.equals(it.written);
    }

    @Override
    public int hashCode() {
        return written.hashCode();
    }

    @Override
    public String toString() {
        return written.toString();
    }

    /**
     * The order one such array is written in, and the only way to build one.
     *
     * <p>Made where the orders are declared and nowhere else, for the reason
     * {@link CanonicalSelection.Order} gives: a second order over a kind that has one is not
     * something another part of this compiler is in a position to write.
     */
    public static final class Order<T> {

        private final Comparator<T> by;

        private Order(Comparator<T> by) {
            this.by = by;
        }

        /** The order a kind of entry is written in, as a comparison of what a document writes. */
        static <T> Order<T> by(Comparator<T> by) {
            return new Order<>(Objects.requireNonNull(by, "an array is written in some order"));
        }

        /**
         * The entries of {@code held}, in this order, each of them kept.
         *
         * <p>Nothing is folded. Two entries a document writes alike are two things that happened,
         * and an array whose length said how many kinds there are would be answering the question
         * the other array already answers.
         *
         * <p>Refused where two entries compare equal and are not equal, which is the one case where
         * this would be publishing an order nobody decided.
         */
        public CanonicalArrangement<T> arrange(Collection<? extends T> held) {
            List<T> out = new ArrayList<>(held.size());
            for (T each : held) {
                out.add(Objects.requireNonNull(each, "an entry a document writes is something"));
            }
            out.sort(by);
            for (int i = 1; i < out.size(); i++) {
                T before = out.get(i - 1);
                T here = out.get(i);
                if (by.compare(before, here) == 0 && !before.equals(here)) {
                    throw new IllegalArgumentException("two entries this order cannot tell apart,"
                            + " so which of them a document writes first is whichever it was"
                            + " handed first: " + before + " and " + here);
                }
            }
            return new CanonicalArrangement<>(List.copyOf(out));
        }
    }
}
