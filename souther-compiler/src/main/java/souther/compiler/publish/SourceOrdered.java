package souther.compiler.publish;

import souther.compiler.inputs.AuthoredOrder;

import java.util.List;

/**
 * Some of one kind of reason, in the order the author wrote what raised them.
 *
 * <p>The other way a plurality can arrive with an order. A {@link CanonicalSelection} is in the
 * order this compiler publishes that kind in, which is a decision about what a reader is shown; this
 * is in an order the model already has, and what a reader is shown is that order because it is the
 * author's. The reasons a question stands are the parts of a clause that raised it, and a consumer
 * reading the first entry as the first thing to lift is reading what the author wrote first.
 *
 * <p><b>So the two are told apart by their types and not by their containers.</b> A list says
 * somebody put it in an order and does not say who: the walk that found the reasons, or the person
 * who wrote them. Between those two the difference is the whole of what a reader may do with the
 * order — one of them is a fact about the model and the other is a fact about a traversal — so a
 * plurality that reaches a report says which it is, or it is a plurality nobody has answered for.
 *
 * <p><b>What this cannot check is that the order it is handed is the author's.</b> Nothing in a
 * list of reasons says where its order came from; a caller states it by making one of these. What
 * it does make impossible is a plurality crossing into a report without either order being claimed
 * for it.
 *
 * <p>Each reason once, keeping the first place it was written at. Two parts one limit stopped are
 * one thing to lift and one entry, and the entry is where the first of them stands.
 */
public final class SourceOrdered<T> {

    private final List<T> written;

    private SourceOrdered(List<T> written) {
        this.written = written;
    }

    /**
     * The reasons as the author wrote them, carried across from where that was said.
     *
     * <p><b>Not a place the claim is made.</b> Whether an order is the model's is decided by
     * whoever had the source in hand, and {@link AuthoredOrder} is that claim said there; this
     * carries it to the crossing. Taking a bare list instead, the claim was made by whatever was
     * holding one — and a projection two packages from anything that had seen a clause was stating
     * a fact about the model, correctly for as long as there was one producer.
     *
     * <p>Where the order is this compiler's, it belongs to {@link PublicationOrders} and the value
     * is a {@link CanonicalSelection}. There is no third kind, and a plurality that is partly one
     * and partly the other is two pluralities: nothing in the model puts a part somebody wrote
     * before or after a limit that belongs to no part, so a sequence across the two would publish a
     * precedence out of the store a reason was recorded in.
     */
    public static <T> SourceOrdered<T> carrying(AuthoredOrder<T> written) {
        return new SourceOrdered<>(List.copyOf(written.written()));
    }

    /** The reasons that are held, in the order they were written. */
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
        return other instanceof SourceOrdered<?> it && written.equals(it.written);
    }

    @Override
    public int hashCode() {
        return written.hashCode();
    }

    @Override
    public String toString() {
        return written.toString();
    }
}
