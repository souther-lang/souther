package souther.compiler.publish;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

/**
 * Some of one kind of reason, in the order everything outside this compiler is given them in.
 *
 * <p>A set says which reasons hold and says nothing about which comes first. What a report writes
 * is a sequence, so an order is taken from somewhere whatever anybody decides: from the order the
 * constants happen to be declared in, where the set is an {@code EnumSet}, or from the order a walk
 * happened to find them in, where it is not. Neither is a decision about what a reader is shown,
 * and both move when somebody tidies something they have nothing to do with.
 *
 * <p>So the crossing is made once and made here. Past it a plurality of one kind is this, which is
 * the written order of that kind with what is not held left out — and there is one way to reach it,
 * {@link Order#keep}. The constructor is private and no other class is in a position to call it,
 * so a sequence of reasons that nobody put in order cannot be built, let alone published.
 *
 * <p><b>An order and not a rank.</b> Nothing here says one reason outranks another, and nothing
 * offers a comparison between two of them. What is written down is the sequence itself, which is
 * all a total order over a finite set is; a number per member is a carrier wider than that, and two
 * members given one number come out in whichever order they were found in.
 *
 * @param <T> the kind of reason, whose order {@link PublicationOrders} writes down
 */
public final class CanonicalSelection<T> {

    private final List<T> written;

    private CanonicalSelection(List<T> written) {
        this.written = written;
    }

    /** The members that are held, in the order they are said. */
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
        return other instanceof CanonicalSelection<?> it && written.equals(it.written);
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
     * The order one kind of reason is published in, and the only way to select from it.
     *
     * <p>Made where the orders are declared and nowhere else: the factories are package-private, so
     * a second order over a kind that already has one is not something another part of this
     * compiler can write. What it holds is a sequence of slots — the members themselves, where the
     * kind can be written out as values, or the arms, where a member carries something and the
     * order of the payload is that payload's own kind to decide.
     *
     * <p><b>A composite orders only what the composing introduced.</b> An order over arms says
     * which arm is said first and nothing about what is inside one, because deciding that here
     * would be a second order over a kind that has one already.
     */
    public static final class Order<T> {

        private final List<Object> slots;
        private final Function<T, Object> slotOf;

        private Order(List<Object> slots, Function<T, Object> slotOf) {
            if (List.copyOf(slots).size() != Set.copyOf(slots).size()) {
                throw new IllegalArgumentException(
                        "an order says each of its places once: " + slots);
            }
            this.slots = List.copyOf(slots);
            this.slotOf = slotOf;
        }

        /** The order of a kind whose members can be written out, each its own place. */
        static <T> Order<T> overValues(List<T> values) {
            return new Order<>(List.copyOf(values), each -> each);
        }

        /**
         * The order of a kind whose members carry something, one place per family.
         *
         * <p>A family and not a class. What a report says once may be answered in more than one
         * way — a question about a point is open where a reading stopped and where nothing was
         * read — and a place per concrete answer would hold two where the sentence holds one, which
         * is the order deciding a question from whatever happened to leave it open. Where a family
         * has one member the two are the same thing.
         *
         * <p>At most one member to a place, which is what {@link #keep} holds to. Two members of
         * one family are two answers to a question asked once, and putting them in order would be
         * this deciding which of the two a reader is told.
         */
        static <T> Order<T> overFamilies(List<Class<? extends T>> families) {
            List<Object> slots = List.copyOf(families);
            return new Order<>(slots, value -> {
                Object found = null;
                for (Object each : slots) {
                    if (((Class<?>) each).isInstance(value)) {
                        if (found != null) {
                            throw new IllegalArgumentException("a reason in two places in the order"
                                    + " it is published in: " + value);
                        }
                        found = each;
                    }
                }
                return found;
            });
        }

        /**
         * The members of {@code held}, in this order.
         *
         * <p>Built by taking the order and keeping what is held, rather than by taking what is held
         * and putting it in order. Nothing here compares two members, so there is no comparison to
         * be undecided between two of them.
         *
         * <p>Refused rather than mended in the two cases where mending would be an answer of this
         * one's own: a member with no place in the order is one nothing would publish, and two
         * members in one place are two things to say where the order has room for one.
         */
        public CanonicalSelection<T> keep(Collection<? extends T> held) {
            Map<Object, T> bySlot = new LinkedHashMap<>();
            for (T each : held) {
                Object slot = slotOf.apply(Objects.requireNonNull(each,
                        "a reason that is nothing is not one this compiler met"));
                if (!slots.contains(slot)) {
                    throw new IllegalArgumentException(
                            "a reason with no place in the order it is published in: " + each);
                }
                T already = bySlot.put(slot, each);
                if (already != null && !already.equals(each)) {
                    throw new IllegalArgumentException("two reasons for one place in the order they"
                            + " are published in: " + already + " and " + each);
                }
            }
            List<T> out = new ArrayList<>();
            for (Object slot : slots) {
                T here = bySlot.get(slot);
                if (here != null) {
                    out.add(here);
                }
            }
            return new CanonicalSelection<>(List.copyOf(out));
        }

        /**
         * The places themselves, for the check that the order holds every one there is.
         *
         * <p>The one property a sequence cannot carry for itself. Repeats, pairs out of order and
         * two members in one place are all impossible in a sequence; a member the order leaves out
         * is not, and it is a reason something could be published for and no order anywhere would
         * place.
         *
         * <p>Kept inside this package. Offered wider, the full order is a list anybody can walk and
         * keep what they hold of — which is the thing {@link #keep} exists to be the only way to
         * do, written out again at the far end.
         */
        List<Object> slots() {
            return slots;
        }
    }
}
