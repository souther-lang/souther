package souther.compiler.carrier;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Which elements are in, and nothing about what order they were given in.
 *
 * <p>A {@link Set} answers this and more: {@code iterator}, {@code stream}, {@code forEach}, even
 * {@code toString} — every one of them a walk, and a walk taken off a set that was built through a
 * salted copy is a walk taken off nothing, differently on some runs than on others. This answers
 * only whether an element is in, so a caller who wants to know something about an order has to ask
 * a value that states one rather than iterating this to find out — there is nothing here to
 * iterate, no count to take, and nothing that spells the contents out as text either.
 *
 * <p>Not a {@code Set} and not an {@code Iterable}, and built from nothing wider than one element
 * at a time ({@link #built}), so there is no arbitrary iteration this could be built from to launder
 * into an answer that looks like one. A caller who holds a {@code Set} hands its elements over one
 * by one; what this keeps of them is which were handed over, and that is all a reader can ask.
 *
 * <p>An element stated twice is one element: stating {@code x} and stating {@code x} again is what
 * stating {@code x} once already said, so there is nothing to refuse. A caller for whom a repeated
 * element is a mistake of its own says so where it holds the elements — which of them may repeat is
 * a fact about what they are, and this holds nothing about that. A {@code null} element is refused,
 * and so is asking about one.
 *
 * <p>Two of these are equal where they hold the same elements, whichever order they were filled in.
 */
public final class Membership<E> {

    private final Set<E> in;

    private Membership(Set<E> in) {
        this.in = in;
    }

    /**
     * Built from {@code fill}, which hands over one element at a time and nothing else.
     *
     * <p>The {@link Members} {@code fill} is handed writes straight to a set this keeps to itself
     * until {@code fill} returns, and only a snapshot of it leaves — so a caller who keeps the
     * {@link Members} past the call cannot go on changing what a value already built from it holds.
     */
    public static <E> Membership<E> built(Consumer<Members<E>> fill) {
        Set<E> in = new HashSet<>();
        fill.accept(element -> in.add(Objects.requireNonNull(element, "an element")));
        return new Membership<>(Set.copyOf(in));
    }

    /** How {@link #built} is filled: an element to state, and nothing this can be asked to do
     *  besides state one. */
    public interface Members<E> {
        void add(E element);
    }

    /** Whether {@code element} is in. */
    public boolean contains(E element) {
        return in.contains(Objects.requireNonNull(element, "an element"));
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof Membership<?> membership && in.equals(membership.in);
    }

    @Override
    public int hashCode() {
        return in.hashCode();
    }
}
