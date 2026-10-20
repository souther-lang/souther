package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A container of the input a list holds one value for each element of, and where in the element
 * that value stands ({@link ElementQuestion#ONE_PER_ELEMENT}).
 *
 * <p>Each element is answered once, in the one occurrence of the container the list was made
 * from, so how often a value occurs among what the list holds is how often it occurs at that place
 * among the elements of that occurrence.
 *
 * @param container the position of the container
 * @param projected the way from an element of it to the value the list holds for that element
 * @param wrapped   whether some step answered a newtype wearing that value rather than the value:
 *                  which values are equal is kept, and nothing about their order is said
 */
public record OnePerElement(TermPath container, ElementProjection projected, boolean wrapped) {

    public OnePerElement {
        Objects.requireNonNull(container, "a run of one value for each element is over a container");
        Objects.requireNonNull(projected, "and the value held for an element stands somewhere in"
                + " it, the element itself at the least");
    }

    /** The position of what stands at {@code within} in the value held for an element. */
    public TermPath placeOf(ElementProjection within) {
        return projected.then(within).from(container.element());
    }

    /**
     * What an answer made of one element is, as far as which answers are equal goes: the value at
     * a place of the element, or a newtype wearing it.
     *
     * <p>A newtype of one value is a name the value wears, and two of them are equal exactly where
     * the values are, which is the whole of what a count of how often a key occurs asks. Its
     * values are not the values of the place — {@code Money(x)} is not {@code x} — so the way to
     * the place is the one a place is read by and the wrapping is said beside it. A value standing
     * as a wider type is not read through: what the wider type says equal or in order is not shown
     * to be what the narrower one does. Both are said of every node on the way, behind a name or a
     * {@code let} as much as at the answer itself, by the one walk a place is read by
     * ({@link ElementProjection#readAsAKey}).
     *
     * @param at      the way from the element to the value the answer is or wears
     * @param wrapped whether the answer wears that value as a newtype rather than being it
     */
    public record Answered(ElementProjection at, boolean wrapped) {

        public Answered {
            Objects.requireNonNull(at, "an answer is or wears the value at some place of the"
                    + " element, the element itself at the least");
        }

        /** The element itself. */
        public static final Answered ITSELF = new Answered(new ElementProjection(List.of()), false);

        /**
         * What {@code answer}, made of the element handed to {@code element}, is, or null where it
         * is no place of that element and no newtype wearing one.
         *
         * @param held what each binding on the way holds, over the whole body the answer is in
         */
        public static Answered of(Core answer, BindingId element, Map<BindingId, Core> held,
                                  DeclarationNewtypes newtypes) {
            return ElementProjection.readAsAKey(answer, element, held, newtypes);
        }
    }

    /**
     * What a reading takes out of each element of a list, where the element may be something a
     * walk built and no place of the input: a component of the tuple it is, and then a way into
     * what that comes to.
     *
     * <p>A key or a value a fold's step reads off its element is read off what the list holds,
     * which a walk may have built of each element of another list. Crossing that walk takes the
     * construction apart ({@link ElementProjection#readAsAKey(Core, ReadOff, BindingId, Map,
     * DeclarationNewtypes)}), and once nothing is left to take apart the read is a place of the
     * element it reached.
     *
     * @param component which component of the tuple each element is is taken, or -1 where the
     *                  element is read as it is
     * @param then      what is read from there: a way to a value, and whether a newtype wearing it
     *                  was read through on the way
     */
    public record ReadOff(int component, Answered then) {

        public ReadOff {
            Objects.requireNonNull(then, "a read goes on to some value, the one it came to at the"
                    + " least");
        }

        /** The element itself. */
        public static final ReadOff ITSELF = new ReadOff(-1, Answered.ITSELF);

        /** Whether nothing is left to take apart, so that the read is a place of the element. */
        public boolean placed() {
            return component < 0;
        }
    }
}
