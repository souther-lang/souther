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
     * values are not the values of the place — {@code Money(x)} is not {@code x} — so the place
     * itself is read as it was ({@link ElementProjection#read}) and the wrapping is said beside it.
     * A value standing as a wider type is not read through: what the wider type says equal or in
     * order is not shown to be what the narrower one does.
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
            ElementProjection at = answer instanceof Core.Widen ? null
                    : ElementProjection.read(answer, element, held, newtypes);
            if (at != null) {
                return new Answered(at, false);
            }
            return switch (answer) {
                case Core.Widen _ -> null;
                case Core.Construct made when newtypes.of(made.typeName().key())
                        && made.values().size() == 1 -> {
                    Answered worn = of(made.values().getFirst().value(), element, held, newtypes);
                    yield worn == null ? null : new Answered(worn.at(), true);
                }
                case null, default -> null;
            };
        }
    }
}
