package souther.compiler.meaning;

import souther.compiler.inputs.TermPath;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.List;

/**
 * A number a comparison is written over, told apart by which value it is.
 *
 * <p>Wider than what a row controls ({@link DecisionAtom}). A value the body bound to a name — what
 * a dependency answered under {@code let x = opaque()}, what an attempt built — is no position a
 * row writes at, and it is still one value however often it is compared: {@code x < 5} and
 * {@code x < 6} are about one number, and the second follows from the first whatever the number
 * is. Not knowing what a value is computed from is not the same as not knowing which value it is,
 * and only the second leaves a comparison over it with nothing to say.
 */
public sealed interface Quantity permits DecisionAtom, Quantity.OfABinding {

    /**
     * The number at {@code steps} below the value bound at {@code binding}: one value, by the
     * binding that names it and nothing else.
     *
     * <p>By the binding and not by what it was bound to. Two calls of one dependency with one
     * argument are two answers, and a value named twice is one; what tells them apart is which
     * name stands for which, which is what the binding is.
     *
     * <p>A field read that reaches nowhere else — the value inside a newtype — is no step, so
     * {@code x.value} and {@code x} are one quantity, as they are one place.
     *
     * @param binding which binding names the value
     * @param steps   the steps read off it that go somewhere, outermost first
     * @param type    what stands there, which is how its numbers are spaced
     */
    record OfABinding(BindingId binding, List<TermPath.Step> steps, Type type)
            implements Quantity {

        public OfABinding {
            if (binding == null || type == null) {
                throw new IllegalArgumentException("a bound number is some binding's, of some type");
            }
            steps = List.copyOf(steps);
        }

        @Override
        public String toString() {
            StringBuilder out = new StringBuilder(binding.toString());
            steps.forEach(each -> out.append('.').append(each));
            return out.toString();
        }
    }
}
