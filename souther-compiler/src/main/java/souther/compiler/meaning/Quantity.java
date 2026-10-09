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
public sealed interface Quantity permits DecisionAtom, Quantity.OfABinding,
        Quantity.HowManyMeet, Quantity.HowManyHold {

    /**
     * How many of these statements hold: what a closure states of each value a container was
     * written with, one statement for each.
     *
     * <p>No count of a container the input holds. The values are written out, so each is a
     * statement of its own about the input, and how many of them hold against a number is which of
     * them hold — said that way where it is compared ({@link Proposition#compared}). Of statements
     * none of which is settled: one that is settled is already a number, and is added beside this.
     */
    record HowManyHold(List<Proposition> each) implements Quantity {

        public HowManyHold {
            each = List.copyOf(each);
            if (each.isEmpty()) {
                throw new IllegalArgumentException("how many of no statements hold is none");
            }
            if (each.stream().anyMatch(one -> one instanceof Proposition.Always)) {
                throw new IllegalArgumentException("a settled statement is a number, and not one"
                        + " of these: " + each);
            }
        }

        @Override
        public String spelled() {
            StringBuilder out = new StringBuilder("#[");
            for (int i = 0; i < each.size(); i++) {
                out.append(i == 0 ? "" : ", ").append(each.get(i).key());
            }
            return out.append("]").toString();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * How many elements of the container at {@code container} meet {@code ofTheElement}: never
     * fewer than none, never more than the container holds, and none exactly where no element
     * meets it.
     *
     * <p>A number with a statement inside, and not a value of the input: what it is turns on every
     * element, so held against nought it is that statement quantified ({@link
     * Proposition#compared}), and held against any other number it says how many, which is kept
     * as the relation. What it is about is the element where it stands, so two counts written with
     * their elements named differently are one count.
     *
     * <p>Only of a statement that may come out one way for one element and the other way for
     * another, and only of a statement read through: a count of what is the same for every element
     * is the container's size or none, and a count of what nobody read is no number anything can be
     * said of.
     */
    record HowManyMeet(TermPath container, Proposition ofTheElement) implements Quantity {

        public HowManyMeet {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("a count is of the elements of some container");
            }
            if (!ofTheElement.mayTurnOnAnElementOf(container)) {
                throw new IllegalArgumentException("a count of " + ofTheElement
                        + " is the same for every element of " + container);
            }
            if (Proposition.leavesSomethingUnread(ofTheElement)) {
                throw new IllegalArgumentException("a count is of a statement read through, and "
                        + ofTheElement + " was not");
            }
        }

        @Override
        public String spelled() {
            return "#" + container + " [" + ofTheElement.key() + "]";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What this quantity is, as an identity spells it.
     *
     * <p>Whole, so that two quantities are one exactly where they are the same thing. A dependency
     * is written under the module that declares it: two modules may declare behaviors of one name,
     * and a spelling that left the module off would make the order two quantities come in — and so
     * which way a comparison over them faces ({@link Relation.OneWay}) — turn on which of them a
     * reader happens to meet.
     */
    String spelled();

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
        public String spelled() {
            StringBuilder out = new StringBuilder(binding.toString());
            steps.forEach(each -> out.append('.').append(each));
            return out.toString();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }
}
