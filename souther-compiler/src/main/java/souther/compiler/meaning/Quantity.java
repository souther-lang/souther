package souther.compiler.meaning;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

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
        Quantity.HowManyMeet, Quantity.HowManyHold, Quantity.HowManyDifferent, Quantity.SumOver {

    /**
     * Whether every position this is read off is at or under one of {@code roots}: the position a
     * number is of, and the container a count or a sum is over. A value a body bound or a
     * dependency answered is computed from something nothing here names, and what a count meets
     * is the closure's, so neither is held against {@code roots}.
     */
    default boolean staysWithin(Collection<TermPath> roots) {
        return switch (this) {
            case DecisionAtom.OfTheInput(var term) -> term.subjectPath().isAtOrUnderAny(roots);
            case DecisionAtom.OfAnAnswer _, OfABinding _, HowManyHold _ -> true;
            case HowManyMeet(TermPath counted, var _) -> counted.isAtOrUnderAny(roots);
            case HowManyDifferent(TermPath counted, TermPath each) ->
                    counted.isAtOrUnderAny(roots) && each.isAtOrUnderAny(roots);
            case SumOver(TermPath summed, var each) -> summed.isAtOrUnderAny(roots)
                    && each.coefs().keySet().stream().allMatch(one -> one.staysWithin(roots));
        };
    }

    /**
     * How many different values stand at {@code ofTheElement} over the elements of the container
     * at {@code container}: the element itself, a position inside it, or the key it is filed under
     * — two of them one value where they are equal. Never more than the container holds, and
     * nought exactly where it holds nothing.
     *
     * <p>A number about every pair of elements and not about each: whether one adds to it turns on
     * the ones beside it, so it is no count of elements meeting something.
     */
    record HowManyDifferent(TermPath container, TermPath ofTheElement) implements Quantity {

        public HowManyDifferent {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("the values are of a container's elements");
            }
            if (!ofTheElement.isAtOrUnder(container.element())
                    && !ofTheElement.isAtOrUnder(container.key())) {
                throw new IllegalArgumentException(ofTheElement + " is no part of an element of "
                        + container);
            }
        }

        @Override
        public String spelled() {
            return "#different " + container + " [" + ofTheElement + "]";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What {@code ofTheElement}, a number of each element of the container at {@code container},
     * adds up to over all of them: how many the lists inside a list hold between them, say. The
     * input's own totals are of a value standing at one position inside each element
     * ({@code NumericTerm.TakenOver}); this is of any number of the element.
     */
    record SumOver(TermPath container, LinearForm<Quantity> ofTheElement) implements Quantity {

        public SumOver {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("a sum is of a number of each element");
            }
        }

        @Override
        public String spelled() {
            StringBuilder out = new StringBuilder("#sum " + container + " [");
            out.append(ofTheElement.constant());
            ofTheElement.coefs().forEach((each, by) -> out.append(" + ").append(by).append('·')
                    .append(each.spelled()));
            return out.append(']').toString();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

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

        /**
         * That some element meets what is counted: the count being one or more, which is what it
         * is wherever a count is held against nought ({@link Proposition#compared}).
         */
        public Proposition someMeets() {
            return new Proposition.Some(container, ofTheElement, true);
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
     * <p>What the value was made from is no part of a statement about it, and is carried beside
     * the binding only as far as a reader is owed: where the reading of it stopped, which is why
     * the number is none of the input's. A reader that takes a fact about the value takes all the
     * statement says, and one that cannot settle something past it says that this was what it
     * could not read. Empty where nothing of the value was read to stop — an answer a dependency
     * gave, what an attempt built — since there is nothing it is made of to read.
     *
     * @param binding which binding names the value
     * @param steps   the steps read off it that go somewhere, outermost first
     * @param type    what stands there, which is how its numbers are spaced
     * @param madeOf  why what the value was made from is no number of the input, where the
     *                reading met it and stopped
     */
    record OfABinding(BindingId binding, List<TermPath.Step> steps, Type type,
                      Optional<WhyUnread> madeOf)
            implements Quantity {

        public OfABinding {
            if (binding == null || type == null || madeOf == null) {
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
