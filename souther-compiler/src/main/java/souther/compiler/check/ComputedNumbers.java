package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The numbers a value's clauses write as arithmetic over its places ({@link ComputedNumber}), and
 * what the rules come to once the places are at numbers.
 *
 * <p>A computed number is an atom of the interval algebra like any other, and a clause comparing it
 * is a rule between atoms. What the algebra cannot know is how the atom is made of the places, which
 * is why the places a clause is written over are not constrained by a rule that only names the atom.
 * The two things said here are the ones that make it known: a clause that defines a place as such a
 * number leaves the places it is made of free ({@link #definedFrom}), and a number made of places
 * that each stand at one number stands at the number it comes to ({@link #settled}).
 */
final class ComputedNumbers {

    private ComputedNumbers() {}

    /** Whether {@code term} stands for a place of the value, which is what a number is made of. */
    static boolean aPlace(Term term) {
        return term.shape() == Term.Shape.AT || term.shape() == Term.Shape.ON;
    }

    /**
     * The places {@code constraint} defines a place from, or none where it does not define one.
     *
     * <p>Defining is {@code x == e}, with {@code e} computed from places other than {@code x}: a
     * relation that says what {@code x} comes to beside the places and says nothing of any one of
     * them. A comparison of a computed number with a written one, or two computed numbers in one
     * rule, relates the places among themselves, and is not read through this.
     */
    static Set<FactSubject> definedFrom(NumericConstraint constraint) {
        Map<FactSubject, ExactRatio> weights = constraint.form().coefs();
        if (constraint.rel() != Rel.EQ || !constraint.form().constant().isZero()
                || weights.size() != 2) {
            return Set.of();
        }
        List<FactSubject> atoms = new ArrayList<>(weights.keySet());
        ExactRatio first = weights.get(atoms.get(0));
        ExactRatio second = weights.get(atoms.get(1));
        if (first.negated().compareTo(second) != 0) {
            return Set.of();
        }
        Set<FactSubject> from = definition(atoms.get(0), atoms.get(1));
        return from.isEmpty() ? definition(atoms.get(1), atoms.get(0)) : from;
    }

    /** The places {@code computed} is made of, where it is made of places other than
     *  {@code defined}, and {@code defined} is itself a place. */
    private static Set<FactSubject> definition(FactSubject defined, FactSubject computed) {
        if (!aPlace(defined.identity())) {
            return Set.of();
        }
        ComputedNumber number = ComputedNumber.of(computed.identity(), ComputedNumbers::aPlace);
        if (number == null || number.places().contains(defined.identity())) {
            return Set.of();
        }
        Set<FactSubject> from = new LinkedHashSet<>();
        number.places().forEach(place -> from.add(FactSubject.of(place)));
        return from;
    }

    /**
     * {@code state} with each computed number equal to what it comes to, wherever every place it is
     * made of stands at one number.
     *
     * <p>Nothing is added for a number with a place that is still free, and nothing is taken away
     * from one that is already known. The equality is stated the way settling a position states
     * one ({@link ConstraintState#settling}), so a number settled here is the number a caller
     * who settled it would have named.
     */
    static ConstraintState<FactSubject> settled(ConstraintState<FactSubject> state) {
        ConstraintState<FactSubject> out = state;
        NumericDomain<FactSubject> numbers = state.numbers();
        // Each number is made of places and never of another number, so settling one does not
        // change what any other is made of and the order they are taken in says nothing.
        for (FactSubject atom : numbers.atomsSpokenOf()) {
            ComputedNumber number = ComputedNumber.of(atom.identity(), ComputedNumbers::aPlace);
            Granularity spacing = numbers.spacingOf(atom);
            if (number == null || spacing == null) {
                continue;
            }
            ExactRatio comesTo = number.comesTo(place -> standingAt(numbers, FactSubject.of(place)));
            Optional<Count> at = comesTo == null ? null : Count.written(comesTo).orNull();
            if (at != null && at.isPresent()) {
                out = ConstraintState.settling(out, atom, at.get(), spacing);
            }
        }
        return out;
    }

    /** The one number {@code place} stands at, or null where the rules leave it more than one. */
    private static ExactRatio standingAt(NumericDomain<FactSubject> numbers, FactSubject place) {
        NumericDomain.Bounds bounds = numbers.boundsOf(place);
        if (bounds.min() == null || bounds.max() == null || !bounds.min().inclusive()
                || !bounds.max().inclusive()) {
            return null;
        }
        ExactRatio low = Count.number(bounds.min().at()).exactly();
        return low.compareTo(Count.number(bounds.max().at()).exactly()) == 0 ? low : null;
    }
}
