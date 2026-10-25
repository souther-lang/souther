package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.HashSet;
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
 * is a rule between atoms. What the algebra cannot know is how the atom is made of the places. Two
 * things are said here for it: a place defined as such a number leaves the places it is made of free
 * only where the number cannot come to anything the place's other rules refuse
 * ({@link #leavesFree}), and a number made of places that each stand at one number stands at the
 * number it comes to ({@link #settled}).
 */
final class ComputedNumbers {

    private ComputedNumbers() {}

    /** Whether {@code term} stands for a place of the value, which is what a number is made of. */
    static boolean aPlace(Term term) {
        return term.shape() == Term.Shape.AT || term.shape() == Term.Shape.ON;
    }

    /**
     * A place and the number it is defined as: {@code defined == number}, the number made of places
     * other than the one it defines.
     *
     * @param defined the place
     * @param atom    the atom standing for the number
     */
    record Definition(FactSubject defined, FactSubject atom, ComputedNumber number) {

        /** The places the number is made of. */
        Set<FactSubject> operands() {
            Set<FactSubject> out = new LinkedHashSet<>();
            number.places().forEach(place -> out.add(FactSubject.of(place)));
            return out;
        }
    }

    /** A definition and the rule that states it. */
    record Defining(RuleRef.Invariant rule, Definition definition) {}

    /** The definitions {@code owed} states for {@code rule}. */
    static List<Defining> definingIn(RuleRef.Invariant rule, Predicates.Owed owed) {
        List<Defining> out = new ArrayList<>();
        for (Predicates.Part each : owed.parts()) {
            if (each instanceof Predicates.Part.Carried carried
                    && carried.clause().numeric() != null) {
                Definition definition = definitionIn(carried.clause().numeric());
                if (definition != null) {
                    out.add(new Defining(rule, definition));
                }
            }
        }
        return out;
    }

    /**
     * {@code constraint} read as defining a place as a number made of others, or null where it does
     * not.
     *
     * <p>A comparison of a computed number with a written one, or two computed numbers in one rule,
     * relates the places among themselves, and is not read through this.
     */
    static Definition definitionIn(NumericConstraint constraint) {
        Map<FactSubject, ExactRatio> weights = constraint.form().coefs();
        if (constraint.rel() != Rel.EQ || !constraint.form().constant().isZero()
                || weights.size() != 2) {
            return null;
        }
        List<FactSubject> atoms = new ArrayList<>(weights.keySet());
        ExactRatio first = weights.get(atoms.get(0));
        ExactRatio second = weights.get(atoms.get(1));
        if (first.negated().compareTo(second) != 0) {
            return null;
        }
        Definition definition = definition(atoms.get(0), atoms.get(1));
        return definition != null ? definition : definition(atoms.get(1), atoms.get(0));
    }

    private static Definition definition(FactSubject defined, FactSubject computed) {
        if (!aPlace(defined.identity())) {
            return null;
        }
        ComputedNumber number = ComputedNumber.of(computed.identity(), ComputedNumbers::aPlace);
        return number == null || number.places().contains(defined.identity()) ? null
                : new Definition(defined, computed, number);
    }

    /**
     * Whether {@code definition}'s places are left as free as they were by the rule defining a
     * place from them, given everything {@code numbers} holds.
     *
     * <p>Free where the number lies, whatever the places are, inside what the defined place may be:
     * any places then have a value of the defined place beside them, and the rule restricts none.
     * Not free where the place has been held to less by another rule ({@code c == a * b} beside
     * {@code c == 1} leaves no {@code a} of nought), or where the number reaches past what the place
     * admits, because then some places have none.
     */
    static boolean leavesFree(Definition definition, NumericDomain<FactSubject> numbers) {
        ComputedNumber.Range image = definition.number()
                .lies(place -> rangeOf(numbers.boundsOf(FactSubject.of(place))));
        NumericDomain.Bounds allowed = numbers.boundsOf(definition.defined());
        return reachesNoFurtherThan(image.low(), allowed.min(), true)
                && reachesNoFurtherThan(image.high(), allowed.max(), false);
    }

    private static ComputedNumber.Range rangeOf(NumericDomain.Bounds bounds) {
        return new ComputedNumber.Range(
                bounds.min() == null ? null : Count.number(bounds.min().at()).exactly(),
                bounds.max() == null ? null : Count.number(bounds.max().at()).exactly());
    }

    /** Whether an end of the number's range is inside the end of the range the place allows. */
    private static boolean reachesNoFurtherThan(ExactRatio end, Endpoint allowed,
                                                boolean fromBelow) {
        if (allowed == null) {
            return true;
        }
        if (end == null) {
            return false;
        }
        int against = end.compareTo(Count.number(allowed.at()).exactly());
        int inside = fromBelow ? against : -against;
        return inside > 0 || (inside == 0 && allowed.inclusive());
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
        return settled(state, in(state));
    }

    /**
     * The same, for a caller that settles one state's places many times and has asked which
     * numbers there are once.
     *
     * <p>Taken to where nothing more settles. A place a number is made of may itself stand at what
     * another number comes to, which is only known once that one is settled, so the numbers are
     * asked again over what the settling so far left until a pass settles none. Each pass settles a
     * number it has not, so there are no more passes than numbers.
     */
    static ConstraintState<FactSubject> settled(ConstraintState<FactSubject> state,
                                                List<Computed> numbers) {
        ConstraintState<FactSubject> out = state;
        Set<FactSubject> done = new HashSet<>();
        boolean moved = true;
        while (moved) {
            moved = false;
            NumericDomain<FactSubject> domain = out.numbers();
            for (Computed each : numbers) {
                if (done.contains(each.atom())) {
                    continue;
                }
                ExactRatio comesTo = each.number()
                        .comesTo(place -> standingAt(domain, FactSubject.of(place)));
                Optional<Count> at = comesTo == null ? null : Count.written(comesTo).orNull();
                if (at != null && at.isPresent()) {
                    out = ConstraintState.settling(out, each.atom(), at.get(), each.spacing());
                    done.add(each.atom());
                    moved = true;
                }
            }
        }
        return out;
    }

    /** A number the rules write as arithmetic over places, and how its values are spaced. */
    record Computed(FactSubject atom, ComputedNumber number, Granularity spacing) {}

    /**
     * The numbers {@code state} holds that are arithmetic over places.
     *
     * <p>Settling a place states an equality on an atom the state already has, so the atoms are
     * the same whatever is settled and one reading of them serves every settling.
     */
    static List<Computed> in(ConstraintState<FactSubject> state) {
        NumericDomain<FactSubject> domain = state.numbers();
        List<Computed> out = new ArrayList<>();
        for (FactSubject atom : domain.atomsSpokenOf()) {
            ComputedNumber number = ComputedNumber.of(atom.identity(), ComputedNumbers::aPlace);
            Granularity spacing = domain.spacingOf(atom);
            if (number != null && spacing != null) {
                out.add(new Computed(atom, number, spacing));
            }
        }
        return List.copyOf(out);
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
