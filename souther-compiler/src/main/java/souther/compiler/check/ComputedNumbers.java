package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumberSpace;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

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
    static List<Defining> definingIn(RuleRef.Invariant rule, Predicates.Owed owed,
                                     Function<Term, ComputedNumber.Range> orders) {
        List<Defining> out = new ArrayList<>();
        for (Predicates.Part each : owed.parts()) {
            if (each instanceof Predicates.Part.Carried carried
                    && carried.clause().numeric() != null) {
                Definition definition = definitionIn(carried.clause().numeric(), orders);
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
    static Definition definitionIn(NumericConstraint constraint,
                                   Function<Term, ComputedNumber.Range> orders) {
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
        Definition definition = definition(atoms.get(0), atoms.get(1), orders);
        return definition != null ? definition : definition(atoms.get(1), atoms.get(0), orders);
    }

    private static Definition definition(FactSubject defined, FactSubject computed,
                                         Function<Term, ComputedNumber.Range> orders) {
        if (!aPlace(defined.identity())) {
            return null;
        }
        ComputedNumber number =
                ComputedNumber.of(computed.identity(), ComputedNumbers::aPlace, orders);
        return number == null || number.places().contains(defined.identity()) ? null
                : new Definition(defined, computed, number);
    }

    /**
     * Whether {@code definition}'s places are left as free as they were by the rule defining a
     * place from them, given everything {@code numbers} holds.
     *
     * <p>Free where two things are shown. Nothing else ties any of the places to another position
     * ({@link NumericDomain#relationsOf}): a range is a box and says nothing of how two positions go
     * together, so independence is shown by there being no rule that relates them and never by where
     * their ranges lie ({@code c == a * b} beside {@code c == a + 1} puts no end on {@code c} and
     * still holds {@code a} and {@code b} to two pairs). And the number lies, whatever the places
     * are, inside what the defined place admits: any places then have a value of the defined place
     * beside them, and the rule restricts none ({@code c == 1} leaves no {@code a} of nought).
     * Where either is not shown the places stay unanswered, which is the rule left unread and not a
     * claim about them.
     *
     * <p>And the two are asked of what the places can be, which is not what their ranges say. A range
     * is the hull of what a place admits: a place that admits one number or three admits less than
     * its range, and a rule read as alternatives, or not read, leaves the interval algebra holding
     * the hull and nothing of the gap. So the defined place has to restrict nothing besides its
     * range, and every place has to be shown exact ({@link Account}). The numbers also stop where
     * their order does: the arithmetic of whole numbers aborts at the step that leaves them, so a
     * product of two whole numbers each as great as the order allows is no value of any place, and
     * every step of the number is held inside the order it is worked out in.
     */
    static boolean leavesFree(Definition definition, NumericDomain<FactSubject> numbers,
                              Account account) {
        // Nothing but the definition ties the defined place or the number to another position, and
        // nothing ties a place the number is made of to any. A range is a box and says nothing of
        // how two positions go together, so a place related to another by some other rule is not
        // shown free by where its range lies: the relation is the part that is not read.
        if (numbers.relationsOf(definition.defined()) != 1
                || numbers.relationsOf(definition.atom()) != 1
                || definition.operands().stream().anyMatch(each -> numbers.relationsOf(each) != 0)) {
            return false;
        }
        if (!account.restrictsNothingBesideItsRange(definition.defined())
                || !definition.operands().stream().allMatch(account::shownExact)) {
            return false;
        }
        NumericDomain.Bounds order = account.orderOf(definition.defined());
        if (order == null) {
            return false;
        }
        ComputedNumber.Range image = definition.number().lies(place -> {
            NumericDomain.Bounds stops = account.orderOf(FactSubject.of(place));
            return stops == null ? null
                    : within(numbers.boundsOf(FactSubject.of(place)), stops);
        });
        if (image == null) {
            return false;
        }
        NumericDomain.Bounds allowed = numbers.boundsOf(definition.defined());
        return reachesNoFurtherThan(image.low(), allowed.min(), true)
                && reachesNoFurtherThan(image.high(), allowed.max(), false)
                && reachesNoFurtherThan(image.low(), order.min(), true)
                && reachesNoFurtherThan(image.high(), order.max(), false);
    }

    /** What the reading of a value's rules can say of a place beyond the ranges of the interval
     *  algebra. */
    interface Account {

        /** Where the order the value of {@code place} is counted on stops, a place or a step made
         *  of places: open ends where it does not stop, and null where the order is not known,
         *  which proves nothing. */
        NumericDomain.Bounds orderOf(FactSubject place);

        /** Whether what is held of the place is what the rules leave it, and not something wider
         *  that a choice reaching across places left. */
        boolean shownExact(FactSubject place);

        /** Whether the place is shown exact and its rules leave it every number its range
         *  holds. */
        boolean restrictsNothingBesideItsRange(FactSubject place);
    }

    /**
     * The order the value of each term runs on, as the range it runs over, or null for a term no
     * order is known for.
     *
     * <p>Asked of the terms as they were named: the type of the expression a term was named from is
     * the type of the value, and a step of a number answers on it.
     */
    static Function<Term, ComputedNumber.Range> ordersOf(Terms terms) {
        return term -> {
            Carrier order = terms.carrierOfTerm(term);
            return order == null ? null : rangeOf(order.whereItStops());
        };
    }

    private static ComputedNumber.Range rangeOf(NumericDomain.Bounds bounds) {
        return bounds == null ? ComputedNumber.Range.ANY : new ComputedNumber.Range(
                bounds.min() == null ? null : Count.number(bounds.min().at()).exactly(),
                bounds.max() == null ? null : Count.number(bounds.max().at()).exactly());
    }

    /** The range of {@code bounds} inside where {@code order} stops. */
    private static ComputedNumber.Range within(NumericDomain.Bounds bounds,
                                               NumericDomain.Bounds order) {
        ComputedNumber.Range own = rangeOf(bounds);
        ComputedNumber.Range stops = rangeOf(order);
        ExactRatio low = own.low() == null ? stops.low() : stops.low() == null ? own.low()
                : own.low().compareTo(stops.low()) >= 0 ? own.low() : stops.low();
        ExactRatio high = own.high() == null ? stops.high() : stops.high() == null ? own.high()
                : own.high().compareTo(stops.high()) <= 0 ? own.high() : stops.high();
        return new ComputedNumber.Range(low, high);
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
     * who settled it would have named. A number whose arithmetic aborts at the places it is given
     * ({@link ComputedNumber#comesTo}) is the answer of no run, and nothing is settled at it.
     *
     * <p>For a caller that settles one state's places many times and has asked which numbers there
     * are once.
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
                    out = ConstraintState.settling(out, each.atom(), at.get(), each.space());
                    done.add(each.atom());
                    moved = true;
                }
            }
        }
        return out;
    }

    /** A number the rules write as arithmetic over places, and how its values are spaced. */
    record Computed(FactSubject atom, ComputedNumber number, NumberSpace space) {}

    /**
     * The numbers {@code state} holds that are arithmetic over places.
     *
     * <p>Settling a place states an equality on an atom the state already has, so the atoms are
     * the same whatever is settled and one reading of them serves every settling.
     */
    static List<Computed> in(ConstraintState<FactSubject> state,
                             Function<Term, ComputedNumber.Range> orders) {
        NumericDomain<FactSubject> domain = state.numbers();
        List<Computed> out = new ArrayList<>();
        for (FactSubject atom : domain.atomsSpokenOf()) {
            ComputedNumber number =
                    ComputedNumber.of(atom.identity(), ComputedNumbers::aPlace, orders);
            NumberSpace space = domain.spaceOf(atom);
            if (number != null && space != null) {
                out.add(new Computed(atom, number, space));
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
