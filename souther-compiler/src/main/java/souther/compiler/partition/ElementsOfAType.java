package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * The values a list may be grown by at a position of one element type when no row ran that type:
 * what the compiler stands for the type with, that with one more element where the type is a
 * collection, and the numbers a unit away from those.
 *
 * <p>Every value is one the compiler already knows how to make, asked for once for the type and
 * built by the type's own decoder ({@link Generator.CandidateCheck#builtAlone}). Nothing here walks
 * the structure of a type: what stands for a type, and what stands for a collection of one of it
 * ({@link Witnesses#ofSize}), are the proposals' own, with their bounds and their guard against a
 * type that holds itself, so the work done is the work of those and does not grow with how deep
 * the type goes. A type the decoder does not build on its own (an optional, a tuple) or a check
 * with no runtime offers nothing.
 *
 * <p>The values beyond the representatives are for the ones that are the identity of the body's
 * arithmetic. A sum is the same at no element as at a zero, and a count of what the elements hold
 * is the same at an empty list as at none: a collection with an element in it, and a number a unit
 * away, are the values that tell the body from a constant.
 *
 * <p>These are proposals and not observations, so they are kept apart from
 * {@link InputsRowsRanWith}: whether one of them answers, and answers differently, is what running
 * the candidate says. What stopped the compiler building them is carried with them
 * ({@link Elements#met}), as {@link Proposals} carries it: a type whose values were not all built
 * is not one that has no others.
 */
final class ElementsOfAType {

    private ElementsOfAType() {}

    /**
     * What a list of {@code element} may be grown by, and what the building of it met.
     *
     * @param values the representatives of the element, then the same with one more element, then
     *               the numbers a unit from each
     * @param met    every stop met in building them, which a caller taking all of the values
     *               reached
     */
    record Elements(List<ObservedValue> values, CompositionShortfall met) {

        Elements {
            values = List.copyOf(values);
        }
    }

    /** What stands for a collection of one element of {@code type}; nothing where it is not a
     *  collection. */
    static Proposals withOneElement(Type type, RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        return view.shape() instanceof Shape.Sequence
                ? Witnesses.ofSize(view, 1, List.of(), reading, Set.of()) : Proposals.NONE;
    }

    /**
     * @param representatives what stands for a type, with what the building of it met
     * @param withOneElement  what stands for a collection of one element of a type, which is
     *                        nothing for a type that is not a collection
     * @param reading         how the rules of the types are read
     * @param check           what builds a value of a type from a fixture
     * @param element         the type of the elements of the list
     */
    static Elements of(Function<Type, Proposals> representatives,
                       Function<Type, Proposals> withOneElement, RuleReadingContext reading,
                       Generator.CandidateCheck check, Type element) {
        Set<ObservedValue> out = new LinkedHashSet<>();
        CompositionShortfall met = CompositionShortfall.NONE;
        for (Function<Type, Proposals> source : List.of(representatives, withOneElement)) {
            Proposals proposed = source.apply(element);
            for (FixtureTemplate each : proposed.values()) {
                check.builtAlone(element, each).ifPresent(out::add);
            }
            met = met.and(proposed.met());
        }
        for (ObservedValue each : List.copyOf(out)) {
            for (Iterator<ObservedValue> near = NearbyValues.oneUnitFrom(each, element, reading);
                 near.hasNext(); ) {
                out.add(near.next());
            }
        }
        return new Elements(new ArrayList<>(out), met);
    }
}
