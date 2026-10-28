package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
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
 * what the compiler stands for the type with, as the type's own decoder builds it, the numbers a
 * unit away, and those values with one more element in a list they hold.
 *
 * <p>These are proposals and not observations, so they are kept apart from
 * {@link InputsRowsRanWith}: whether one of them answers, and answers differently, is what running
 * the candidate says. A value is what {@link Generator.CandidateCheck#builtAlone} makes of the
 * fixture that stands for the type, so a type the decoder builds is offered whatever it is, and one
 * it does not build on its own (an optional, a tuple) or a check with no runtime offers nothing.
 *
 * <p>The steps beyond the representatives are for the values that are the identity of the body's
 * arithmetic. A sum is the same at no element as at a zero, and a count of what the elements hold
 * is the same at an empty list as at none: a number a unit away and a list with one element more
 * are the values that tell the body from a constant. The second is asked of the element's own
 * element type, and a type already being expanded is not asked again.
 *
 * <p>What stopped the compiler building the type's values is carried with them
 * ({@link Elements#met}), as {@link Proposals} carries it: a type whose values were not all built
 * is not one that has no others.
 */
final class ElementsOfAType {

    private ElementsOfAType() {}

    /**
     * What a list of {@code element} may be grown by, and what the building of it met.
     *
     * @param values the representatives of the element, then the numbers a unit from each, then
     *               each with one more element
     * @param met    every stop met in building them, which a caller taking all of the values
     *               reached
     */
    record Elements(List<ObservedValue> values, CompositionShortfall met) {

        Elements {
            values = List.copyOf(values);
        }
    }

    /**
     * @param representatives what stands for a type, with what the building of it met
     * @param reading         how the rules of the types are read
     * @param check           what builds a value of a type from a fixture
     * @param element         the type of the elements of the list
     */
    static Elements of(Function<Type, Proposals> representatives, RuleReadingContext reading,
                       Generator.CandidateCheck check, Type element) {
        return of(representatives, reading, check, element, Set.of());
    }

    private static Elements of(Function<Type, Proposals> representatives,
                               RuleReadingContext reading, Generator.CandidateCheck check,
                               Type element, Set<Type> expanding) {
        Proposals proposed = representatives.apply(element);
        Set<ObservedValue> out = new LinkedHashSet<>();
        for (FixtureTemplate each : proposed.values()) {
            check.builtAlone(element, each).ifPresent(out::add);
        }
        List<ObservedValue> stood = List.copyOf(out);
        for (ObservedValue each : stood) {
            for (Iterator<ObservedValue> near = NearbyValues.oneUnitFrom(each, element, reading);
                 near.hasNext(); ) {
                out.add(near.next());
            }
        }
        List<CompositionShortfall> met = new ArrayList<>(List.of(proposed.met()));
        if (!expanding.contains(element)) {
            Set<Type> inside = new LinkedHashSet<>(expanding);
            inside.add(element);
            for (ObservedValue each : stood) {
                NearbyValues.grown(each, element, reading, InputsRowsRanWith.NONE,
                        inner -> {
                            Elements within = of(representatives, reading, check, inner, inside);
                            met.add(within.met());
                            return within.values();
                        }).forEachRemaining(out::add);
            }
        }
        CompositionShortfall all = CompositionShortfall.NONE;
        for (CompositionShortfall each : met) {
            all = all.and(each);
        }
        return new Elements(List.copyOf(out), all);
    }
}
