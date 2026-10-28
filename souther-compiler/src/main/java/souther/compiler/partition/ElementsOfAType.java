package souther.compiler.partition;

import souther.compiler.check.FieldDomains;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * The values a list may be grown by at a position of one element type when no row ran that type:
 * what the compiler stands for the type with, as the type's own decoder builds it, and the whole
 * numbers beside those.
 *
 * <p>These are proposals and not observations, so they are kept apart from
 * {@link InputsRowsRanWith}: whether one of them answers, and answers differently, is what running
 * the candidate says. A value is what {@link Generator.CandidateCheck#builtAlone} makes of the
 * fixture that stands for the type, so a type the decoder builds is offered whatever it is, and one
 * it does not build on its own (an optional, a tuple) or a check with no runtime offers nothing.
 * The unit steps are for the numbers: a representative that is the identity of the body's
 * arithmetic (0 for a sum) tells it from a constant at no element, and a value a unit away does.
 */
final class ElementsOfAType {

    private ElementsOfAType() {}

    /** The representatives of {@code element}, then the numbers a unit from each. */
    static List<ObservedValue> of(MeasuredInput subject, Generator.CandidateCheck check,
                                  Type element) {
        List<ObservedValue> out = new ArrayList<>();
        for (FixtureTemplate each : subject.representativesHolding(element,
                FieldDomains.ConstructionLimits.NONE).values()) {
            check.builtAlone(element, each).filter(value -> !out.contains(value))
                    .ifPresent(out::add);
        }
        List<ObservedValue> stood = List.copyOf(out);
        for (ObservedValue each : stood) {
            for (Iterator<ObservedValue> near = NearbyValues.oneUnitFrom(each, element,
                    subject.ruleReading()); near.hasNext(); ) {
                ObservedValue value = near.next();
                if (!out.contains(value)) {
                    out.add(value);
                }
            }
        }
        return List.copyOf(out);
    }
}
