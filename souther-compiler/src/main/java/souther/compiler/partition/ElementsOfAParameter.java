package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.List;
import java.util.function.Function;

/**
 * The values an element of a container written at a parameter is listed at, and the rows holding
 * some of them as that container and nothing else.
 *
 * <p>What a statement about one element answers of each value is read at such a row, and two
 * readers ask it: the composer choosing which values a container is made of
 * ({@link CardinalityComposer}), and the most a count of the elements comes to
 * ({@link HowManyCanMeet}). Both list the values here under one figure and walk the same rows, so
 * a value one of them reads is a value the other reads, and the figure says one thing about both.
 *
 * <p>A parameter and nothing inside one: a row holding the container alone is a row holding the
 * parameter, which is what makes it walkable with nothing else written.
 */
final class ElementsOfAParameter {

    /** How many values of the element are listed before the listing stops. */
    private static final int MOST_VALUES =
            CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.maximum();

    private final BehaviorInputs where;
    private final ValuesOfAnElement.Listed listed;

    private ElementsOfAParameter(BehaviorInputs where, ValuesOfAnElement.Listed listed) {
        this.where = where;
        this.listed = listed;
    }

    /**
     * The values of {@code element}, the element of the container {@code container} of
     * {@code type}, as {@link ValuesOfAnElement#of} lists them — or null where the container is
     * not a parameter, or some part of the element is one nothing here lists values of.
     *
     * @param numbersAt the values a number standing at a position is read at, or null where none
     *                  are chosen there
     */
    static ElementsOfAParameter of(TermPath container, Type type, Type element,
                                   RuleReadingContext reading,
                                   Function<TermPath, List<ObservedValue>> numbersAt) {
        if (!container.steps().isEmpty()) {
            return null;
        }
        ValuesOfAnElement.Listed listed = ValuesOfAnElement.of(element, container.element(),
                reading, MOST_VALUES, numbersAt);
        return listed == null ? null : new ElementsOfAParameter(new BehaviorInputs(
                List.of(container.head()), List.of(type), reading.source(), reading.policy()),
                listed);
    }

    /** The values listed, and whether the figure stopped the listing. */
    ValuesOfAnElement.Listed listed() {
        return listed;
    }

    /** A row holding {@code values} as the container, and nothing else. */
    BorderQuantity.Observation holding(List<ObservedValue> values) {
        return new StandingAtAPoint.DiscoveringRow(where, new ObservedInputs(
                List.of(new ObservedValue.Sequence(values)), new Generator.Watched.NoAccount(),
                new AnswerObservation.NotAnswered()));
    }
}
