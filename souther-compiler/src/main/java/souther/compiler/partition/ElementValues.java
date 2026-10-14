package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

/**
 * The values an element of a container is listed at, and the two ways each is read: as part of a
 * row holding the container, and as the element alone.
 *
 * <p>Two readers list them: the composer choosing which values a container is made of
 * ({@link CardinalityComposer}), and the most a count of the elements comes to
 * ({@link HowManyCanMeet}). Both list them here under one figure, so a value one of them reads is
 * a value the other reads, and the figure says one thing about both.
 *
 * <p>The two ways of reading are two questions. A row holding the container holds those values
 * and no others, which is what a composed row is. The element alone holds one value and says
 * nothing of anything else — not of the other elements, not of the container, not of any other
 * position — so a statement read at it is told it could not walk anywhere but into the element,
 * and that reads as not being able to tell and never as failing. What a statement fails of there,
 * it fails of wherever the value stands.
 */
final class ElementValues {

    /** How many values of the element are listed before the listing stops. */
    private static final int MOST_VALUES =
            CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.maximum();

    /** The name the element alone is read under, as the one value a row of it holds. */
    private static final String ALONE = "element";

    private final TermPath container;
    private final Type element;
    private final RuleReadingContext reading;
    private final ValuesOfAnElement.Listed listed;

    private ElementValues(TermPath container, Type element, RuleReadingContext reading,
                          ValuesOfAnElement.Listed listed) {
        this.container = container;
        this.element = element;
        this.reading = reading;
        this.listed = listed;
    }

    /**
     * The values of {@code element}, the element of the container at {@code container}, as
     * {@link ValuesOfAnElement#of} lists them — or null where some part of the element is one
     * nothing here lists values of.
     *
     * @param numbersAt the values a number standing at a position is read at, or null where none
     *                  are chosen there
     */
    static ElementValues of(TermPath container, Type element, RuleReadingContext reading,
                            Function<TermPath, List<ObservedValue>> numbersAt) {
        ValuesOfAnElement.Listed listed = ValuesOfAnElement.of(element, container.element(),
                reading, MOST_VALUES, numbersAt);
        return listed == null ? null : new ElementValues(container, element, reading, listed);
    }

    /** How many values of one part of the element a caller may hand {@code numbersAt}: no more
     *  than are listed of the whole. */
    static int mostOfAPart() {
        return MOST_VALUES;
    }

    /** The values listed, and whether the figure stopped the listing. */
    ValuesOfAnElement.Listed listed() {
        return listed;
    }

    /**
     * A row holding {@code values} as the container, and nothing else.
     *
     * @param type the container's type, which is the parameter's: a row holds a parameter, so
     *             only a container that is one is held this way
     */
    BorderQuantity.Observation holding(Type type, List<ObservedValue> values) {
        if (!container.steps().isEmpty()) {
            throw new IllegalStateException("a row holding `" + container + "` alone holds the"
                    + " parameter it is, and it is inside one");
        }
        return new StandingAtAPoint.DiscoveringRow(
                new BehaviorInputs(List.of(container.head()), List.of(type), reading.source(),
                        reading.policy()),
                new ObservedInputs(List.of(new ObservedValue.Sequence(values)),
                        new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()));
    }

    /** The element alone, holding {@code value}. */
    BorderQuantity.Observation alone(ObservedValue value) {
        return new Alone(container.element(), new StandingAtAPoint.DiscoveringRow(
                new BehaviorInputs(List.of(ALONE), List.of(element), reading.source(),
                        reading.policy()),
                new ObservedInputs(List.of(value), new Generator.Watched.NoAccount(),
                        new AnswerObservation.NotAnswered())));
    }

    /**
     * A reading of one element, walked from the element: a path under it is read in the element,
     * and every other path could not be walked.
     *
     * @param element where the element stands in the input
     * @param within  the element read as a row of its own, under {@link #ALONE}
     */
    private record Alone(TermPath element, BorderQuantity.Observation within)
            implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            TermPath inside = inside(path);
            return inside == null ? WalkResult.couldNotWalk() : within.at(inside);
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            TermPath inside = inside(path);
            return inside == null ? WalkResult.couldNotWalk() : within.everyValueAt(inside);
        }

        /** The elements of a container inside the element, each read the same way. */
        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath of) {
            TermPath inside = inside(of);
            if (inside == null) {
                return WalkResult.couldNotWalk();
            }
            return switch (within.eachElementOf(inside)) {
                case WalkResult.CouldNotWalk<List<BorderQuantity.Observation>> _ ->
                        WalkResult.couldNotWalk();
                case WalkResult.Reached(List<BorderQuantity.Observation> each) -> {
                    List<BorderQuantity.Observation> out = new ArrayList<>();
                    each.forEach(one -> out.add(new Alone(element, one)));
                    yield WalkResult.reached(out);
                }
            };
        }

        /** {@code path} as the element's own row names it, or null where it is not inside the
         *  element. */
        private TermPath inside(TermPath path) {
            return path.isAtOrUnder(element) ? new TermPath(ALONE,
                    path.steps().subList(element.steps().size(), path.steps().size())) : null;
        }
    }
}
