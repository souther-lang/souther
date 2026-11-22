package souther.compiler.query;

import souther.compiler.observe.Figure;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * Whether one behavior is left unmeasured for its author to change first, and what to change.
 *
 * <p>A behavior whose measuring runs into a figure is dear to measure and is not measured whole
 * for it: what is past the figure is said not to be read. Where its author is told a change that
 * takes it out of the figure's way, the change is what they act on and the rest is not waited for,
 * so the body is left unread ({@link souther.compiler.partition.BodyReading.ToBeChangedFirst}) and
 * the other behaviors are measured.
 *
 * <p><b>Both halves, and neither alone.</b> A behavior no change is told for is measured as far as
 * it goes, however long: waiting is the only way to what its rows do not cover. And one told a
 * change that runs into no figure is measured, so that its author is told what its rows do not
 * cover as well. What is told is told of how the values and the applications are written, which is
 * the most they may come to ({@link ConditionsReadThroughTooManyChoices},
 * {@link HelpersReadOnApplicationsAroundThem}); what measuring runs into turns on what they
 * multiply to on the way down, and is told of reading the body
 * ({@link Adequacy.WhatStopsMeasuring}).
 *
 * <p>Asked only where the build leaves such behaviors ({@link Adequacy.LeavingWhatIsToBeChanged}).
 *
 * @param name     the module
 * @param behavior the behavior
 */
public record ToBeChangedFirst(String name, String behavior)
        implements Key<ToBeChangedFirst.Left> {

    /**
     * What is left for the author to change, or {@link #NOTHING}.
     *
     * @param figure  the figure measuring the behavior as written runs into; empty where the
     *                behavior is measured
     * @param choices what to declare so that no condition is read through too many choices
     * @param helpers the helpers to declare so that their comparisons are read once each
     */
    public record Left(Optional<Figure> figure, WhatToDeclare choices,
                       List<HelpersReadOnApplicationsAroundThem.Told> helpers) {

        /** The behavior is measured. */
        public static final Left NOTHING =
                new Left(Optional.empty(), WhatToDeclare.NOTHING, List.of());

        public Left {
            Objects.requireNonNull(figure, "measuring runs into a figure or does not");
            Objects.requireNonNull(choices, "what to declare for the choices, if nothing nothing");
            helpers = List.copyOf(helpers);
            if (figure.isPresent() && choices.conditions() == 0 && helpers.isEmpty()) {
                throw new IllegalArgumentException("a behavior is left for a change that is told");
            }
        }
    }

    @Override
    public String module() {
        return name;
    }

    @Override
    public Answer<Left> compute(Db db) {
        if (!Adequacy.leavesWhatIsToBeChanged(db) || !Adequacy.chosen(db, name, behavior)) {
            return Answer.of(Left.NOTHING);
        }
        WhatToDeclare choices = db.ask(new ConditionsReadThroughTooManyChoices(name, behavior))
                .value();
        List<HelpersReadOnApplicationsAroundThem.Told> helpers =
                db.ask(new HelpersReadOnApplicationsAroundThem(name, behavior)).value();
        // Both read off the one walk of the body, so neither is answered without the other.
        if (choices == null || helpers == null
                || (choices.conditions() == 0 && helpers.isEmpty())) {
            return Answer.of(Left.NOTHING);
        }
        Optional<Figure> figure = db.ask(new Adequacy.WhatStopsMeasuring(name, behavior)).value();
        return Answer.of((figure == null || figure.isEmpty()) ? Left.NOTHING
                : new Left(figure, choices, helpers));
    }
}
