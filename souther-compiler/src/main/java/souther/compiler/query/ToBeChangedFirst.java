package souther.compiler.query;

import souther.compiler.meaning.AHelperReadOnApplicationsAroundIt;
import souther.compiler.observe.Figure;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * Whether one behavior is left unmeasured for its author to change first, and what to change.
 *
 * <p>A behavior whose measuring stops at a figure is not measured whole for it: what is past the
 * figure is said not to be read, however long the rest is waited for. Where what it stopped in is a
 * construct its author is told a change of, the change is what they act on, so the measuring ends
 * there: the body is left unread
 * ({@link souther.compiler.partition.BodyReading.ToBeChangedFirst}) and the other behaviors are
 * measured.
 *
 * <p><b>What stopped is what the change is told of.</b> What is told is told of how values and
 * applications are written, which is the most they may come to
 * ({@link ConditionsReadThroughTooManyChoices}, {@link HelpersReadOnApplicationsAroundThem}), so it
 * shows no stop; and a stop at a construct nothing is told of is answered by no change. A behavior
 * is left on neither, and on both only of one construct: measured as far as it goes otherwise,
 * however long.
 *
 * <p>A condition is read before anything is asked of the ways to it
 * ({@link Adequacy.ConditionsReadToAStop}), and where its lines decide is asked once they are known,
 * in dividing the body ({@link Adequacy.Dividing}); each says the stop the reader that spent the
 * figure says. The search for rows comes after both and is asked for neither, and a figure met
 * there ends nothing.
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
     * @param figure  the figure measuring the behavior as written stopped at; empty where the
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
            Objects.requireNonNull(figure, "measuring stopped at a figure or did not");
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

    /**
     * The conditions of the body told to be read through too many choices. None where the build
     * leaves nothing, or does not measure the behavior.
     */
    static Set<ModelOccurrence> throughTooManyChoices(Db db, String name, String behavior) {
        return ConditionsReadThroughTooManyChoices.past(read(db, name, behavior));
    }

    /**
     * The constructs of the body a change told of takes out of the figures' way: the conditions
     * read through too many choices, and every comparison written in a helper that is told to be
     * declared as a behavior, which leaves none of them in the body. None where the build leaves
     * nothing, or does not measure the behavior.
     */
    static Set<ModelOccurrence> told(Db db, String name, String behavior) {
        List<AComparisonRead> read = read(db, name, behavior);
        List<HelpersReadOnApplicationsAroundThem.Told> helpers = read.isEmpty() ? List.of()
                : db.ask(new HelpersReadOnApplicationsAroundThem(name, behavior)).value();
        Set<ModelOccurrence> out =
                new LinkedHashSet<>(ConditionsReadThroughTooManyChoices.past(read));
        if (helpers != null && !helpers.isEmpty()) {
            Set<ValueName.Helper> declared = new LinkedHashSet<>();
            helpers.forEach(each -> declared.add(each.named().helper()));
            read.stream().map(AComparisonRead::copy)
                    .filter(copy -> AHelperReadOnApplicationsAroundIt.writtenIn(copy)
                            .filter(declared::contains).isPresent())
                    .forEach(out::add);
        }
        return out;
    }

    private static List<AComparisonRead> read(Db db, String name, String behavior) {
        if (!Adequacy.leavesWhatIsToBeChanged(db) || !Adequacy.chosen(db, name, behavior)) {
            return List.of();
        }
        List<AComparisonRead> read = db.ask(new Adequacy.ComparisonsRead(name, behavior)).value();
        return read == null ? List.of() : read;
    }

    @Override
    public Answer<Left> compute(Db db) {
        // Dividing the body is where the measuring ends, so a body no change is told of is not
        // divided for this.
        Adequacy.BodyDivided divided = told(db, name, behavior).isEmpty() ? null
                : db.ask(new Adequacy.Dividing(name, behavior)).value();
        Optional<Figure> figure = divided == null ? Optional.empty() : divided.leftAt();
        if (figure.isEmpty()) {
            return Answer.of(Left.NOTHING);
        }
        WhatToDeclare choices = db.ask(new ConditionsReadThroughTooManyChoices(name, behavior))
                .value();
        List<HelpersReadOnApplicationsAroundThem.Told> helpers =
                db.ask(new HelpersReadOnApplicationsAroundThem(name, behavior)).value();
        return Answer.of(new Left(figure,
                choices == null ? WhatToDeclare.NOTHING : choices,
                helpers == null ? List.of() : helpers));
    }
}
