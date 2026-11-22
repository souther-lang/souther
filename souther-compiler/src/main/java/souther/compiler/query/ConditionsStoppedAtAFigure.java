package souther.compiler.query;

import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.Figure;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.partition.BodyReading;
import souther.compiler.reading.WhatABodyStates;
import souther.compiler.types.ModelOccurrence;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * The conditions of one behavior's body some part of which was read no further at a figure that
 * counts how many times a condition is read, which figures those were, and what to declare so that
 * those conditions are read.
 *
 * <p>Read off what each condition states ({@link MeaningsOfABody}), whose parts nothing read say
 * the figure they stopped at: what stopped, whichever reader meets it. A condition told of in
 * several copies is one for each copy, as it is read once in each.
 *
 * <p>What to declare is told of these conditions, by which they are, and of no condition that was
 * read whole. It is told of each of them however few readings its choices may come to, since that
 * the reading stopped is what happened.
 *
 * @param name     the module
 * @param behavior the behavior
 */
public record ConditionsStoppedAtAFigure(String name, String behavior)
        implements Key<ConditionsStoppedAtAFigure.Stopped> {

    /**
     * What stopped.
     *
     * @param figures the figures, each once, in the order a report says them
     * @param declare what to declare, of the conditions that stopped
     */
    public record Stopped(List<Figure> figures, WhatToDeclare declare) {

        /** Nothing stopped at a figure. */
        public static final Stopped NOTHING = new Stopped(List.of(), WhatToDeclare.NOTHING);

        public Stopped {
            figures = List.copyOf(figures);
            Objects.requireNonNull(declare, "what to declare, if nothing stopped nothing");
        }

        /** How many conditions stopped. */
        public int conditions() {
            return declare.conditions();
        }
    }

    @Override
    public String module() {
        return name;
    }

    @Override
    public Answer<Stopped> compute(Db db) {
        Adequacy.ToDivide divided = Adequacy.toDivide(db, name, behavior, null);
        if (divided == null || !(divided.body() instanceof BodyReading.Read it)
                || it.analysis() == null) {
            return Answer.absent();
        }
        Set<ModelOccurrence> conditions = new LinkedHashSet<>();
        Set<Figure> figures = new LinkedHashSet<>();
        gather(WhatABodyStates.of(it.analysis(), divided.read().domain(), divided.read().rules(),
                db.readings().revision()), conditions, figures);
        if (conditions.isEmpty()) {
            return Answer.of(Stopped.NOTHING);
        }
        List<AComparisonRead> read = db.ask(new Adequacy.ComparisonsRead(name, behavior)).value();
        return Answer.of(new Stopped(Figure.inOrder(figures),
                WhatToDeclare.of(conditions, read == null ? List.of() : read)));
    }

    private static void gather(MeaningsOfABody body, Set<ModelOccurrence> conditions,
                               Set<Figure> figures) {
        body.stated().forEach((site, meaning) -> {
            if (site.part() == MeaningsOfABody.Part.Asked.ITSELF) {
                Set<Figure> met = Proposition.figuresOfReadingsIn(meaning.states());
                if (!met.isEmpty()) {
                    conditions.add(site.construct());
                    figures.addAll(met);
                }
            }
        });
        body.applications().values().forEach(each -> gather(each, conditions, figures));
    }
}
