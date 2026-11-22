package souther.compiler.query;

import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.Figure;
import souther.compiler.partition.BodyReading;
import souther.compiler.reading.WhatABodyStates;
import souther.compiler.types.ModelOccurrence;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The comparisons of one behavior's body some part of which was read no further at a figure of
 * this compiler's work, and which figures those were.
 *
 * <p>Read off what each comparison states ({@link MeaningsOfABody}), whose parts nothing read say
 * the figure they stopped at: what stopped, whichever reader meets it. A comparison told of in
 * several copies is one for each copy, as it is read once in each.
 *
 * @param name     the module
 * @param behavior the behavior
 */
public record ConditionsStoppedAtAFigure(String name, String behavior)
        implements Key<ConditionsStoppedAtAFigure.Stopped> {

    /**
     * What stopped.
     *
     * @param conditions how many comparisons
     * @param figures    the figures, each once, in the order a report says them
     */
    public record Stopped(int conditions, List<Figure> figures) {

        /** Nothing stopped at a figure. */
        public static final Stopped NOTHING = new Stopped(0, List.of());

        public Stopped {
            figures = List.copyOf(figures);
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
        return Answer.of(stoppedIn(WhatABodyStates.of(it.analysis(), divided.read().domain(),
                divided.read().rules(), db.readings().revision())));
    }

    /** What stopped among the comparisons of {@code body}, on every application of its closures. */
    static Stopped stoppedIn(MeaningsOfABody body) {
        Set<ModelOccurrence> conditions = new LinkedHashSet<>();
        Set<Figure> figures = new LinkedHashSet<>();
        gather(body, conditions, figures);
        return conditions.isEmpty() ? Stopped.NOTHING
                : new Stopped(conditions.size(), Figure.inOrder(figures));
    }

    private static void gather(MeaningsOfABody body, Set<ModelOccurrence> conditions,
                               Set<Figure> figures) {
        body.stated().forEach((site, meaning) -> {
            if (site.part() == MeaningsOfABody.Part.Asked.ITSELF) {
                Set<Figure> met = Proposition.figuresStoppedAtIn(meaning.states());
                if (!met.isEmpty()) {
                    conditions.add(site.construct());
                    figures.addAll(met);
                }
            }
        });
        body.applications().values().forEach(each -> gather(each, conditions, figures));
    }
}
