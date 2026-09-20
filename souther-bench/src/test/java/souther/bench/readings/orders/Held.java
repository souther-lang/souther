package souther.bench.readings.orders;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.query.Weakening;

import java.util.Map;
import java.util.Set;

/**
 * What a copy made, in the shapes this compiler holds them in, for a reader to take an order off.
 *
 * <p>A model written to be read by the walk that follows an unordered copy, and by nothing else.
 * Made by {@code Set.copyOf} and {@code Map.copyOf}, so that what it hands back iterates in an
 * order the run decides, and of the kinds the readers of the real ones are written over: reasons
 * a search met, the terms of a form, and the causes a report folds.
 *
 * @param figures    a set of the figures a search is held to
 * @param named      a map from a name to one of them
 * @param terms      the terms of a form
 * @param weakenings the causes of a weakening
 */
public record Held(Set<CompositionBudget> figures, Map<String, CompositionBudget> named,
                   Set<NumericTerm> terms, Set<Weakening> weakenings) {

    public Held {
        figures = Set.copyOf(figures);
        named = Map.copyOf(named);
        terms = Set.copyOf(terms);
        weakenings = Set.copyOf(weakenings);
    }
}
