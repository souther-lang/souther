package souther.compiler.crossing;

import souther.compiler.hash.SaysWhatStandsForIt;

/**
 * A value a collection may hold, whose equality is the equality of the one thing it names.
 *
 * <p>The stronger of the two claims a value can make about being held in a collection.
 * {@link ObjectEqualityIsTheCrossingAnswer} says that what a set does with it answers what a
 * comparison of two builds would; this says what that answer is over — the value
 * {@link SaysWhatStandsForIt#standsFor()} names — so what was the writer's word becomes something a
 * reading can walk and refuse.
 *
 * <p>More than the walk over values is owed elsewhere. Naming what may be followed in a value's
 * place is asked one way for the walk that proves a number is taken from values: two equal values
 * name equal things, and a value told apart by more is free to name the less. Held in a collection,
 * a value told apart by more than what it names is one the collection tells apart and this
 * comparison does not, which is the thing being refused. So the two are one here.
 *
 * <p>For a value with something inside. A closed set of cases has nothing to name and says the
 * weaker thing.
 */
public interface ObjectEqualityIsRepresentedByWhatItStandsFor
        extends ObjectEqualityIsTheCrossingAnswer, SaysWhatStandsForIt {
}
