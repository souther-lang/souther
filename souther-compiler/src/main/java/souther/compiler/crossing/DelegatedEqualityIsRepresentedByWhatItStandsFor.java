package souther.compiler.crossing;

import souther.compiler.hash.SaysWhatStandsForIt;

/**
 * A value whose delegated equality is the equality of the one thing it names, and nothing besides.
 *
 * <p>The stronger of the two claims. {@link DelegatedEqualityIsTheCrossingAnswer} says that leaving
 * this comparison to an equality answers what taking the value apart would have; this says what
 * that equality is over — the value {@link SaysWhatStandsForIt#standsFor()} names — so the claim
 * stops being only the writer's word. What is named can be walked by the rules the comparison uses
 * on everything else, and a part of it the comparison passes over, or reads by an answer of its
 * own, is that claim coming out false.
 *
 * <p><b>Which is more than the walk is owed.</b> Naming what may be followed in a value's place is
 * already asked of a value elsewhere, for the walk that proves a number is taken from values, and
 * what is asked there is one-way: two equal values name equal things, and a value told apart by
 * more than what it names is free to name the less. That is not enough here. A comparison left to
 * an equality that reads more than the representation does is a comparison reading more, and this
 * says the two are one.
 *
 * <p>For a value with something inside. A closed set of cases has nothing to name and says the
 * weaker thing.
 */
public interface DelegatedEqualityIsRepresentedByWhatItStandsFor
        extends DelegatedEqualityIsTheCrossingAnswer, SaysWhatStandsForIt {
}
