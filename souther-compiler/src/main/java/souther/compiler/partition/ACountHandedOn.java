package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;

/**
 * A count of the elements of a container meeting a statement that holds of another container: that
 * some entry of it is keyed by the element, or that some element of it is the element's value.
 *
 * <p>Whether an element meets such a statement is not the element's to say. It is what the other
 * container holds, and that is composed after the counted one, out of what the counted one was
 * built as — so how many elements meet it is chosen, and handed on as what the other container is
 * to hold for each of them ({@link ContentsAsked}).
 *
 * <p><b>Chosen once, off what the count is asked at.</b> Which count a container is composed at is
 * the number the search is walking ({@link AskedAt#walked}) — the one a caller named where it named
 * one — and not the numbers a search is about, which a walk of one number out of them says nothing
 * of the rest of. The counted container is composed with that many elements meeting the statement
 * and the other container is handed exactly that, both by {@link #counted} on the one value, so the
 * two compose one row.
 *
 * <p><b>The first so many meet it and the rest do not.</b> A container of more elements than are
 * counted holds the statement for its first elements, in the order it holds them, and its denial for
 * the others. Elements equal at what the other container is asked about cannot be on both sides, so
 * a container saying one value again is a container nothing builds the other one for, and the next
 * is tried.
 *
 * @param counted    the container whose elements are counted
 * @param other      the container the statement holds of
 * @param value      the position inside the counted element the other container is asked about
 * @param ofTheKey   whether the other container is asked about its keys rather than its elements
 * @param holdsWhere whether the statement holds where the other container holds the value, rather
 *                   than where it holds none equal to it
 */
record ACountHandedOn(TermPath counted, TermPath other, TermPath value, boolean ofTheKey,
                      boolean holdsWhere) {

    private static final int MOST_ELEMENTS =
            CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    ACountHandedOn {
        Objects.requireNonNull(counted, "a count is of the elements of some container");
        Objects.requireNonNull(other, "the statement holds of some container");
        Objects.requireNonNull(value, "the other container is asked about some position");
    }

    /**
     * What {@code meeting}, counted over the elements of {@code counted}, hands on — or nothing
     * where it is not a statement that some entry or element of another container is a value
     * inside the counted element.
     */
    static Optional<ACountHandedOn> of(TermPath counted, Proposition meeting) {
        if (!(meeting instanceof Proposition.Some(DecisionSubject.AnInput(TermPath other),
                Proposition.SameValue(DecisionSubject.AnInput(TermPath one),
                        DecisionSubject.AnInput(TermPath another), boolean same, var _),
                boolean holds, var _))
                || !same || other.isAtOrUnder(counted.element())
                || counted.isAtOrUnder(other.element())) {
            return Optional.empty();
        }
        for (boolean keyed : new boolean[] {true, false}) {
            TermPath inOther = keyed ? other.key() : other.element();
            TermPath value = one.equals(inOther) ? another : another.equals(inOther) ? one : null;
            if (value != null && value.isAtOrUnder(counted.element())
                    && !value.isAtOrUnder(other.element()) && !value.isAtOrUnder(other.key())) {
                return Optional.of(new ACountHandedOn(counted, other, value, keyed, holds));
            }
        }
        return Optional.empty();
    }

    /**
     * How many elements meet the statement in a container composed for {@code at}: the number a
     * caller named, where it named one, and otherwise the fewest the search walks — which is the
     * one every size of container the walk allows can be composed at. Nothing where the walk holds
     * no count up to the most elements a container for a count is composed with, which is that
     * figure stopping it: the composer says so ({@link CardinalityComposer}), and nothing is
     * handed on for a container it does not compose.
     */
    static OptionalInt counted(AskedAt at) {
        Place named = at.named();
        for (int count = 0; count <= MOST_ELEMENTS; count++) {
            Count place = Count.of(count);
            if (at.walking().holds(place, Carrier.WHOLE)
                    && (named == null || named.sameAs(place))) {
                return OptionalInt.of(count);
            }
        }
        return OptionalInt.empty();
    }

    /**
     * What the other container is asked for each element of the counted one, where the first
     * {@code count} elements meet the statement and the rest do not.
     */
    List<ContentsAsked.Asked> asked(int count) {
        List<ContentsAsked.Asked> out = new ArrayList<>();
        // Holding the value meets the statement where it holds there; holding none equal to it
        // meets its denial.
        if (count > 0) {
            out.add(new ContentsAsked.Asked(other, value, holdsWhere, ofTheKey, Optional.of(
                    new ContentsAsked.Around(counted, false, 0, count))));
        }
        out.add(new ContentsAsked.Asked(other, value, !holdsWhere, ofTheKey, Optional.of(
                new ContentsAsked.Around(counted, false, count, Integer.MAX_VALUE))));
        return out;
    }

    /**
     * What every count among {@code asked} that hands its statement on asks of the other
     * container, at the count each is composed at.
     */
    static List<ContentsAsked.Asked> askedOf(Map<RealizationTarget, AskedAt> asked) {
        List<ContentsAsked.Asked> out = new ArrayList<>();
        asked.forEach((target, at) -> {
            if (target instanceof RealizationTarget.ACount count) {
                of(count.count().container(), count.count().meeting()).ifPresent(handed ->
                        counted(at).ifPresent(meeting -> out.addAll(handed.asked(meeting))));
            }
        });
        return out;
    }
}
