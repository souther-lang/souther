package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactRatio;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * A count of the elements of a container meeting a statement that holds of another container: that
 * some entry of it is keyed by the element, or that some element of it is the element's value.
 *
 * <p>Whether an element meets such a statement is not the element's to say. It is what the other
 * container holds, and that is composed after the counted one, out of what the counted one was
 * built as — so how many elements meet it is chosen, and handed on as what the other container is
 * to hold for each of them ({@link ContentsAsked}).
 *
 * <p>Chosen two ways and no others: every element meeting it, where the count asked is not none, and
 * none of them meeting it, where none is a count asked. A count met by some elements and not by
 * others is a container whose elements the other one holds for some and not the rest, which this
 * does not write; so a container this composes nothing for is said as written some of, and never as
 * the model leaving nothing ({@link CompositionRepertoire#ELEMENTS_CHOSEN_FOR_A_COUNT}).
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
     * Whether the elements of a container composed at one of {@code counts} are to meet none of
     * the statements counted, rather than every one: where none is one of the counts.
     *
     * <p>The one place this is decided, for what composes the counted container and for what
     * hands the other one its contents, so that the two compose one row.
     */
    static boolean metByNone(LevelRegion counts) {
        return counts.contains(new Level.OfTheQuantity(ExactRatio.ZERO));
    }

    /**
     * What the other container is asked for each element of the counted one, where the elements
     * are to meet the statement — or are to meet none of it, {@code byNone}.
     */
    ContentsAsked.Asked asked(boolean byNone) {
        // Holding the value meets the statement where it holds there, and so does holding none
        // equal to it where it holds there; meeting none of it is the other of the two.
        boolean holding = holdsWhere != byNone;
        return new ContentsAsked.Asked(other, value, holding, ofTheKey,
                Optional.of(new ContentsAsked.Around(counted, false)));
    }

    /**
     * What every count among {@code asked} that hands its statement on asks of the other
     * container, at the counts each is asked for.
     */
    static List<ContentsAsked.Asked> askedOf(Map<RealizationTarget, AskedAt> asked) {
        List<ContentsAsked.Asked> out = new ArrayList<>();
        asked.forEach((target, at) -> {
            if (target instanceof RealizationTarget.ACount count) {
                of(count.count().container(), count.count().meeting()).ifPresent(handed ->
                        out.add(handed.asked(metByNone(at.about().values()))));
            }
        });
        return out;
    }
}
