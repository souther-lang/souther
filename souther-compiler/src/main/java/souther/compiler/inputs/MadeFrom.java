package souther.compiler.inputs;

import java.util.List;
import java.util.Objects;

/**
 * Where the values of an expression came from, which is not where the expression stands.
 *
 * <p>The answer of the walks after where a value came from ({@link InputReads#cameFrom}) and after
 * what it was worked out of ({@link InputReads#madeOf}). Those walks go through what makes other
 * values of the elements of a list, so a place named here is a place the expression's values were
 * made from. A rule about the expression is about that place; the expression is not the values
 * there.
 *
 * <p>So what only a position allows is not offered: no step into a field or an element of a place,
 * no narrowing to a case, and no join with the answer of a walk after where a value stands. A field
 * of a value is the answer for the value: a field of a record made of an element is not a field of
 * the element, and a place that is one is said by the walk after where the values stand, with its
 * field ({@link ValuesAt}), which a reader that wants a place a rule is drawn at asks
 * ({@link InputReads#pathOf}).
 *
 * <p><b>The two are said together by a reader whose expression stands at one of several places.</b>
 * What it stands at is the position's to say, and what it was made out of beyond that is this
 * answer's ({@link #placesBeyond}). Either alone leaves out the other: a reader that took only the
 * places the expression may stand at left out every container the same name was made of.
 *
 * <p>Made from the answer of those walks by {@link InputReads}, which owns them.
 */
public sealed interface MadeFrom {

    /** The expression's values came from this place, on every run. */
    record FromOne(TermPath place) implements MadeFrom {

        public FromOne {
            Objects.requireNonNull(place, "a value that came from a place came from somewhere");
        }
    }

    /**
     * The expression's values came from one of these places, the one the run is on, and nothing here
     * says which.
     */
    record FromOneOf(List<TermPath> among) implements MadeFrom {

        public FromOneOf {
            among = List.copyOf(among);
            if (among.isEmpty()) {
                throw new IllegalArgumentException("a value that came from one of several has some");
            }
        }
    }

    /** The expression was worked out of every place of one of the alternatives, the one the run is
     *  on. */
    record FromEvery(List<List<TermPath>> alternatives) implements MadeFrom {

        public FromEvery {
            alternatives = alternatives.stream().map(List::copyOf).toList();
            if (alternatives.isEmpty() || alternatives.stream().anyMatch(List::isEmpty)) {
                throw new IllegalArgumentException("a value made of places is made of some");
            }
        }

        /** Every place the value is made of on some run, once each. */
        @Override
        public List<TermPath> places() {
            return alternatives.stream().flatMap(List::stream).distinct().toList();
        }
    }

    /** The values came from no place the walk follows. */
    record FromNothing() implements MadeFrom {}

    /**
     * The places the values came from that what stands says nothing of: those no place of
     * {@code stands} is at or under. A place the expression stands at is said, with its field, by
     * the position; what came from the whole of a container the expression stands at an element of
     * is the same container, and adds nothing.
     */
    default List<TermPath> placesBeyond(ValuesAt stands) {
        List<TermPath> said = stands.places();
        return places().stream()
                .filter(each -> said.stream().noneMatch(there -> there.isAtOrUnder(each)))
                .toList();
    }

    /** Every place the values came from on some run, once each; none for {@link FromNothing}. */
    default List<TermPath> places() {
        return switch (this) {
            case FromOne(var place) -> List.of(place);
            case FromOneOf(var among) -> among;
            case FromEvery every -> every.places();
            case FromNothing _ -> List.of();
        };
    }
}
