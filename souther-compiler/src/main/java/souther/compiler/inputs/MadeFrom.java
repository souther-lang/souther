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
 * no narrowing to a case, and no join with the answer of a walk after where a value stands. The
 * walk itself reads a field off a place the values came from through what keeps them, and reads none
 * through a payload, which an operation may have made of other values: a field of a record made of
 * an element is not a field of the element. A reader that wants a place a rule is drawn at asks
 * {@link InputReads#pathOf} ({@link ValuesAt}).
 *
 * <p>The walk crosses every edge the walk after a position crosses, and the edges where elements
 * are made of others as well. So the places an expression stands at are among the places here, and
 * a reader that needs where a rule about it is owed asks this answer: one that took the position
 * alone, for an expression that may stand at one of several places, left out every container the
 * same name was made of.
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
