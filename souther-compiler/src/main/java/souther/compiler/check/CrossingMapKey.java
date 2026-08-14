package souther.compiler.check;

import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.Type;

import java.util.Objects;

/**
 * A {@code Map} key admitted where an external representation crosses, and what it is converted
 * through.
 *
 * <p>It is a witness rather than a yes. Holding one means a position that crosses took this key: it
 * has a representation, and where it names a type that name is one a model declares. Classifying a
 * type answers only the first — {@link MapKeyRepresentation} is a fact about the type and anyone may
 * work one out — so a value of that kind is not evidence of anything a reader below can act on. This
 * is.
 *
 * <p>The two questions stay two. A key with no representation and a key naming the language's own
 * vocabulary are refused for different reasons, and the position that asked words each of them: a
 * behavior's parameter and a data's field say the same thing about a different subject. What they
 * share is {@link CrossingNominal}, which a named key holds rather than re-establishes — so a key
 * cannot be admitted by a walk that forgot whose vocabulary the name is.
 *
 * <p>A fixture's key position is not one of these. A fixture writes what a row states and crosses
 * nothing, so it decides what it takes on its own; the representation is what it shares with a
 * position that crosses, and the admission is what it does not.
 */
public final class CrossingMapKey {

    private final MapKeyRepresentation representation;

    private CrossingMapKey(MapKeyRepresentation representation) {
        this.representation = Objects.requireNonNull(representation);
    }

    /** A key written as its own leaf's text, which names no type and so admits nothing. */
    public static CrossingMapKey lexical(MapKeyRepresentation.Lexical representation) {
        return new CrossingMapKey(representation);
    }

    /**
     * A key that goes through a named type's own codec.
     *
     * <p>Made from the admission rather than beside it: the representation is built here from the
     * name the walk admitted, so there is no pair of a witness and a name for a caller to get wrong.
     */
    public static CrossingMapKey named(CrossingNominal admitted) {
        return new CrossingMapKey(new MapKeyRepresentation.NamedKey(admitted.name()));
    }

    /** What the key is converted through, which is what a decoder and an encoder are built from. */
    public MapKeyRepresentation representation() {
        return representation;
    }

    /** The type in the language this key has — what the map it keys is a map of. */
    public Type type() {
        return representation.type();
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof CrossingMapKey k && representation.equals(k.representation);
    }

    @Override
    public int hashCode() {
        return representation.hashCode();
    }

    @Override
    public String toString() {
        return "CrossingMapKey[" + representation + "]";
    }
}
