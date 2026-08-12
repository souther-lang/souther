package souther.compiler.check;

import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.Type;

import java.util.Objects;

/**
 * A {@code Map} key a behavior's boundary admitted, and what it is converted through.
 *
 * <p>It is a witness rather than a yes. Holding one means a key position established by a boundary
 * took this key: it has a representation, and the type it names is one a model declared. Classifying
 * a type answers only the first — {@link MapKeyRepresentation} is a fact about the type and anyone
 * may work one out — so a value of that kind is not evidence of anything a reader below the check
 * can act on. This is, which is why it is made in one place: {@link SignatureBoundary}, where a key
 * position is admitted.
 *
 * <p>Both questions used to be one type, and the split is what the second was hiding. A key position
 * a fixture or a data field establishes is not a boundary, and each decides what it takes; the
 * representation is what they share, and the admission is what they do not.
 */
public final class BoundaryMapKey {

    private final MapKeyRepresentation representation;

    BoundaryMapKey(MapKeyRepresentation representation) {
        this.representation = Objects.requireNonNull(representation);
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
        return other instanceof BoundaryMapKey k && representation.equals(k.representation);
    }

    @Override
    public int hashCode() {
        return representation.hashCode();
    }

    @Override
    public String toString() {
        return "BoundaryMapKey[" + representation + "]";
    }
}
