package souther.compiler.check;

import souther.compiler.hash.ValueHash;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

/**
 * The names read off a value one after another, held as the chain one name shorter and the name
 * read last.
 *
 * <p>A chain one name longer is made in one step and shares everything before that name with the
 * chain it was made from. A value is read at every name of a chain as deep as a chain of
 * declarations, and a chain held as a list of its names would be copied, hashed and compared over its
 * whole length each time it is made one longer — so naming each position of such a chain would cost
 * the square of the chain, and a reading naming the positions of every rule under it the cube.
 *
 * <p>The number it is asked for is worked out once, from the number of the chain before it and the
 * name, and kept. Both are values — the name is text — so the number is a function of the names and
 * of nothing else, the same as {@link Term}'s own.
 *
 * <p>Equal by the names, in order. Two chains made one from the other share what is before the
 * last name, so comparing them stops where the two meet; two made apart compare a name at a time.
 */
final class FieldPath {

    /** No names at all: the value itself. */
    static final FieldPath NONE = new FieldPath(null, null);

    private final FieldPath before;
    private final String last;
    private final int length;
    private final int hash;

    private FieldPath(FieldPath before, String last) {
        this.before = before;
        this.last = last;
        this.length = before == null ? 0 : before.length + 1;
        this.hash = before == null ? ValueHash.ofOnePart(FieldPath.class, 0)
                : ValueHash.ofItsParts(FieldPath.class, before.hash, last.hashCode());
    }

    /** {@code names}, the first read first. */
    static FieldPath of(List<String> names) {
        FieldPath out = NONE;
        for (String name : names) {
            out = out.then(name);
        }
        return out;
    }

    /** This with {@code name} read off it. */
    FieldPath then(String name) {
        return new FieldPath(this, Objects.requireNonNull(name, "a name is read"));
    }

    /**
     * This with {@code more} read off it.
     *
     * <p>The chain {@code more} is where this has no names, which is where a chain is read off the
     * value itself; otherwise its names are read on one at a time.
     */
    FieldPath then(FieldPath more) {
        if (length == 0) {
            return more;
        }
        FieldPath out = this;
        for (String name : more.names()) {
            out = out.then(name);
        }
        return out;
    }

    /** How many names. */
    int size() {
        return length;
    }

    boolean isEmpty() {
        return length == 0;
    }

    /** The names, the first read first. Written out each time it is asked for, so a reader that only
     *  needs how many there are, or the chain to extend, asks for those. */
    List<String> names() {
        String[] out = new String[length];
        FieldPath at = this;
        for (int i = length - 1; i >= 0; i--) {
            out[i] = at.last;
            at = at.before;
        }
        return Arrays.asList(out);
    }

    @Override
    public boolean equals(Object other) {
        if (!(other instanceof FieldPath that)) {
            return false;
        }
        FieldPath one = this;
        while (one != that) {
            if (one.hash != that.hash || one.length != that.length
                    || !Objects.equals(one.last, that.last)) {
                return false;
            }
            one = one.before;
            that = that.before;
        }
        return true;
    }

    @Override
    public int hashCode() {
        return hash;
    }

    @Override
    public String toString() {
        return String.join(".", names());
    }
}
