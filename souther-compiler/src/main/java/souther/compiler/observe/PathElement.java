package souther.compiler.observe;

/**
 * One step from a value to a place inside it.
 *
 * <p>Where two values differ is said as the steps that reach it rather than as the text of a path.
 * A path spelled out is a reading of the values — which name a field goes by, how a key is written —
 * and a reader given only the text would have to take it apart to do anything but print it. The
 * steps say the same thing in the form the question was asked in, and whoever prints them decides
 * how a path is written for whoever is reading it.
 */
public sealed interface PathElement {

    /** Into the field of a construction. */
    record Field(String name) implements PathElement {

        public Field {
            if (name == null) {
                throw new IllegalArgumentException("a field step names a field");
            }
        }
    }

    /** Into an element of an ordered sequence, counted from zero. */
    record Index(int at) implements PathElement {

        public Index {
            if (at < 0) {
                throw new IllegalArgumentException("an element stands at zero or later: " + at);
            }
        }
    }

    /**
     * Into what a map holds under one key.
     *
     * <p>The key as it was stated, which is what says which entry this is: a map's entries are
     * matched by key rather than looked up by one, so the entry reached here is the one whose key
     * this is the same key as.
     */
    record Key(Asserted key) implements PathElement {

        public Key {
            if (key == null || !Limits.UNBOUNDED.admits(key)) {
                throw new IllegalArgumentException(
                        "a key that says which entry a difference is at is a value that is there");
            }
        }
    }
}
