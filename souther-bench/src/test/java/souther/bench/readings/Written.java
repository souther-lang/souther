package souther.bench.readings;

/**
 * A model written to be read by the walk that holds this compiler's stages apart, and by nothing
 * else.
 *
 * <p>Its own sums, not the compiler's. What the walk is given is which sum says what a module
 * wrote and which says what is built out of others, so a model with sums of its own asks it the
 * question it is really for: whether it derives those sets from the class files it was handed. A
 * fixture written in the compiler's own types would be a check of the compiler's spelling.
 */
public final class Written {

    private Written() {}

    /** What a module wrote, which is the thing a reader is not to reach for. */
    public sealed interface Declared permits Declared.Record, Declared.OneValue {

        /** A declaration with fields. */
        record Record(String name) implements Declared {

            /** Something to read off it, which is what reaching one is for. */
            public boolean holdsAnything() {
                return !name.isEmpty();
            }
        }

        /** A declaration of one value. */
        record OneValue(String name) implements Declared {}
    }

    /** A position's type: either something with nothing inside it, or something built of others. */
    public sealed interface Position permits Position.Leaf, Position.Built {

        /** Nothing inside it. A name read off one is a name and not a structure. */
        record Leaf(String name) implements Position {}

        /** Built out of others, which is what taking one apart reads. */
        sealed interface Built extends Position permits Built.OfOne, Built.OfTwo {

            record OfOne(Position element) implements Built {}

            record OfTwo(Position key, Position value, String label) implements Built {}
        }
    }

    /** Where a name is looked up, which is the one way to a declaration from a name alone. */
    public interface Names {

        Declared declaredNode(String name);
    }
}
