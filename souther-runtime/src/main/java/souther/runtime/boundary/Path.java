package souther.runtime.boundary;

import org.jspecify.annotations.Nullable;
import souther.runtime.PersistentVector;

import java.util.List;
import java.util.Objects;

/**
 * Where in the input a refusal is: the steps from the root to it, each a member's name or an
 * element's index, written as a JSON Pointer (RFC 6901) by {@link #toJsonPointer} (spec
 * {@code [#decoder-error]}).
 *
 * <p>A step keeps what it was. The member {@code 0} and the element at index 0 are two steps, though a
 * JSON Pointer writes both as {@code /0}, so a library whose paths tell them apart is handed each as
 * what it is. A member's name is kept as it was read, so the member {@code a/b} and the member
 * {@code b} of {@code a} are two paths: {@code /a~1b} and {@code /a/b}.
 */
public final class Path {

    /** One step of a path. */
    public sealed interface Segment {

        /** The step as a JSON Pointer writes it, before {@code ~} and {@code /} are escaped. */
        String text();

        /** The member {@code name} of an object. */
        record Member(String name) implements Segment {
            public Member {
                Objects.requireNonNull(name);
            }

            @Override
            public String text() {
                return name;
            }
        }

        /** The element at {@code index} of an array. */
        record Element(int index) implements Segment {
            @Override
            public String text() {
                return Integer.toString(index);
            }
        }
    }

    /** The input itself. */
    public static final Path ROOT = new Path(PersistentVector.empty());

    private final PersistentVector<Segment> segments;

    private Path(PersistentVector<Segment> segments) {
        this.segments = segments;
    }

    /** The member {@code name} of what this path names. */
    public Path append(String name) {
        return new Path(segments.append(new Segment.Member(name)));
    }

    /** The element at {@code index} of what this path names. */
    public Path append(int index) {
        return new Path(segments.append(new Segment.Element(index)));
    }

    /** The steps from the root, in order. */
    public List<Segment> segments() {
        return segments;
    }

    /** This path as RFC 6901 writes it: {@code ""} for the root, and {@code ~} and {@code /} inside a
     *  segment written {@code ~0} and {@code ~1}. */
    public String toJsonPointer() {
        StringBuilder sb = new StringBuilder();
        for (Segment s : segments) {
            sb.append('/').append(s.text().replace("~", "~0").replace("/", "~1"));
        }
        return sb.toString();
    }

    @Override
    public String toString() {
        return toJsonPointer();
    }

    @Override
    public boolean equals(@Nullable Object o) {
        return o instanceof Path other && segments.equals(other.segments);
    }

    @Override
    public int hashCode() {
        return segments.hashCode();
    }
}
