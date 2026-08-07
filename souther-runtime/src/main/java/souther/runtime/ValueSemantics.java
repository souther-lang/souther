package souther.runtime;

import org.jspecify.annotations.Nullable;

/**
 * Souther's value semantics for a type whose Java {@code equals} and {@code hashCode} belong to a
 * JDK contract it cannot break.
 *
 * <p>A {@link PersistentVector} is a {@code java.util.List}, so its {@code equals} must accept any
 * other List and compare elements the way that interface says. Were it to compare them the way the
 * language does, two lists holding the same amounts would answer differently depending on which side
 * was asked — {@code a.equals(b)} true and {@code b.equals(a)} false — because the JDK list on the
 * other side compares its elements with their own {@code equals}. A Set and a Map are in the same
 * position. Those three keep their JDK equality and carry the language's here instead.
 *
 * <p>Everything else — a generated data class, a newtype, an {@link Option}, a {@link Tuple} — only
 * ever compares with its own type, so there is no foreign implementation to disagree with and no
 * contract to keep. Their {@code equals} and {@code hashCode} are the language's directly.
 */
public interface ValueSemantics {

    /** Whether {@code other} is the same Souther value as this one. */
    boolean valueEquals(@Nullable Object other);

    /** A hash that agrees with {@link #valueEquals}. */
    int valueHash();
}
