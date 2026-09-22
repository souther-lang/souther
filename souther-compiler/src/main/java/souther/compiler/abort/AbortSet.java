package souther.compiler.abort;

import java.util.EnumSet;
import java.util.Set;

/**
 * Every {@link AbortKind} one execution site can end without a value for.
 *
 * <p>A small immutable value, not a registry. What owns one — a {@code Core} site, a kernel, an
 * {@code ensures} crossing — is answered by whoever asks the question this rides back from; this
 * itself says only which reasons, and how many. Most sites answer {@link #NONE} or a single kind;
 * more than one is real too — {@code Int.truncatingDivide} answers with both
 * {@link AbortKind#DIVISION_BY_ZERO} and {@link AbortKind#ANSWER_HAS_NO_PLACE}, on a zero divisor
 * and on the one pair whose quotient no {@code Int} holds, which the specification treats as two
 * reasons.
 *
 * <p>Order carries no meaning — two kinds either sit at one site or they do not, and nothing asks
 * which was found first — so this is backed by an {@code EnumSet} and answers no orderable view of
 * itself, the way a {@link souther.compiler.core.KernelSignature}'s
 * {@code languageCaseMembers} does.
 */
public final class AbortSet {

    /** No reason: the site always answers a value or a business case, never neither. */
    public static final AbortSet NONE = new AbortSet(EnumSet.noneOf(AbortKind.class));

    private final EnumSet<AbortKind> kinds;

    private AbortSet(EnumSet<AbortKind> kinds) {
        this.kinds = kinds;
    }

    /** The kinds {@code first} and the rest of {@code more}, in no particular order and with no
     *  duplicate — a kind is either at this site or it is not. */
    public static AbortSet of(AbortKind first, AbortKind... more) {
        EnumSet<AbortKind> kinds = EnumSet.of(first, more);
        return new AbortSet(kinds);
    }

    /** {@code kinds}, or {@link #NONE} where it is empty — so a caller that built an empty
     *  collection gets the one instance answering no reason rather than a second one meaning the
     *  same thing. */
    public static AbortSet copyOf(Set<AbortKind> kinds) {
        if (kinds.isEmpty()) {
            return NONE;
        }
        return new AbortSet(EnumSet.copyOf(kinds));
    }

    /** Whether {@code kind} is a reason this site can end without a value for. */
    public boolean contains(AbortKind kind) {
        return kinds.contains(kind);
    }

    /** Whether this answers no reason at all. */
    public boolean isEmpty() {
        return kinds.isEmpty();
    }

    /** Every reason, as a set with no order to it. A caller wanting one written out sorts it as it
     *  wants to; nothing about the site prefers one order over another. */
    public Set<AbortKind> kinds() {
        return Set.copyOf(kinds);
    }

    /** {@code this} and {@code other} together — every reason either answers. Used where one site's
     *  answer is built from more than one sub-question, such as a kernel whose call can both take a
     *  zero divisor and overflow its answer. */
    public AbortSet union(AbortSet other) {
        if (other.isEmpty()) {
            return this;
        }
        if (this.isEmpty()) {
            return other;
        }
        EnumSet<AbortKind> merged = EnumSet.copyOf(this.kinds);
        merged.addAll(other.kinds);
        return new AbortSet(merged);
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof AbortSet that && this.kinds.equals(that.kinds);
    }

    @Override
    public int hashCode() {
        return kinds.hashCode();
    }

    @Override
    public String toString() {
        return kinds.toString();
    }
}
