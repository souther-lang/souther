package souther.compiler.coverage;

import souther.compiler.core.Core;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.util.Optional;

/**
 * One thing a node of a body settles on its own, as what it is.
 *
 * <p>Held as a sum rather than as whatever the node happened to have. What a node says varies by
 * node — a literal is a number here and an operator there — and a list of them under no type is a
 * value nothing downstream can be asked anything about: what reaches it is told it holds objects,
 * and a reader that wanted to know what a body does would have to know which node put what where.
 *
 * <p>Which is not only a matter of reading. {@link ExecutableIdentity} is part of what says a
 * recording is of these bodies, so it crosses everywhere a recording does — including the seam an
 * execution that is not this one's would be written against. Untyped, that seam asks such an
 * execution to know the compiler's own trees.
 */
public sealed interface Settled {

    /** The type the node was decided to have, which every one of them says. */
    record OfType(Type type) implements Settled {}

    /** A whole number written in the body. */
    record Whole(long value) implements Settled {}

    /** A decimal written in the body. */
    record Fraction(BigDecimal value) implements Settled {}

    /** A truth written in the body. */
    record Truth(boolean value) implements Settled {}

    /**
     * A word the body holds: text written in it, a field it reads or fills, the reason under an
     * {@code unreachable}, or the name an author put a departure under.
     *
     * <p>One arm for the several of them because they are one thing here — a word the source wrote,
     * compared as it was written. Which word it is, is said by where it stands: a node's words are
     * added in a fixed order under a {@link ExecutableIdentity.Kind} that says which node it is.
     */
    record Word(String text) implements Settled {}

    /** A word a node may or may not have, kept as the difference between having none and having
     *  one: an {@code else} the author named and one they left unnamed are not the same body. */
    record MaybeWord(Optional<String> text) implements Settled {}

    /** Which kind of temporal a literal is, beside the text of it. */
    record TemporalKind(Type.Prim kind) implements Settled {}

    /** Where a name this node reads is bound, as a place rather than as what it is spelled. */
    record Bound(BinderAddress at) implements Settled {}

    /** A type the node names: what a unit value is, or what a construction constructs. */
    record Names(TypeSymbol data) implements Settled {}

    /** What a comparison compares by. */
    record Operator(BinOp op) implements Settled {}

    /** What a call applies. */
    record Applies(Core.CallTarget fn) implements Settled {}

    /** A number that is part of what the node does rather than a value it holds: how many names a
     *  block takes, which member of a tuple is read and out of how many. */
    record Count(int of) implements Settled {}

    /** Which case a match arm matches. */
    record Matching(Core.ResolvedPattern pattern) implements Settled {}
}
