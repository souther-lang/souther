package souther.compiler.codegen;

import souther.compiler.ast.Hir;
import souther.compiler.types.ValueName;
import souther.compiler.check.ClauseComparison;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.ConstEval;
import souther.compiler.check.Symbols;
import souther.compiler.core.Kernel;
import souther.compiler.numeric.EndSide;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.Optional;

/**
 * Maps a newtype's invariant onto Raoh's decoder constraints (issue #83), so a violation reported by
 * a derived decoder carries the code and metadata of the rule it broke — {@code too_short} with
 * {@code min}, {@code invalid_format} with {@code pattern} — instead of one {@code
 * invariant_violation} for every invariant in the model. The failure itself is Raoh's: the code, the
 * metadata, the default message and the path all come from the constraint, so a
 * {@code MessageResolver} keyed on the standard codes works unchanged.
 *
 * <p>Only exact equivalences are mapped. A constraint weaker than the invariant would be caught by
 * {@code __construct}, which still runs; a constraint stronger than it would reject values the
 * domain accepts, and would do so at the boundary where it reads as bad input. Anything this cannot
 * prove equivalent is left to the emitter's fallback.
 */
public final class InvariantConstraints {

    /** The name a newtype's single field carries, and so the name its invariant reads it by. */
    private static final String VALUE = "value";

    public sealed interface Constraint {}

    /** A {@code StringDecoder} constraint. */
    public sealed interface OfString extends Constraint {}

    public record MinLength(int n) implements OfString {}

    public record MaxLength(int n) implements OfString {}

    public record FixedLength(int n) implements OfString {}

    public record Pattern(String regex) implements OfString {}

    /** A {@code LongDecoder} constraint — Souther's {@code Int} is carried as a long. */
    public sealed interface OfInt extends Constraint {}

    public record Min(long n) implements OfInt {}

    public record Max(long n) implements OfInt {}

    public record Positive() implements OfInt {}

    public record NonNegative() implements OfInt {}

    /** A {@code DecimalDecoder} constraint. */
    public sealed interface OfDecimal extends Constraint {}

    public record DecimalMin(BigDecimal n) implements OfDecimal {}

    public record DecimalMax(BigDecimal n) implements OfDecimal {}

    public record DecimalPositive() implements OfDecimal {}

    public record DecimalNonNegative() implements OfDecimal {}

    /** A {@code ListDecoder} constraint — a newtype over a {@code List}, whose decoder Raoh answers
     * typed until something untyped is chained onto it. */
    public sealed interface OfList extends Constraint {}

    /** {@code nonempty()} rather than {@code minSize(1)}: Raoh states emptiness on its own, and says so
     * in the message. */
    public record NonEmpty() implements OfList {}

    public record MinSize(int n) implements OfList {}

    public record MaxSize(int n) implements OfList {}

    public record FixedSize(int n) implements OfList {}

    /** {@code unique()}: no element appears twice, compared by value as Souther compares. */
    public record Unique() implements OfList {}

    /** A {@code RecordDecoder} constraint — a newtype over a {@code Map}, which crosses the boundary as
     * an object and is decoded as a record of its values. */
    public sealed interface OfMap extends Constraint {}

    public record MapMinSize(int n) implements OfMap {}

    public record MapMaxSize(int n) implements OfMap {}

    /** The symbols this reads clauses against. Which operations state a constraint is a fact about
     *  the library the clause was resolved against, so it is held here rather than asked at each
     *  call. */
    private final Symbols symbols;

    private InvariantConstraints(Symbols symbols) {
        this.symbols = symbols;
    }

    /** Reading clauses resolved against the library {@code symbols} names. */
    public static InvariantConstraints against(Symbols symbols) {
        return new InvariantConstraints(symbols);
    }

    /**
     * The Raoh constraint equivalent to {@code clause} on a newtype whose value is {@code base}, or
     * empty when this cannot prove one.
     */
    public Optional<Constraint> of(Hir.Expr clause, Type base) {
        if (clause instanceof Hir.Apply call) {
            return ofCall(call, base);
        }
        ClauseComparison read = ClauseComparison.of(clause).orElse(null);
        if (read == null) {
            return Optional.empty();
        }
        // `0 <= value` says what `value >= 0` says: read the value-bearing side as the left one.
        ClauseComparison bound = bearsValue(read.left()) || !bearsValue(read.right())
                ? read : read.turned();
        ComparisonClaim placed = bound.claim();
        Hir.Expr left = bound.left();
        Hir.Expr right = bound.right();
        if (base == Type.STRING) {
            return ofStringLength(placed, left, right);
        }
        if (base == Type.INT) {
            return ofInt(placed, left, right);
        }
        if (base == Type.DECIMAL) {
            return ofDecimal(placed, left, right);
        }
        if (base instanceof Type.ListOf) {
            return ofListSize(placed, left, right);
        }
        if (base instanceof Type.MapOf) {
            return ofMapSize(placed, left, right);
        }
        return Optional.empty();
    }

    /**
     * The bound at {@code end} that admits what a bound placed at {@code n} admits, or null where
     * there is none to name.
     *
     * <p>A length, a size and an {@code Int} are whole numbers, so a bound that refuses the number
     * it names admits exactly what the next one along admits — and Raoh's constraints are inclusive,
     * so that is the one to hand it. At either end of what the constraint can hold there is no next
     * number, and the clause keeps the check it already has.
     */
    private static Long inclusiveAt(EndSide end, boolean holdsAtTheValue, long n,
                                    long least, long most) {
        if (holdsAtTheValue) {
            return n;
        }
        if (end == EndSide.LOWER) {
            return n == most ? null : n + 1;
        }
        return n == least ? null : n - 1;
    }

    /** Which end of the values a comparison bounds: the side it is satisfied on is where its
     *  values run from. */
    private static EndSide endOf(ComparisonClaim.Cut cut) {
        return EndSide.facing(cut.satisfyingSide());
    }

    /**
     * A bound on how many elements a list has: {@code List.length(value) >= 1} is Raoh's
     * {@code nonempty()}, {@code >= 3} its {@code minSize(3)}, and so on. A size is a whole number, so a
     * strict bound is the adjacent inclusive one — read the same way a string's length is.
     *
     * <p>A {@code Set} has no entry of its own here. Souther decodes one as a list and drops the
     * duplicates while mapping it (spec §collections), so a constraint chained after that mapping is no
     * longer on a typed decoder, and one chained before it would count the duplicates.
     */
    private Optional<Constraint> ofListSize(ComparisonClaim placed, Hir.Expr left, Hir.Expr right) {
        Integer n = sizeBound(Kernel.LIST_LENGTH, left, right);
        if (n == null) {
            return Optional.empty();
        }
        return switch (placed) {
            case ComparisonClaim.Singled singled ->
                    singled.holdsAtTheValue() ? Optional.of(new FixedSize(n)) : Optional.empty();
            case ComparisonClaim.Cut cut -> {
                EndSide end = endOf(cut);
                Long at = inclusiveAt(end, cut.holdsAtTheValue(), n, 0, Integer.MAX_VALUE);
                yield at == null ? Optional.empty()
                        : Optional.of(end == EndSide.LOWER
                                ? at == 1 ? new NonEmpty() : new MinSize(at.intValue())
                                : new MaxSize(at.intValue()));
            }
        };
    }

    /** The same for a map, which Raoh decodes as a record of its values and bounds by entry count.
     * There is no emptiness constraint of its own there, so {@code >= 1} is a minimum of one. */
    private Optional<Constraint> ofMapSize(ComparisonClaim placed, Hir.Expr left, Hir.Expr right) {
        Integer n = sizeBound(Kernel.MAP_SIZE, left, right);
        if (n == null || !(placed instanceof ComparisonClaim.Cut cut)) {
            return Optional.empty();
        }
        EndSide end = endOf(cut);
        Long at = inclusiveAt(end, cut.holdsAtTheValue(), n, 0, Integer.MAX_VALUE);
        return at == null ? Optional.empty()
                : Optional.of(end == EndSide.LOWER
                        ? new MapMinSize(at.intValue()) : new MapMaxSize(at.intValue()));
    }

    /** The literal bound {@code size(value)} is compared against, or null when this is not that shape. */
    private Integer sizeBound(Kernel size, Hir.Expr left, Hir.Expr right) {
        if (!(left instanceof Hir.Apply call) || !applies(call, size)
                || call.args().size() != 1 || !isValue(call.args().get(0))) {
            return null;
        }
        Long bound = intLiteral(right);
        if (bound == null || bound < 0 || bound > Integer.MAX_VALUE) {
            return null;
        }
        return bound.intValue();
    }

    private Optional<Constraint> ofCall(Hir.Apply call, Type base) {
        // `String.matches(p, value)` is whole-string anchored (Strings.matches), and so is Raoh's
        // pattern (Matcher.matches), so the two accept the same strings. The regex is asked for the
        // same way the check asks — one reading of which expressions are compile-time strings and of
        // what one composes to, so a pattern the check accepted cannot arrive here unrecognised and
        // lose its constraint. It has been compiled once at check time, so it is known well-formed.
        if (base == Type.STRING && applies(call, Kernel.STRING_MATCHES) && call.args().size() == 2
                && isValue(call.args().get(1))) {
            return ConstEval.against(symbols).evalString(call.args().get(0)).map(Pattern::new);
        }
        // `List.allDistinctBy(x -> x, value)` says of the elements what Raoh's `unique()` says of them:
        // no two are equal, by the same value equality (spec §collections, ADR-0009). A projection that
        // is not the identity says it of something else — the elements' products, their ids — and Raoh
        // has no constraint for that, so the clause keeps its own check.
        if (base instanceof Type.ListOf && statesDistinctness(call)
                && call.args().size() == 2 && isValue(call.args().get(1))
                && isIdentity(call.args().get(0))) {
            return Optional.of(new Unique());
        }
        return Optional.empty();
    }

    private Optional<Constraint> ofStringLength(ComparisonClaim placed, Hir.Expr left,
                                                Hir.Expr right) {
        if (!(left instanceof Hir.Apply call) || !applies(call, Kernel.STRING_LENGTH)
                || call.args().size() != 1 || !isValue(call.args().get(0))) {
            return Optional.empty();
        }
        Long bound = intLiteral(right);
        if (bound == null || bound < 0 || bound > Integer.MAX_VALUE) {
            return Optional.empty();
        }
        int n = bound.intValue();
        return switch (placed) {
            case ComparisonClaim.Singled singled ->
                    singled.holdsAtTheValue() ? Optional.of(new FixedLength(n)) : Optional.empty();
            case ComparisonClaim.Cut cut -> {
                EndSide end = endOf(cut);
                Long at = inclusiveAt(end, cut.holdsAtTheValue(), n, 0, Integer.MAX_VALUE);
                yield at == null ? Optional.empty()
                        : Optional.of(end == EndSide.LOWER
                                ? new MinLength(at.intValue()) : new MaxLength(at.intValue()));
            }
        };
    }

    private static Optional<Constraint> ofInt(ComparisonClaim placed, Hir.Expr left,
                                              Hir.Expr right) {
        if (!isValue(left)) {
            return Optional.empty();
        }
        Long bound = intLiteral(right);
        if (bound == null || !(placed instanceof ComparisonClaim.Cut cut)) {
            return Optional.empty();
        }
        long n = bound;
        EndSide end = endOf(cut);
        // Raoh names both of the bounds at nought, and the name is what a reader is shown — so a
        // bound there is that one rather than the number it would be moved to.
        if (end == EndSide.LOWER && n == 0) {
            return Optional.of(cut.holdsAtTheValue() ? new NonNegative() : new Positive());
        }
        Long at = inclusiveAt(end, cut.holdsAtTheValue(), n, Long.MIN_VALUE, Long.MAX_VALUE);
        return at == null ? Optional.empty()
                : Optional.of(end == EndSide.LOWER ? new Min(at) : new Max(at));
    }

    private static Optional<Constraint> ofDecimal(ComparisonClaim placed, Hir.Expr left,
                                                  Hir.Expr right) {
        if (!isValue(left)) {
            return Optional.empty();
        }
        BigDecimal bound = decimalLiteral(right);
        if (bound == null || !(placed instanceof ComparisonClaim.Cut cut)) {
            return Optional.empty();
        }
        boolean zero = bound.signum() == 0;
        // A Decimal has no next value, so a bound refusing the number it names is no inclusive
        // bound at all — except at nought, which Raoh states directly as positive().
        if (!cut.holdsAtTheValue()) {
            return endOf(cut) == EndSide.LOWER && zero
                    ? Optional.of(new DecimalPositive()) : Optional.empty();
        }
        return Optional.of(endOf(cut) == EndSide.LOWER
                ? zero ? new DecimalNonNegative() : new DecimalMin(bound)
                : new DecimalMax(bound));
    }

    /** Whether the expression reads the newtype's value — directly, or through {@code String.length}. */
    private static boolean bearsValue(Hir.Expr e) {
        if (isValue(e)) {
            return true;
        }
        return e instanceof Hir.Apply call && call.args().size() == 1 && isValue(call.args().get(0));
    }

    private static boolean isValue(Hir.Expr e) {
        return e instanceof Hir.Var v && v.name().equals(VALUE);
    }

    /**
     * Whether {@code call} applies {@code kernel} — asked of what the name reaches, which is what a
     * library operation is filed under whether or not an import let it be written bare, and then of
     * which kernel the library declares that operation to be.
     *
     * <p>The kernel and not the alias. What makes a length comparison a size constraint is that the
     * call computes a length; the alias it is published under is the library's, and a clause
     * recognised by one would go on being recognised for exactly as long as the two agreed.
     *
     * <p>A call applying a name nothing declares, or one that is no kernel, applies no operation
     * this recognises. There is no constraint to map it to, and the clause keeps the check it
     * already has.
     */
    private boolean applies(Hir.Apply call, Kernel kernel) {
        return applied(call) instanceof ValueName.Stdlib.Operation operation
                && symbols.kernelOf(operation) == kernel;
    }

    /** Whether {@code call} states that the elements are distinct — the library's own predicate for
     *  it, which has a Souther body rather than a kernel and so is a value the library hands over
     *  ({@link Symbols#theDistinctnessPredicate}). */
    private boolean statesDistinctness(Hir.Apply call) {
        return symbols.theDistinctnessPredicate().equals(applied(call));
    }

    /** What {@code call} applies, or null where it applies a name nothing declares. */
    private static ValueName applied(Hir.Apply call) {
        return call.answered() == null ? null : call.answered().denotes();
    }

    /** Whether a projection hands back what it was given — {@code x -> x}, however the parameter is
     * spelled. A block with one parameter is how a lambda arrives here (spec §blocks). The body reads
     * the parameter when it reads that binding; a name spelled like it, bound elsewhere, is another
     * value. */
    private static boolean isIdentity(Hir.Expr e) {
        return e instanceof Hir.Block b && b.params().size() == 1
                && b.body() instanceof Hir.Var.Denoting v
                && v.denotes() instanceof ValueName.Local local
                && local.id().equals(b.params().get(0).id());
    }

    /** An Int literal, negation included ({@code -1}), or null when the operand is not one. */
    private static Long intLiteral(Hir.Expr e) {
        if (e instanceof Hir.IntLit lit) {
            return lit.value();
        }
        if (e instanceof Hir.Neg neg && neg.operand() instanceof Hir.IntLit lit
                && lit.value() != Long.MIN_VALUE) {
            return -lit.value();
        }
        return null;
    }

    /** A Decimal literal; an Int literal counts, since a bare literal takes the other side's type. */
    private static BigDecimal decimalLiteral(Hir.Expr e) {
        if (e instanceof Hir.DecimalLit lit) {
            return lit.value();
        }
        if (e instanceof Hir.Neg neg && neg.operand() instanceof Hir.DecimalLit lit) {
            return lit.value().negate();
        }
        Long asInt = intLiteral(e);
        return asInt == null ? null : BigDecimal.valueOf(asInt);
    }
}
